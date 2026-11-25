/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardWatchEventKinds;
import java.nio.file.WatchKey;
import java.nio.file.WatchService;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.Duration;
import java.time.Instant;
import java.util.EnumSet;
import java.util.HexFormat;
import java.util.Optional;
import java.util.OptionalLong;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * The session directory of the {@code EXCHANGE_V1} protocol. See {@code TraceAbstraction/.doc/multiprocessed/} for
 * the protocol.
 *
 * <ul>
 * <li>{@code in/}: written by the worker service, read here in sequence order. Files are never changed or deleted
 * here.</li>
 * <li>{@code out/}: written here, as {@code *.tmp} and then renamed atomically.</li>
 * <li>{@code blobs/<sha256>}: bodies larger than {@link #BLOB_THRESHOLD}, referenced by a {@code .ref.json}
 * file.</li>
 * <li>{@code log/}: belongs to the worker service; nothing is written there.</li>
 * </ul>
 *
 * A message file is named {@code <seq>-<TYPE>[-j<job>][-g<generation>].<ext>}. A file in {@code in/} with an unknown
 * name, type or extension, a type the kind does not accept, or a sequence number out of order throws.
 */
public final class FileExchange implements IExchange {

	/** Bodies larger than this many bytes go into {@code blobs/}. */
	public static final int BLOB_THRESHOLD = 1 << 20;

	public static final String IN = "in";
	public static final String OUT = "out";
	public static final String BLOBS = "blobs";
	public static final String SHUTDOWN = "shutdown";
	public static final String READY = "ready.json";
	public static final String STATISTICS = "statistics.json";

	private static final String TMP = ".tmp";
	private static final String REF_EXTENSION = "ref.json";
	private static final Pattern MESSAGE_NAME =
			Pattern.compile("(\\d+)-([A-Z_]+)(?:-j(\\d+))?(?:-g(\\d+))?\\.(ref\\.json|[a-z]+)");
	private static final int SEQ_DIGITS = 10;

	/**
	 * The content of a {@code .ref.json} file.
	 *
	 * @param sha256
	 *            the SHA-256 of the body, which is also its file name in {@code blobs/}
	 * @param size
	 *            the size of the body in bytes
	 */
	public record BlobRef(String sha256, long size) {
	}

	private record PendingFile(long seq, String name, Matcher match) {
	}

	private final Path mIn;
	private final Path mOut;
	private final Path mBlobs;
	private final Set<MessageType> mAccepts;
	private final Set<MessageType> mEmits;
	private final WatchService mWatchService;
	// read by the thread that watches for a cancellation, see waitForStop
	private final Set<String> mConsumed = ConcurrentHashMap.newKeySet();
	private WatchService mStopWatchService;
	private long mLastInSeq = -1;
	private long mNextOutSeq = 1;
	private boolean mReady;

	/**
	 * Opens a session directory. Creates {@code in/}, {@code out/} and {@code blobs/} if they do not exist.
	 *
	 * @param root
	 *            the session directory
	 * @param accepts
	 *            the message types the session kind reads
	 * @param emits
	 *            the message types the session kind writes
	 */
	public FileExchange(final Path root, final Set<MessageType> accepts, final Set<MessageType> emits) {
		mIn = root.resolve(IN);
		mOut = root.resolve(OUT);
		mBlobs = root.resolve(BLOBS);
		mAccepts = EnumSet.copyOf(accepts);
		mEmits = EnumSet.copyOf(emits);
		try {
			Files.createDirectories(mIn);
			Files.createDirectories(mOut);
			Files.createDirectories(mBlobs);
			mWatchService = FileSystems.getDefault().newWatchService();
			mIn.register(mWatchService, StandardWatchEventKinds.ENTRY_CREATE);
		} catch (final IOException e) {
			throw new UncheckedIOException("Cannot open session directory " + root, e);
		}
	}

	@Override
	public Optional<ExchangeMessage> take(final Instant deadline) {
		while (true) {
			if (isShutdownRequested()) {
				return Optional.empty();
			}
			final Optional<ExchangeMessage> next = poll();
			if (next.isPresent()) {
				return next;
			}
			final long remaining = Duration.between(Instant.now(), deadline).toMillis();
			if (remaining <= 0) {
				throw new DeadlineExpiredException("No message in " + mIn + " before " + deadline);
			}
			final WatchKey key;
			try {
				key = mWatchService.poll(remaining, TimeUnit.MILLISECONDS);
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
				throw new IllegalStateException("Interrupted while waiting for a message", e);
			}
			if (key != null) {
				key.pollEvents();
				if (!key.reset()) {
					throw new IllegalStateException("Cannot watch " + mIn + " any longer");
				}
			}
		}
	}

	@Override
	public Optional<ExchangeMessage> poll() {
		if (isShutdownRequested()) {
			return Optional.empty();
		}
		final PendingFile next = nextPendingFile();
		if (next == null) {
			return Optional.empty();
		}
		final ExchangeMessage message = read(next);
		mConsumed.add(next.name());
		mLastInSeq = next.seq();
		return Optional.of(message);
	}

	@Override
	public boolean isShutdownRequested() {
		return Files.exists(mIn.resolve(SHUTDOWN));
	}

	@Override
	public boolean waitForStop(final long job, final Duration timeout) throws InterruptedException {
		final Instant deadline = Instant.now().plus(timeout);
		final WatchService watchService = stopWatchService();
		while (true) {
			if (isShutdownRequested() || isCancelPending(job)) {
				return true;
			}
			final long remaining = Duration.between(Instant.now(), deadline).toMillis();
			if (remaining <= 0) {
				return false;
			}
			final WatchKey key = watchService.poll(remaining, TimeUnit.MILLISECONDS);
			if (key != null) {
				key.pollEvents();
				if (!key.reset()) {
					throw new IllegalStateException("Cannot watch " + mIn + " any longer");
				}
			}
		}
	}

	private synchronized WatchService stopWatchService() {
		if (mStopWatchService == null) {
			try {
				mStopWatchService = FileSystems.getDefault().newWatchService();
				mIn.register(mStopWatchService, StandardWatchEventKinds.ENTRY_CREATE);
			} catch (final IOException e) {
				throw new UncheckedIOException("Cannot watch " + mIn, e);
			}
		}
		return mStopWatchService;
	}

	private boolean isCancelPending(final long job) {
		final String jobId = Long.toString(job);
		try (Stream<Path> files = Files.list(mIn)) {
			return files.map(f -> f.getFileName().toString())
					.filter(name -> !name.endsWith(TMP) && !mConsumed.contains(name)).map(MESSAGE_NAME::matcher)
					.anyMatch(m -> m.matches() && MessageType.CANCEL.name().equals(m.group(2))
							&& jobId.equals(m.group(3)));
		} catch (final IOException e) {
			throw new UncheckedIOException("Cannot list " + mIn, e);
		}
	}

	/**
	 * Lists {@code in/} and returns the unread message with the lowest sequence number.
	 */
	private PendingFile nextPendingFile() {
		final TreeMap<Long, PendingFile> pending = new TreeMap<>();
		try (Stream<Path> files = Files.list(mIn)) {
			for (final Path file : (Iterable<Path>) files::iterator) {
				final String name = file.getFileName().toString();
				if (name.endsWith(TMP) || name.equals(SHUTDOWN) || mConsumed.contains(name)) {
					continue;
				}
				final Matcher match = MESSAGE_NAME.matcher(name);
				if (!match.matches()) {
					throw new IllegalArgumentException("Unknown file in " + mIn + ": " + name);
				}
				final long seq = Long.parseLong(match.group(1));
				if (seq <= mLastInSeq) {
					throw new IllegalArgumentException("Message " + name + " arrived after message " + mLastInSeq
							+ " was read; messages must arrive in sequence order");
				}
				final PendingFile previous = pending.put(seq, new PendingFile(seq, name, match));
				if (previous != null) {
					throw new IllegalArgumentException(
							"Two messages with sequence number " + seq + ": " + previous.name() + " and " + name);
				}
			}
		} catch (final IOException e) {
			throw new UncheckedIOException("Cannot list " + mIn, e);
		}
		return pending.isEmpty() ? null : pending.firstEntry().getValue();
	}

	private ExchangeMessage read(final PendingFile file) {
		final Matcher match = file.match();
		final MessageType type = MessageType.fromName(match.group(2));
		if (!mAccepts.contains(type)) {
			throw new IllegalArgumentException("This session kind does not accept " + type + ": " + file.name());
		}
		final String extension = match.group(5);
		final String body;
		if (REF_EXTENSION.equals(extension)) {
			body = readBlob(JsonCodec.decodePlain(readString(mIn.resolve(file.name())), BlobRef.class));
		} else {
			// throws for an unknown extension; formats that share an extension are told apart by the type
			ContentFormat.fromExtension(extension);
			if (!type.getFormat().getExtension().equals(extension)) {
				throw new IllegalArgumentException(
						type + " needs format " + type.getFormat() + ", not ." + extension + ": " + file.name());
			}
			body = readString(mIn.resolve(file.name()));
		}
		return new ExchangeMessage(file.seq(), type, optionalLong(match.group(3)), optionalLong(match.group(4)),
				body);
	}

	private String readBlob(final BlobRef ref) {
		if (ref.sha256() == null || !ref.sha256().matches("[0-9a-f]{64}")) {
			throw new IllegalArgumentException("Malformed blob reference " + ref);
		}
		final byte[] bytes;
		try {
			bytes = Files.readAllBytes(mBlobs.resolve(ref.sha256()));
		} catch (final NoSuchFileException e) {
			throw new IllegalArgumentException("Missing blob " + ref.sha256(), e);
		} catch (final IOException e) {
			throw new UncheckedIOException("Cannot read blob " + ref.sha256(), e);
		}
		if (bytes.length != ref.size() || !sha256(bytes).equals(ref.sha256())) {
			throw new IllegalArgumentException("Blob " + ref.sha256() + " does not match its reference " + ref);
		}
		return new String(bytes, StandardCharsets.UTF_8);
	}

	@Override
	public void send(final MessageType type, final OptionalLong job, final OptionalLong generation,
			final String body) {
		if (!mReady && type != MessageType.EXCEPTION) {
			// a crash may come before the session is ready; anything else may not
			throw new IllegalStateException("Send " + type + " before ready.json was written");
		}
		if (!mEmits.contains(type)) {
			throw new IllegalArgumentException("This session kind does not emit " + type);
		}
		if (type == MessageType.WITNESS) {
			throw new IllegalArgumentException("The witness is out/witness.yml, not a numbered message");
		}
		final StringBuilder name = new StringBuilder();
		name.append(String.format("%0" + SEQ_DIGITS + "d", mNextOutSeq)).append('-').append(type.name());
		job.ifPresent(j -> name.append("-j").append(j));
		generation.ifPresent(g -> name.append("-g").append(g));
		final byte[] bytes = body.getBytes(StandardCharsets.UTF_8);
		if (bytes.length > BLOB_THRESHOLD) {
			final String sha = sha256(bytes);
			writeAtomically(mBlobs.resolve(sha), bytes);
			name.append('.').append(REF_EXTENSION);
			writeAtomically(mOut.resolve(name.toString()),
					JsonCodec.encodePlain(new BlobRef(sha, bytes.length)).getBytes(StandardCharsets.UTF_8));
		} else {
			name.append('.').append(type.getFormat().getExtension());
			writeAtomically(mOut.resolve(name.toString()), bytes);
		}
		mNextOutSeq++;
	}

	@Override
	public void announceReady(final ReadyFile ready) {
		if (mReady) {
			throw new IllegalStateException("ready.json was already written");
		}
		writeAtomically(mOut.resolve(READY), JsonCodec.encodePlain(ready).getBytes(StandardCharsets.UTF_8));
		mReady = true;
	}

	@Override
	public void writeStatistics(final String json) {
		writeAtomically(mOut.resolve(STATISTICS), json.getBytes(StandardCharsets.UTF_8));
	}

	@Override
	public synchronized void close() {
		try {
			mWatchService.close();
			if (mStopWatchService != null) {
				mStopWatchService.close();
			}
		} catch (final IOException e) {
			throw new UncheckedIOException(e);
		}
	}

	/**
	 * Writes a file as {@code <file>.tmp} and renames it atomically.
	 */
	static void writeAtomically(final Path file, final byte[] bytes) {
		final Path tmp = file.resolveSibling(file.getFileName() + TMP);
		try {
			Files.write(tmp, bytes);
			Files.move(tmp, file, StandardCopyOption.ATOMIC_MOVE, StandardCopyOption.REPLACE_EXISTING);
		} catch (final IOException e) {
			throw new UncheckedIOException("Cannot write " + file, e);
		}
	}

	private static String readString(final Path file) {
		try {
			return Files.readString(file, StandardCharsets.UTF_8);
		} catch (final IOException e) {
			throw new UncheckedIOException("Cannot read " + file, e);
		}
	}

	private static OptionalLong optionalLong(final String digits) {
		return digits == null ? OptionalLong.empty() : OptionalLong.of(Long.parseLong(digits));
	}

	/**
	 * @return the lowercase hex SHA-256 of some bytes
	 */
	public static String sha256(final byte[] bytes) {
		try {
			return HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256").digest(bytes));
		} catch (final NoSuchAlgorithmException e) {
			throw new IllegalStateException(e);
		}
	}
}
