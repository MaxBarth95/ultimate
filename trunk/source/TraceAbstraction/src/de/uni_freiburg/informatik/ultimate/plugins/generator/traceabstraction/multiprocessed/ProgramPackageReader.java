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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.LocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsFuns;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.Constant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.DetachedLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.Edge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.EdgeKind;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.FreshVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.FreshVariables;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.GlobalVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.Location;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.Procedure;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.SpecialLocations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.TransitionFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.TypedName;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.SmtText.Declaration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.SmtText.SExpr;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SerialProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Reads a {@link ProgramPackage} into a {@link BasicIcfg} with generic {@code IcfgInternalTransition},
 * {@code IcfgCallTransition} and {@code IcfgReturnTransition} edges that keep the package's edge ids, so that letter
 * names {@code e<id>} stay valid. Edges that overapproximate get their {@link Overapprox} annotation back (with
 * dummy locations), so that a counterexample through them still does not prove a violation.
 *
 * The caller provides the script, built from the session's settings as in the C pipeline and wrapped in a
 * {@code HistoryRecordingScript}. The reader checks that its logic is the package's, replays the declarations in
 * package order and keeps every term variable name, so that predicates parse to the same program variables.
 */
public final class ProgramPackageReader {

	/** The quantified variable that carries a parsed term of any sort, see {@link #parseTerm}. */
	private static final String RESULT_VARIABLE = ".package.result";

	private final ManagedScript mMgdScript;
	private final Script mScript;
	private final Map<String, IProgramVar> mVariables = new HashMap<>();
	private final Map<String, IProgramConst> mConstants = new HashMap<>();

	private ProgramPackageReader(final ManagedScript mgdScript) {
		mMgdScript = mgdScript;
		mScript = mgdScript.getScript();
	}

	/**
	 * @return the ICFG of a PACKAGE_JSON_V1 text
	 * @throws IllegalArgumentException
	 *             if the text is no valid package, or does not fit the script
	 */
	public static BasicIcfg<IcfgLocation> readJson(final ManagedScript mgdScript, final String json) {
		return read(mgdScript, JsonCodec.decode(json, ProgramPackage.class, ProgramPackage.FORMAT));
	}

	/**
	 * @return the ICFG of a package
	 * @throws IllegalArgumentException
	 *             if the package is inconsistent or does not fit the script
	 */
	public static BasicIcfg<IcfgLocation> read(final ManagedScript mgdScript, final ProgramPackage pkg) {
		return new ProgramPackageReader(mgdScript).build(pkg);
	}

	private BasicIcfg<IcfgLocation> build(final ProgramPackage pkg) {
		final String logic = mScript.getTheory().getLogic().name();
		if (!logic.equals(pkg.logic())) {
			throw new IllegalArgumentException(
					"The package was built with logic " + pkg.logic() + ", but the script has logic " + logic);
		}
		for (final String declaration : pkg.declarations()) {
			replay(declaration);
		}

		final DefaultIcfgSymbolTable symbols = new DefaultIcfgSymbolTable();
		for (final GlobalVariable global : pkg.globals()) {
			final Variable old = global.oldVariable();
			final Variable var = global.variable();
			final ProgramOldVar oldVar =
					new ProgramOldVar(old.identifier(), termVariable(old), constant(old.defaultConstant()),
							constant(old.primedConstant()));
			final ProgramNonOldVar nonOldVar = new ProgramNonOldVar(var.identifier(), termVariable(var),
					constant(var.defaultConstant()), constant(var.primedConstant()), oldVar);
			oldVar.setNonOldVar(nonOldVar);
			register(oldVar);
			register(nonOldVar);
			symbols.add(nonOldVar);
		}
		for (final Constant constant : pkg.constants()) {
			final ProgramConst programConst =
					new ProgramConst(constant.identifier(), constant(constant.constant()), constant.theory());
			if (mConstants.put(constant.constant(), programConst) != null) {
				throw new IllegalArgumentException("Two program constants " + constant.constant());
			}
			symbols.add(programConst);
		}
		final Map<String, List<ILocalProgramVar>> inParams = new HashMap<>();
		final Map<String, List<ILocalProgramVar>> outParams = new HashMap<>();
		final HashRelation<String, IProgramNonOldVar> modifiable = new HashRelation<>();
		final Set<String> procedures = new LinkedHashSet<>();
		for (final Procedure proc : pkg.procedures()) {
			procedures.add(proc.name());
			for (final Variable local : proc.locals()) {
				final LocalProgramVar var = new LocalProgramVar(local.identifier(), proc.name(), termVariable(local),
						constant(local.defaultConstant()), constant(local.primedConstant()));
				register(var);
				symbols.add(var);
			}
			inParams.put(proc.name(), locals(proc.inParams()));
			outParams.put(proc.name(), locals(proc.outParams()));
			for (final String global : proc.modifiableGlobals()) {
				final IProgramVar var = variable(global);
				if (!(var instanceof IProgramNonOldVar)) {
					throw new IllegalArgumentException("Modifiable global " + global + " is not a global variable");
				}
				modifiable.addPair(proc.name(), (IProgramNonOldVar) var);
			}
		}
		final Map<String, FunctionSymbol> declared = mScript.getTheory().getDeclaredFunctions();
		for (final String function : pkg.functions()) {
			final FunctionSymbol symbol = declared.get(function);
			if (symbol == null) {
				throw new IllegalArgumentException("Program function " + function + " is not declared");
			}
			symbols.addFun(new ProgramFunction(symbol));
		}
		symbols.finishConstruction();

		final Term axioms = parseTerm(pkg.axioms(), List.of(), mScript.sort("Bool"));
		final Set<IProgramFunction> axiomFunctions =
				TermVarsFuns.computeTermVarsFuns(axioms, mMgdScript, symbols).getFuns();
		final SmtFunctionsAndAxioms smtFunctionsAndAxioms =
				new SmtFunctionsAndAxioms(axioms, axiomFunctions, mMgdScript);

		restoreFreshVariables(pkg.freshVariables());

		final PackageSerialProvider serials = new PackageSerialProvider();
		final IcfgEdgeFactory edgeFactory = new IcfgEdgeFactory(serials);
		final CfgSmtToolkit toolkit = new CfgSmtToolkit(new ModifiableGlobalsTable(modifiable), mMgdScript, symbols,
				procedures, inParams, outParams, edgeFactory,
				new ConcurrencyInformation(Collections.emptyMap(), Collections.emptyMap(), Collections.emptySet()),
				smtFunctionsAndAxioms);
		final BasicIcfg<IcfgLocation> icfg = new BasicIcfg<>(pkg.identifier(), toolkit, IcfgLocation.class);

		final Map<String, IcfgLocation> locations = new HashMap<>();
		final Set<String> withLocations = new HashSet<>();
		for (final Location location : pkg.locations()) {
			if (withLocations.add(location.procedure())) {
				icfg.addProcedure(location.procedure());
			}
			final IcfgLocation loc = new IcfgLocation(new PackageDebugIdentifier(location.debugId(), location.hash()),
					location.procedure());
			final String name = location.procedure() + "::" + location.debugId();
			if (locations.put(name, loc) != null) {
				throw new IllegalArgumentException("Two locations named " + name);
			}
			icfg.addLocation(loc, false, false, false, false, false, false);
		}
		// special locations that are not program points (no edges, see SpecialLocations.detached)
		final SpecialLocations special = pkg.special();
		final Map<String, IcfgLocation> detached = new HashMap<>();
		for (final DetachedLocation location : special.detached()) {
			if (!withLocations.contains(location.procedure())) {
				throw new IllegalArgumentException("Detached location " + location.debugId()
						+ " of a procedure without program points: " + location.procedure());
			}
			final IcfgLocation loc = new IcfgLocation(new PackageDebugIdentifier(location.debugId(), location.hash()),
					location.procedure());
			final String name = location.procedure() + "::" + location.debugId();
			if (locations.containsKey(name) || detached.put(name, loc) != null) {
				throw new IllegalArgumentException("Two locations named " + name);
			}
		}
		// each kind of special location in its recorded order (the collections keep insertion order)
		for (final String name : special.initial()) {
			mark(icfg, locations, detached, name, true, false, false, false, false, false);
		}
		for (final String name : special.error()) {
			mark(icfg, locations, detached, name, false, true, false, false, false, false);
		}
		for (final String name : special.entry()) {
			mark(icfg, locations, detached, name, false, false, true, false, false, false);
		}
		for (final String name : special.exit()) {
			mark(icfg, locations, detached, name, false, false, false, true, false, false);
		}
		for (final String name : special.loopHeads()) {
			mark(icfg, locations, detached, name, false, false, false, false, true, false);
		}
		for (final String name : special.ofInterest()) {
			mark(icfg, locations, detached, name, false, false, false, false, false, true);
		}

		final Map<Integer, IcfgEdge> createdEdges = new HashMap<>();
		final Map<Integer, IcfgCallTransition> calls = new HashMap<>();
		final Map<Integer, UnmodifiableTransFormula> callAssignments = new HashMap<>();
		int maxId = -1;
		final Set<Integer> ids = new HashSet<>();
		// returns refer to their calls, so calls and internal edges come first
		for (final boolean returns : new boolean[] { false, true }) {
			for (final Edge edge : pkg.edges()) {
				if ((edge.kind() == EdgeKind.RETURN) != returns) {
					continue;
				}
				if (!ids.add(edge.id())) {
					throw new IllegalArgumentException("Two edges with id " + edge.id());
				}
				maxId = Math.max(maxId, edge.id());
				final IcfgLocation source = location(locations, edge.source());
				final IcfgLocation target = location(locations, edge.target());
				final UnmodifiableTransFormula tf = transFormula(edge.transFormula());
				serials.setNext(edge.id());
				final IcfgEdge created;
				switch (edge.kind()) {
				case INTERNAL:
					requireNull(edge.call(), edge);
					created = edgeFactory.createInternalTransition(source, target, null, tf,
							edge.withBranchEncoders() == null ? tf : transFormula(edge.withBranchEncoders()));
					break;
				case CALL:
					requireNull(edge.call(), edge);
					requireNull(edge.withBranchEncoders(), edge);
					final IcfgCallTransition call = edgeFactory.createCallTransition(source, target, null, tf);
					calls.put(edge.id(), call);
					callAssignments.put(edge.id(), tf);
					created = call;
					break;
				case RETURN:
					requireNull(edge.withBranchEncoders(), edge);
					if (edge.call() == null || !calls.containsKey(edge.call())) {
						throw new IllegalArgumentException("Return " + edge.id() + " has no call " + edge.call());
					}
					created = edgeFactory.createReturnTransition(source, target, calls.get(edge.call()), null, tf,
							callAssignments.get(edge.call()));
					break;
				default:
					throw new AssertionError(edge.kind());
				}
				if (edge.overapproximations() != null) {
					final Map<String, ILocation> reasons = new LinkedHashMap<>();
					for (final String reason : edge.overapproximations()) {
						reasons.put(reason, new DefaultLocation());
					}
					new Overapprox(reasons).annotate(created);
				}
				if (LetterNaming.idOf(created) != edge.id()) {
					throw new IllegalStateException("Edge " + edge.id() + " got id " + LetterNaming.idOf(created));
				}
				createdEdges.put(edge.id(), created);
			}
		}
		// connected in each location's recorded order, which iterations over the edges of a location follow
		final Set<Integer> connectedOut = new HashSet<>();
		final Set<Integer> connectedIn = new HashSet<>();
		for (final Location location : pkg.locations()) {
			final IcfgLocation loc = locations.get(location.procedure() + "::" + location.debugId());
			for (final Integer id : location.outgoing()) {
				final IcfgEdge edge = createdEdges.get(id);
				if (edge == null || edge.getSource() != loc || !connectedOut.add(id)) {
					throw new IllegalArgumentException("Outgoing edge " + id + " does not fit location " + loc);
				}
				loc.addOutgoing(edge);
			}
			for (final Integer id : location.incoming()) {
				final IcfgEdge edge = createdEdges.get(id);
				if (edge == null || edge.getTarget() != loc || !connectedIn.add(id)) {
					throw new IllegalArgumentException("Incoming edge " + id + " does not fit location " + loc);
				}
				loc.addIncoming(edge);
			}
		}
		if (connectedOut.size() != createdEdges.size() || connectedIn.size() != createdEdges.size()) {
			throw new IllegalArgumentException("Not every edge is an outgoing and an incoming edge of a location");
		}
		// edges created later must not reuse a package id
		serials.setNext(maxId + 1);
		return icfg;
	}

	/**
	 * Gives the script's variable manager the writer's state, before any fresh variable is constructed here.
	 */
	private void restoreFreshVariables(final FreshVariables fresh) {
		final Map<TermVariable, String> basenames = new HashMap<>();
		for (final FreshVariable var : fresh.variables()) {
			basenames.put(mScript.variable(var.name(), SmtText.sort(mScript, var.sort())), var.basename());
		}
		mMgdScript.restoreFreshVariableState(basenames, fresh.counters());
	}

	private void replay(final String text) {
		final Declaration declaration = SmtText.declaration(text);
		if (!"define-fun".equals(declaration.command())) {
			SmtText.declare(mScript, declaration);
			return;
		}
		final List<SExpr[]> params = SmtText.parameters(declaration);
		final TermVariable[] vars = new TermVariable[params.size()];
		for (int i = 0; i < vars.length; i++) {
			vars[i] = mScript.variable(params.get(i)[0].atomOrThrow(), SmtText.sort(mScript, params.get(i)[1]));
		}
		final Sort result = SmtText.sort(mScript, declaration.parts().get(3));
		final Term body = parseTerm(declaration.parts().get(4).text(), List.of(vars), result);
		mScript.defineFun(declaration.name(), vars, result, body);
	}

	/**
	 * Parses a term over the given variables. The term is wrapped as {@code (forall ((r S) vars) (= r term))}, so that
	 * it may be of any sort and the variables are bound; the parser's lets are expanded afterwards.
	 */
	private Term parseTerm(final String text, final Collection<TermVariable> vars, final Sort sort) {
		final StringBuilder sb = new StringBuilder("(forall ((");
		sb.append(PrintTerm.quoteIdentifier(RESULT_VARIABLE)).append(' ').append(sort).append(')');
		for (final TermVariable var : vars) {
			sb.append(" (").append(PrintTerm.quoteIdentifier(var.getName())).append(' ').append(var.getSort())
					.append(')');
		}
		sb.append(") (= ").append(PrintTerm.quoteIdentifier(RESULT_VARIABLE)).append(' ').append(text).append("))");
		final Term parsed = TermParseUtils.parseTerm(mScript, sb.toString());
		final Term equality = ((QuantifiedFormula) parsed).getSubformula();
		final Term term = ((ApplicationTerm) equality).getParameters()[1];
		final Term unlet = new FormulaUnLet().unlet(term);
		if (!unlet.getSort().equals(sort)) {
			throw new IllegalArgumentException("Expected a term of sort " + sort + ", got " + unlet.getSort());
		}
		return unlet;
	}

	/**
	 * A transition formula whose maps and sets iterate in the package's order, i.e. the writer's: they are linked
	 * collections filled in that order and kept as they are ({@link TransFormulaBuilder#constructKeepingCollections}).
	 * Hash maps that other code builds from them later therefore get the same insertion order as in the writer.
	 */
	private UnmodifiableTransFormula transFormula(final TransitionFormula tf) {
		final Map<IProgramVar, TermVariable> inVars = varMap(tf.inVars());
		final Map<IProgramVar, TermVariable> outVars = varMap(tf.outVars());
		final Set<TermVariable> auxVars = new LinkedHashSet<>(typed(tf.auxVars()));
		final Set<TermVariable> branchEncoders = new LinkedHashSet<>(typed(tf.branchEncoders()));
		final Set<IProgramConst> nonTheoryConsts = new LinkedHashSet<>();
		for (final String name : tf.nonTheoryConsts()) {
			final IProgramConst constant = mConstants.get(name);
			if (constant == null) {
				throw new IllegalArgumentException("Unknown program constant " + name);
			}
			nonTheoryConsts.add(constant);
		}
		final Set<TermVariable> free = new LinkedHashSet<>();
		free.addAll(inVars.values());
		free.addAll(outVars.values());
		free.addAll(auxVars);
		free.addAll(branchEncoders);
		return TransFormulaBuilder.constructKeepingCollections(parseTerm(tf.formula(), free, mScript.sort("Bool")),
				inVars, outVars, nonTheoryConsts, auxVars, branchEncoders, tf.infeasibility(), mMgdScript);
	}

	private Map<IProgramVar, TermVariable> varMap(final Map<String, String> names) {
		// in the package's (the writer's iteration) order
		final Map<IProgramVar, TermVariable> result = new LinkedHashMap<>();
		for (final Map.Entry<String, String> entry : names.entrySet()) {
			final IProgramVar var = variable(entry.getKey());
			result.put(var, mScript.variable(entry.getValue(), var.getSort()));
		}
		return result;
	}

	private List<TermVariable> typed(final List<TypedName> names) {
		final List<TermVariable> result = new ArrayList<>(names.size());
		for (final TypedName name : names) {
			result.add(mScript.variable(name.name(), SmtText.sort(mScript, name.sort())));
		}
		return result;
	}

	private TermVariable termVariable(final Variable var) {
		return mScript.variable(var.termVariable(), SmtText.sort(mScript, var.sort()));
	}

	private ApplicationTerm constant(final String name) {
		final Term term = mScript.term(name);
		if (!(term instanceof ApplicationTerm) || ((ApplicationTerm) term).getParameters().length != 0) {
			throw new IllegalArgumentException("Not a constant: " + name);
		}
		return (ApplicationTerm) term;
	}

	private void register(final IProgramVar var) {
		final String name = var.getTermVariable().getName();
		if (mVariables.put(name, var) != null) {
			throw new IllegalArgumentException("Two program variables with term variable " + name);
		}
	}

	private IProgramVar variable(final String termVariable) {
		final IProgramVar var = mVariables.get(termVariable);
		if (var == null) {
			throw new IllegalArgumentException("Unknown program variable " + termVariable);
		}
		return var;
	}

	private List<ILocalProgramVar> locals(final List<String> termVariables) {
		return termVariables.stream().map(this::variable).map(v -> {
			if (!(v instanceof ILocalProgramVar)) {
				throw new IllegalArgumentException("Parameter " + v + " is not a local variable");
			}
			return (ILocalProgramVar) v;
		}).collect(Collectors.toList());
	}

	private static void mark(final BasicIcfg<IcfgLocation> icfg, final Map<String, IcfgLocation> locations,
			final Map<String, IcfgLocation> detached, final String name, final boolean isInitial,
			final boolean isError, final boolean isProcEntry, final boolean isProcExit, final boolean isLoopLocation,
			final boolean isLocationOfInterest) {
		final IcfgLocation detachedLoc = detached.get(name);
		if (detachedLoc != null) {
			icfg.markDetachedLocation(detachedLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation,
					isLocationOfInterest);
		} else {
			icfg.markLocation(location(locations, name), isInitial, isError, isProcEntry, isProcExit, isLoopLocation,
					isLocationOfInterest);
		}
	}

	private static IcfgLocation location(final Map<String, IcfgLocation> locations, final String name) {
		final IcfgLocation loc = locations.get(name);
		if (loc == null) {
			throw new IllegalArgumentException("Unknown location " + name);
		}
		return loc;
	}

	private static void requireNull(final Object value, final Edge edge) {
		if (value != null) {
			throw new IllegalArgumentException("Malformed " + edge.kind() + " edge " + edge.id());
		}
	}

	/**
	 * The debug identifier of a read location: its text, and the hash code of the writer's debug identifier, from which
	 * {@link IcfgLocation} computes its own hash code. So read locations hash, and iterate in hash-based collections,
	 * like the writer's.
	 */
	public static final class PackageDebugIdentifier extends DebugIdentifier {
		private final String mText;
		private final int mHash;

		public PackageDebugIdentifier(final String text, final int hash) {
			mText = text;
			mHash = hash;
		}

		@Override
		public String toString() {
			return mText;
		}

		@Override
		public int hashCode() {
			return mHash;
		}

		@Override
		public boolean equals(final Object obj) {
			return obj instanceof PackageDebugIdentifier && ((PackageDebugIdentifier) obj).mText.equals(mText)
					&& ((PackageDebugIdentifier) obj).mHash == mHash;
		}
	}

	/**
	 * Hands out the package id of the edge being created, then fresh ids above all package ids.
	 */
	private static final class PackageSerialProvider extends SerialProvider {
		private int mNext;

		void setNext(final int next) {
			mNext = next;
		}

		@Override
		public int getFreshSerial() {
			return mNext++;
		}
	}
}
