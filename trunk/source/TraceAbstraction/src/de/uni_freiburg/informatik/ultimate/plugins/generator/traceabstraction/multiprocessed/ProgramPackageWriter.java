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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.DeclarableFunctionSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.DeclarableSortSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.ISmtDeclarable;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
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

/**
 * Writes an ICFG as a {@link ProgramPackage} (PACKAGE_JSON_V1).
 *
 * The SMT declarations are those of the ICFG's script ({@link HistoryRecordingScript}), in declaration order, but only
 * the ones the ICFG uses: the sorts and functions that occur in the edge formulas, the axioms and the constants of the
 * program variables, closed under the bodies of defined functions and the sorts of used functions. So nothing the
 * solver declared for other purposes before the package was written leaks into it.
 *
 * Summary edges of calls to procedures with an implementation are left out: an interprocedural TraceAbstraction never
 * uses them, and the reader could only turn them into plain internal edges, i.e. shortcuts that havoc the callee's
 * effects. Multi-process sessions therefore require the interprocedural analysis ({@link MultiProcessSupport}).
 *
 * Every unsupported construct throws (concurrent edges, unknown edge, variable or constant types).
 */
public final class ProgramPackageWriter {

	private final IIcfg<? extends IcfgLocation> mIcfg;
	private final CfgSmtToolkit mToolkit;
	private final LocationNaming mLocations;
	/** Names of the non-theory functions and sorts the package uses. */
	private final Set<String> mUsedFunctions = new HashSet<>();
	private final Map<String, FunctionSymbol> mFunctionSymbols = new HashMap<>();
	private final Set<String> mUsedSorts = new HashSet<>();
	private final Set<Term> mVisited = new HashSet<>();
	/** Every term variable of the package, by name. */
	private final Map<String, TermVariable> mTermVariables = new HashMap<>();

	private ProgramPackageWriter(final IIcfg<? extends IcfgLocation> icfg) {
		mIcfg = icfg;
		mToolkit = icfg.getCfgSmtToolkit();
		mLocations = new LocationNaming(icfg);
	}

	/**
	 * @return the package of the ICFG
	 */
	public static ProgramPackage write(final IIcfg<? extends IcfgLocation> icfg) {
		return new ProgramPackageWriter(icfg).build();
	}

	/**
	 * @return the PACKAGE_JSON_V1 text of the ICFG
	 */
	public static String writeJson(final IIcfg<? extends IcfgLocation> icfg) {
		return JsonCodec.encode(write(icfg), ProgramPackage.FORMAT);
	}

	private ProgramPackage build() {
		final IIcfgSymbolTable symbols = mToolkit.getSymbolTable();
		final List<GlobalVariable> globals = new ArrayList<>();
		for (final IProgramNonOldVar global : inOrder(symbols.getGlobals(), IProgramNonOldVar::getIdentifier)) {
			globals.add(new GlobalVariable(variable(global), variable(global.getOldVar())));
		}
		final List<Constant> constants = new ArrayList<>();
		for (final IProgramConst constant : inOrder(symbols.getConstants(), IProgramConst::getIdentifier)) {
			constants.add(constant(constant));
		}
		final List<Procedure> procedures = new ArrayList<>();
		for (final String proc : inOrder(mToolkit.getProcedures(), p -> p)) {
			procedures.add(procedure(proc, symbols));
		}
		final List<Location> locations = new ArrayList<>();
		final List<IcfgEdge> edges = new ArrayList<>();
		for (final String proc : inOrder(mIcfg.getProgramPoints().keySet(), p -> p)) {
			final Map<?, ? extends IcfgLocation> points = mIcfg.getProgramPoints().get(proc);
			for (final IcfgLocation loc : inOrder(points.values(), l -> l.getDebugIdentifier().toString())) {
				final List<Integer> outgoing = new ArrayList<>();
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					// an interprocedural analysis never uses it (Cfg2Automaton); as a plain internal edge it
					// would be a shortcut that havocs the callee's effects
					if (!isSummaryOfImplementedCall(edge)) {
						edges.add(edge);
						outgoing.add(LetterNaming.idOf(edge));
					}
				}
				final List<Integer> incoming = new ArrayList<>();
				for (final IcfgEdge edge : loc.getIncomingEdges()) {
					if (!isSummaryOfImplementedCall(edge)) {
						incoming.add(LetterNaming.idOf(edge));
					}
				}
				locations.add(new Location(proc, loc.getDebugIdentifier().toString(),
						loc.getDebugIdentifier().hashCode(), outgoing, incoming));
			}
		}
		edges.sort(Comparator.comparingInt(LetterNaming::idOf));
		final List<Edge> packedEdges = new ArrayList<>(edges.size());
		for (final IcfgEdge edge : edges) {
			packedEdges.add(edge(edge));
		}
		final Term axioms = mToolkit.getSmtFunctionsAndAxioms().getAxioms().getClosedFormula();
		collectSymbols(axioms);
		final List<String> declarations = declarations();
		return new ProgramPackage(mIcfg.getIdentifier(), logic(), declarations, programFunctions(symbols),
				freshVariables(), axioms.toString(), globals, constants, procedures, locations, specialLocations(),
				packedEdges);
	}

	private SpecialLocations specialLocations() {
		final Map<String, IcfgLocation> detached = new LinkedHashMap<>();
		final List<String> initial = names(mIcfg.getInitialNodes(), detached);
		final List<String> errors = new ArrayList<>();
		for (final Set<? extends IcfgLocation> procErrors : mIcfg.getProcedureErrorNodes().values()) {
			errors.addAll(names(procErrors, detached));
		}
		final List<String> entry = names(mIcfg.getProcedureEntryNodes().values(), detached);
		final List<String> exit = names(mIcfg.getProcedureExitNodes().values(), detached);
		final List<String> loopHeads = names(mIcfg.getLoopLocations(), detached);
		final List<String> ofInterest = names(mIcfg.getLocationsOfInterest(), detached);
		final List<DetachedLocation> detachedLocations = new ArrayList<>(detached.size());
		for (final IcfgLocation loc : detached.values()) {
			detachedLocations.add(new DetachedLocation(loc.getProcedure(), loc.getDebugIdentifier().toString(),
					loc.getDebugIdentifier().hashCode()));
		}
		return new SpecialLocations(initial, errors, entry, exit, loopHeads, ofInterest, detachedLocations);
	}

	/**
	 * @param detached
	 *            collects the locations that are not program points (see {@link SpecialLocations#detached()})
	 * @throws IllegalArgumentException
	 *             if such a location has edges, or its name is taken by another location
	 */
	private List<String> names(final Collection<? extends IcfgLocation> locs,
			final Map<String, IcfgLocation> detached) {
		final List<String> result = new ArrayList<>(locs.size());
		for (final IcfgLocation loc : locs) {
			if (mLocations.isProgramPoint(loc)) {
				result.add(mLocations.name(loc));
				continue;
			}
			if (!loc.getIncomingEdges().isEmpty() || !loc.getOutgoingEdges().isEmpty()) {
				throw new IllegalArgumentException("Special location " + loc + " is not a program point but has edges");
			}
			final String name = LocationNaming.nameOf(loc);
			if (mLocations.isName(name)) {
				throw new IllegalArgumentException("Special location " + loc + " has the name of a program point");
			}
			final IcfgLocation previous = detached.put(name, loc);
			if (previous != null && previous != loc) {
				throw new IllegalArgumentException("Two special locations named " + name);
			}
			result.add(name);
		}
		return result;
	}

	private FreshVariables freshVariables() {
		final ManagedScript mgdScript = mToolkit.getManagedScript();
		final List<FreshVariable> variables = new ArrayList<>();
		for (final String name : new TreeMap<>(mTermVariables).keySet()) {
			final TermVariable tv = mTermVariables.get(name);
			final String basename = mgdScript.getFreshVariableBasename(tv);
			if (basename != null) {
				variables.add(new FreshVariable(name, tv.getSort().toString(), basename));
			}
		}
		return new FreshVariables(mgdScript.getFreshVariableCounters(), variables);
	}

	/**
	 * The used functions that the symbol table knows as program functions (not constants).
	 */
	private List<String> programFunctions(final IIcfgSymbolTable symbols) {
		final List<String> result = new ArrayList<>();
		for (final Map.Entry<String, FunctionSymbol> entry : mFunctionSymbols.entrySet()) {
			final IProgramFunction fun = symbols.getProgramFun(entry.getValue());
			if (fun != null && !(fun instanceof IProgramConst)) {
				result.add(entry.getKey());
			}
		}
		result.sort(null);
		return result;
	}

	/**
	 * @return whether the edge summarizes a call to a procedure with an implementation; summaries of procedures without
	 *         one are internal edges like any other
	 */
	static boolean isSummaryOfImplementedCall(final IcfgEdge edge) {
		return edge instanceof IIcfgSummaryTransition<?>
				&& ((IIcfgSummaryTransition<?>) edge).calledProcedureHasImplementation();
	}

	private String logic() {
		return mToolkit.getManagedScript().getScript().getTheory().getLogic().name();
	}

	private void noteTermVariable(final TermVariable tv) {
		final TermVariable previous = mTermVariables.put(tv.getName(), tv);
		if (previous != null && previous != tv) {
			throw new IllegalArgumentException("Two term variables named " + tv.getName());
		}
	}

	private Variable variable(final IProgramVar var) {
		noteTermVariable(var.getTermVariable());
		collectSymbols(var.getDefaultConstant());
		collectSymbols(var.getPrimedConstant());
		collectSort(var.getSort());
		return new Variable(identifier(var), var.getSort().toString(), var.getTermVariable().getName(),
				var.getDefaultConstant().getFunction().getName(), var.getPrimedConstant().getFunction().getName());
	}

	/**
	 * The identifier of a variable; for an old variable the identifier of its non-old variable (as
	 * {@code ProgramOldVar} takes it).
	 */
	private static String identifier(final IProgramVar var) {
		if (var instanceof ILocalProgramVar) {
			return ((ILocalProgramVar) var).getIdentifier();
		}
		if (var instanceof IProgramNonOldVar) {
			return ((IProgramNonOldVar) var).getIdentifier();
		}
		if (var instanceof IProgramOldVar) {
			return ((IProgramOldVar) var).getIdentifierOfNonOldVar();
		}
		throw new UnsupportedOperationException(
				"Program variables of type " + var.getClass().getSimpleName() + " are not supported: " + var);
	}

	private Constant constant(final IProgramConst constant) {
		if (!(constant instanceof ProgramConst)) {
			throw new UnsupportedOperationException(
					"Program constants of type " + constant.getClass().getSimpleName() + " are not supported");
		}
		collectSymbols(constant.getDefaultConstant());
		return new Constant(constant.getIdentifier(), constant.getDefaultConstant().getFunction().getName(),
				((ProgramConst) constant).belongsToSmtTheory());
	}

	private Procedure procedure(final String proc, final IIcfgSymbolTable symbols) {
		final List<Variable> locals = new ArrayList<>();
		for (final ILocalProgramVar local : inOrder(symbols.getLocals(proc), ILocalProgramVar::getIdentifier)) {
			locals.add(variable(local));
		}
		final List<String> modifiable = new ArrayList<>();
		for (final IProgramNonOldVar global : mToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(proc)) {
			modifiable.add(global.getTermVariable().getName());
		}
		return new Procedure(proc, locals, termVariables(mToolkit.getInParams().get(proc)),
				termVariables(mToolkit.getOutParams().get(proc)), modifiable);
	}

	private static List<String> termVariables(final List<ILocalProgramVar> params) {
		if (params == null) {
			return List.of();
		}
		return params.stream().map(p -> p.getTermVariable().getName()).toList();
	}

	private static List<String> overapproximations(final IcfgEdge edge) {
		final Overapprox overapprox = Overapprox.getAnnotation(edge);
		if (overapprox == null || overapprox.getOverapproximatedLocations().isEmpty()) {
			return null;
		}
		final List<String> reasons = new ArrayList<>(overapprox.getOverapproximatedLocations().keySet());
		reasons.sort(null);
		return reasons;
	}

	private Edge edge(final IcfgEdge edge) {
		final int id = LetterNaming.idOf(edge);
		final List<String> overapproximations = overapproximations(edge);
		final String source = mLocations.name(edge.getSource());
		final String target = mLocations.name(edge.getTarget());
		if (edge instanceof IIcfgCallTransition<?>) {
			return new Edge(id, EdgeKind.CALL, source, target,
					transitionFormula(((IIcfgCallTransition<?>) edge).getLocalVarsAssignment()), null, null,
					overapproximations);
		}
		if (edge instanceof IIcfgReturnTransition<?, ?>) {
			final IIcfgReturnTransition<?, ?> ret = (IIcfgReturnTransition<?, ?>) edge;
			return new Edge(id, EdgeKind.RETURN, source, target, transitionFormula(ret.getAssignmentOfReturn()),
					null, LetterNaming.idOf(ret.getCorrespondingCall()), overapproximations);
		}
		if (edge instanceof IIcfgInternalTransition<?>) {
			final TransitionFormula tf = transitionFormula(edge.getTransformula());
			TransitionFormula withBranchEncoders = null;
			if (edge instanceof IActionWithBranchEncoders) {
				final TransitionFormula encoded = transitionFormula(
						((IActionWithBranchEncoders) edge).getTransitionFormulaWithBranchEncoders());
				if (!encoded.equals(tf)) {
					withBranchEncoders = encoded;
				}
			}
			return new Edge(id, EdgeKind.INTERNAL, source, target, tf, withBranchEncoders, null, overapproximations);
		}
		throw new UnsupportedOperationException(
				"Edges of type " + edge.getClass().getSimpleName() + " are not supported: " + edge);
	}

	private TransitionFormula transitionFormula(final UnmodifiableTransFormula tf) {
		collectSymbols(tf.getFormula());
		return new TransitionFormula(tf.getFormula().toString(), varMap(tf.getInVars()), varMap(tf.getOutVars()),
				typed(tf.getAuxVars()), typed(tf.getBranchEncoders()),
				tf.getNonTheoryConsts().stream().map(c -> c.getDefaultConstant().getFunction().getName()).toList(),
				tf.isInfeasible());
	}

	private Map<String, String> varMap(final Map<IProgramVar, TermVariable> vars) {
		final Map<String, String> result = new LinkedHashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> entry : vars.entrySet()) {
			final String key = entry.getKey().getTermVariable().getName();
			noteTermVariable(entry.getValue());
			if (result.put(key, entry.getValue().getName()) != null) {
				throw new IllegalArgumentException("Two program variables with the term variable " + key);
			}
		}
		return result;
	}

	private List<TypedName> typed(final Collection<TermVariable> vars) {
		final List<TypedName> result = new ArrayList<>(vars.size());
		for (final TermVariable var : vars) {
			noteTermVariable(var);
			collectSort(var.getSort());
			result.add(new TypedName(var.getName(), var.getSort().toString()));
		}
		return result;
	}

	/**
	 * Adds the non-theory functions and sorts of a term to the used symbols.
	 */
	private void collectSymbols(final Term root) {
		final Deque<Term> todo = new ArrayDeque<>();
		todo.push(root);
		while (!todo.isEmpty()) {
			final Term term = todo.pop();
			if (!mVisited.add(term)) {
				continue;
			}
			collectSort(term.getSort());
			if (term instanceof ApplicationTerm) {
				final FunctionSymbol fun = ((ApplicationTerm) term).getFunction();
				if (!fun.isIntern()) {
					mUsedFunctions.add(fun.getName());
					mFunctionSymbols.put(fun.getName(), fun);
				}
				for (final Term param : ((ApplicationTerm) term).getParameters()) {
					todo.push(param);
				}
			} else if (term instanceof QuantifiedFormula) {
				for (final TermVariable var : ((QuantifiedFormula) term).getVariables()) {
					noteTermVariable(var);
					collectSort(var.getSort());
				}
				todo.push(((QuantifiedFormula) term).getSubformula());
			} else if (term instanceof LetTerm) {
				for (final Term value : ((LetTerm) term).getValues()) {
					todo.push(value);
				}
				todo.push(((LetTerm) term).getSubTerm());
			} else if (term instanceof AnnotatedTerm) {
				todo.push(((AnnotatedTerm) term).getSubterm());
			} else if (term instanceof LambdaTerm) {
				todo.push(((LambdaTerm) term).getSubterm());
			} else if (term instanceof MatchTerm) {
				todo.push(((MatchTerm) term).getDataTerm());
				for (final Term caseTerm : ((MatchTerm) term).getCases()) {
					todo.push(caseTerm);
				}
			}
		}
	}

	private void collectSort(final Sort sort) {
		if (!sort.isInternal()) {
			mUsedSorts.add(sort.getName());
		}
		for (final Sort argument : sort.getArguments()) {
			collectSort(argument);
		}
	}

	/**
	 * The used declarations in declaration order. Defined functions add the symbols of their bodies; the history is
	 * scanned until nothing new is used.
	 */
	private List<String> declarations() {
		final HistoryRecordingScript history =
				HistoryRecordingScript.extractHistoryRecordingScript(mToolkit.getManagedScript().getScript());
		if (history == null) {
			throw new IllegalStateException("The ICFG's script records no history, so its declarations are unknown");
		}
		final List<ISmtDeclarable> declarations = history.getDeclarationsInOrder();
		boolean changed = true;
		while (changed) {
			changed = false;
			for (final ISmtDeclarable declaration : declarations) {
				if (declaration instanceof DeclarableFunctionSymbol
						&& mUsedFunctions.contains(declaration.getName())) {
					final DeclarableFunctionSymbol fun = (DeclarableFunctionSymbol) declaration;
					final int before = mUsedFunctions.size() + mUsedSorts.size();
					for (final Sort sort : fun.getParamSorts()) {
						collectSort(sort);
					}
					collectSort(fun.getResultSort());
					if (fun.getDefinition() != null) {
						collectSymbols(fun.getDefinition());
					}
					changed |= mUsedFunctions.size() + mUsedSorts.size() != before;
				} else if (declaration instanceof DeclarableSortSymbol && mUsedSorts.contains(declaration.getName())
						&& ((DeclarableSortSymbol) declaration).getDefinition() != null) {
					final int before = mUsedSorts.size();
					collectSort(((DeclarableSortSymbol) declaration).getDefinition());
					changed |= mUsedSorts.size() != before;
				}
			}
		}
		final Set<String> printed = new LinkedHashSet<>();
		final List<String> result = new ArrayList<>();
		for (final ISmtDeclarable declaration : declarations) {
			final boolean used = declaration instanceof DeclarableSortSymbol ? mUsedSorts.contains(declaration.getName())
					: mUsedFunctions.contains(declaration.getName());
			if (used && printed.add(declaration.getName())) {
				result.add(print(declaration));
			}
		}
		final Set<String> missing = new HashSet<>(mUsedFunctions);
		missing.removeAll(printed);
		if (!missing.isEmpty()) {
			throw new IllegalStateException("The ICFG uses functions its script never declared: " + missing);
		}
		return result;
	}

	private static String print(final ISmtDeclarable declaration) {
		final StringBuilder sb = new StringBuilder();
		if (declaration instanceof DeclarableSortSymbol) {
			final DeclarableSortSymbol sort = (DeclarableSortSymbol) declaration;
			if (sort.getDefinition() != null || sort.getParams() != null) {
				throw new UnsupportedOperationException("define-sort is not supported in a program package: " + sort);
			}
			sb.append("(declare-sort ").append(PrintTerm.quoteIdentifier(sort.getName())).append(' ')
					.append(sort.getArity()).append(')');
			return sb.toString();
		}
		if (!(declaration instanceof DeclarableFunctionSymbol)) {
			throw new UnsupportedOperationException(
					"SMT declarations of type " + declaration.getClass().getSimpleName() + " are not supported");
		}
		final DeclarableFunctionSymbol fun = (DeclarableFunctionSymbol) declaration;
		final Sort[] sorts = fun.getParamSorts();
		if (fun.getDefinition() == null) {
			sb.append("(declare-fun ").append(PrintTerm.quoteIdentifier(fun.getName())).append(" (");
			for (int i = 0; i < sorts.length; i++) {
				sb.append(i == 0 ? "" : " ").append(sorts[i]);
			}
			sb.append(") ").append(fun.getResultSort()).append(')');
		} else {
			final String[] ids = fun.getParamIds();
			sb.append("(define-fun ").append(PrintTerm.quoteIdentifier(fun.getName())).append(" (");
			for (int i = 0; i < sorts.length; i++) {
				if (ids[i] == null) {
					throw new UnsupportedOperationException("Unnamed parameter in the definition of " + fun.getName());
				}
				sb.append(i == 0 ? "" : " ").append('(').append(PrintTerm.quoteIdentifier(ids[i])).append(' ')
						.append(sorts[i]).append(')');
			}
			sb.append(") ").append(fun.getResultSort()).append(' ').append(fun.getDefinition()).append(')');
		}
		return sb.toString();
	}

	/**
	 * The items in their iteration order, which the reading side reproduces by inserting in this order.
	 *
	 * @throws IllegalArgumentException
	 *             if two items have the same key
	 */
	private static <T> List<T> inOrder(final Collection<? extends T> items,
			final java.util.function.Function<T, String> key) {
		final List<T> result = new ArrayList<>(items);
		final Set<String> keys = new HashSet<>();
		for (final T item : result) {
			if (!keys.add(key.apply(item))) {
				throw new IllegalArgumentException("Two program elements with the same key " + key.apply(item));
			}
		}
		return result;
	}
}
