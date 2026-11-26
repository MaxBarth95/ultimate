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

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;

/**
 * The program package (format PACKAGE_JSON_V1, message {@code PROGRAM_PACKAGE}): the ICFG that TraceAbstraction
 * receives (the IcfgBuilder's output, with its large block encoding), written by the FRONTEND session
 * ({@link ProgramPackageWriter}). Every list is in a deterministic order, so that equal programs give equal bytes.
 *
 * Collections that the ICFG iterates (symbol table, procedures, program points, the edges of a location, the variables
 * of a transition formula) are written in the iteration order of the writing process, and read back by inserting in
 * that order; locations keep the hash code of their debug identifier. Then the reading process iterates them in the
 * same order, builds the same SMT queries in the same order, and behaves like a process that built the ICFG from C.
 *
 * Variables are referred to by the name of their {@link de.uni_freiburg.informatik.ultimate.logic.TermVariable}, which
 * is unique among the program variables. Formulas and declarations are SMT-LIB text.
 *
 * @param identifier
 *            the identifier of the ICFG
 * @param logic
 *            the SMT logic of the script that built the ICFG
 * @param declarations
 *            the {@code declare-sort}, {@code declare-fun} and {@code define-fun} commands the ICFG needs, in
 *            declaration order (the order in which they replay)
 * @param functions
 *            the declared or defined SMT functions that are program functions (e.g. Boogie functions), ordered
 * @param freshVariables
 *            the state of the script's variable manager, so that the reading side constructs the same fresh names
 * @param axioms
 *            the closed formula of the axioms
 * @param globals
 *            the global variables with their old variables, in the symbol table's iteration order
 * @param constants
 *            the global constants, in the symbol table's iteration order
 * @param procedures
 *            in the iteration order of {@code CfgSmtToolkit.getProcedures()}
 * @param locations
 *            in the iteration order of {@code IIcfg.getProgramPoints()}
 * @param special
 *            the initial, error, entry, exit and loop locations and the locations of interest, each in iteration
 *            order
 * @param edges
 *            ordered by id
 */
public record ProgramPackage(String identifier, String logic, List<String> declarations, List<String> functions,
		FreshVariables freshVariables, String axioms, List<GlobalVariable> globals,
		List<Constant> constants, List<Procedure> procedures, List<Location> locations, SpecialLocations special,
		List<Edge> edges) {

	/**
	 * The format of the package, the value of its {@code format} field.
	 */
	public static final String FORMAT = "PACKAGE_JSON_V1";

	/**
	 * A program variable.
	 *
	 * @param identifier
	 *            {@code IProgramVar.getIdentifier}
	 * @param sort
	 *            its SMT sort
	 * @param termVariable
	 *            the name of its term variable
	 * @param defaultConstant
	 *            the name of its default constant
	 * @param primedConstant
	 *            the name of its primed constant
	 */
	public record Variable(String identifier, String sort, String termVariable, String defaultConstant,
			String primedConstant) {
	}

	/**
	 * A global variable and its old variable.
	 */
	public record GlobalVariable(Variable variable, Variable oldVariable) {
	}

	/**
	 * A global constant.
	 *
	 * @param identifier
	 *            {@code IProgramConst.getIdentifier}
	 * @param constant
	 *            the name of its SMT constant
	 * @param theory
	 *            whether the constant belongs to the SMT theory
	 */
	public record Constant(String identifier, String constant, boolean theory) {
	}

	/**
	 * A procedure.
	 *
	 * @param locals
	 *            its local variables, including the parameters, in the symbol table's iteration order
	 * @param inParams
	 *            the term variables of its in-parameters, in parameter order
	 * @param outParams
	 *            the term variables of its out-parameters, in parameter order
	 * @param modifiableGlobals
	 *            the term variables of the globals it may modify, in the modifiable globals table's iteration order
	 */
	public record Procedure(String name, List<Variable> locals, List<String> inParams, List<String> outParams,
			List<String> modifiableGlobals) {
	}

	/**
	 * A location, named {@code <procedure>::<debugId>} in messages (see {@link LocationNaming}).
	 *
	 * @param hash
	 *            the hash code of its debug identifier, which the location's hash code is computed from
	 * @param outgoing
	 *            the ids of its outgoing edges, in their order at the location
	 * @param incoming
	 *            the ids of its incoming edges, in their order at the location
	 */
	public record Location(String procedure, String debugId, int hash, List<Integer> outgoing,
			List<Integer> incoming) {
	}

	/**
	 * The special locations of the ICFG, as {@link LocationNaming} names, each list in the iteration order of the
	 * collection it comes from ({@code getInitialNodes()}, {@code getProcedureErrorNodes()} flattened in key order,
	 * {@code getProcedureEntryNodes()}, {@code getProcedureExitNodes()}, {@code getLoopLocations()},
	 * {@code getLocationsOfInterest()}).
	 */
	public record SpecialLocations(List<String> initial, List<String> error, List<String> entry, List<String> exit,
			List<String> loopHeads, List<String> ofInterest) {
	}

	/**
	 * The kind of an edge.
	 */
	public enum EdgeKind {
		INTERNAL, CALL, RETURN
	}

	/**
	 * An edge. Its id is its letter name {@code e<id>} in messages.
	 *
	 * @param source
	 *            the {@link LocationNaming} name of the source
	 * @param target
	 *            the {@link LocationNaming} name of the target
	 * @param transFormula
	 *            the transition formula: for a call the assignment of the local variables, for a return the assignment
	 *            of the return values
	 * @param withBranchEncoders
	 *            for an internal edge, its transition formula with branch encoders, if it differs from
	 *            {@code transFormula}
	 * @param call
	 *            for a return, the id of its call
	 * @param overapproximations
	 *            the reasons why the edge overapproximates the program ({@code Overapprox} annotation), ordered; a
	 *            counterexample through such an edge does not prove a violation
	 */
	public record Edge(int id, EdgeKind kind, String source, String target, TransitionFormula transFormula,
			TransitionFormula withBranchEncoders, Integer call, List<String> overapproximations) {
		static final Set<String> OPTIONAL = Set.of("withBranchEncoders", "call", "overapproximations");
	}

	/**
	 * A transition formula.
	 *
	 * @param formula
	 *            SMT-LIB over the term variables of {@code inVars}, {@code outVars}, {@code auxVars} and
	 *            {@code branchEncoders}
	 * @param inVars
	 *            program variable (its term variable) to the term variable of the formula, in iteration order
	 * @param outVars
	 *            program variable (its term variable) to the term variable of the formula, in iteration order
	 * @param auxVars
	 *            in iteration order
	 * @param branchEncoders
	 *            in iteration order
	 * @param nonTheoryConsts
	 *            the SMT constants of the program constants the formula uses, in iteration order
	 */
	public record TransitionFormula(String formula, Map<String, String> inVars, Map<String, String> outVars,
			List<TypedName> auxVars, List<TypedName> branchEncoders,
			List<String> nonTheoryConsts, Infeasibility infeasibility) {
	}

	/**
	 * A term variable.
	 */
	public record TypedName(String name, String sort) {
	}

	/**
	 * The state of the {@code ManagedScript}'s variable manager: the counter of each basename and the basename of each
	 * term variable of the package that the manager constructed. With it, a reading process constructs the same fresh
	 * names as the writing one, and no fresh variable clashes with a variable of the package (term variables are equal
	 * when their names are).
	 *
	 * @param counters
	 *            basename to the number of fresh variables constructed for it
	 * @param variables
	 *            ordered by name
	 */
	public record FreshVariables(SortedMap<String, Integer> counters, List<FreshVariable> variables) {
	}

	/**
	 * A term variable and the basename the variable manager constructed it for.
	 */
	public record FreshVariable(String name, String sort, String basename) {
	}
}
