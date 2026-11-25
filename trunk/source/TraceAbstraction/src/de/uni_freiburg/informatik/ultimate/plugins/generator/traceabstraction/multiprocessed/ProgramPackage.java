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
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;

/**
 * The program package (format PACKAGE_JSON_V1, message {@code PROGRAM_PACKAGE}): the ICFG that TraceAbstraction
 * receives, after block encoding, written by the FRONTEND session ({@link ProgramPackageWriter}). Every list is in a
 * deterministic order, so that equal programs give equal bytes.
 *
 * Variables are referred to by the name of their {@link de.uni_freiburg.informatik.ultimate.logic.TermVariable}, which
 * is unique among the program variables. Formulas and declarations are SMT-LIB text.
 *
 * @param logic
 *            the SMT logic of the script that built the ICFG
 * @param declarations
 *            the {@code declare-sort}, {@code define-sort}, {@code declare-fun} and {@code define-fun} commands the
 *            ICFG needs, in declaration order (the order in which they replay)
 * @param axioms
 *            the closed formula of the axioms
 * @param globals
 *            the global variables with their old variables, ordered by identifier
 * @param constants
 *            the global constants, ordered by identifier
 * @param procedures
 *            ordered by name
 * @param locations
 *            ordered by procedure and debug identifier
 * @param edges
 *            ordered by id
 */
public record ProgramPackage(String logic, List<String> declarations, String axioms, List<GlobalVariable> globals,
		List<Constant> constants, List<Procedure> procedures, List<Location> locations, List<Edge> edges) {

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
	 *            its local variables, including the parameters, ordered by identifier
	 * @param inParams
	 *            the term variables of its in-parameters, in parameter order
	 * @param outParams
	 *            the term variables of its out-parameters, in parameter order
	 * @param modifiableGlobals
	 *            the term variables of the globals it may modify, ordered
	 */
	public record Procedure(String name, List<Variable> locals, List<String> inParams, List<String> outParams,
			List<String> modifiableGlobals) {
	}

	/**
	 * A location, named {@code <procedure>::<debugId>} in messages (see {@link LocationNaming}).
	 */
	public record Location(String procedure, String debugId, boolean initial, boolean error, boolean entry,
			boolean exit, boolean loopHead) {
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
	 */
	public record Edge(int id, EdgeKind kind, String source, String target, TransitionFormula transFormula,
			TransitionFormula withBranchEncoders, Integer call) {
		static final Set<String> OPTIONAL = Set.of("withBranchEncoders", "call");
	}

	/**
	 * A transition formula.
	 *
	 * @param formula
	 *            SMT-LIB over the term variables of {@code inVars}, {@code outVars}, {@code auxVars} and
	 *            {@code branchEncoders}
	 * @param inVars
	 *            program variable (its term variable) to the term variable of the formula
	 * @param outVars
	 *            program variable (its term variable) to the term variable of the formula
	 * @param auxVars
	 *            ordered by name
	 * @param branchEncoders
	 *            ordered by name
	 * @param nonTheoryConsts
	 *            the SMT constants of the program constants the formula uses, ordered
	 */
	public record TransitionFormula(String formula, SortedMap<String, String> inVars,
			SortedMap<String, String> outVars, List<TypedName> auxVars, List<TypedName> branchEncoders,
			List<String> nonTheoryConsts, Infeasibility infeasibility) {
	}

	/**
	 * A term variable.
	 */
	public record TypedName(String name, String sort) {
	}
}
