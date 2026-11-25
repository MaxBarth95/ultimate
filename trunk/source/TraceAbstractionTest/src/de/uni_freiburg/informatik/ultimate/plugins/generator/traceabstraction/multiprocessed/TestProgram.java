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

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtParserUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SerialProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * A small program for the codec tests: {@code main} increments the global {@code x}, calls {@code f} and then may
 * reach its error location.
 *
 * <pre>
 * main::l0 --inc--> main::l1 --call--> f::entry --skip--> f::exit --return--> main::l2 --assume--> main::err
 * </pre>
 */
final class TestProgram {

	static final String MAIN = "main";
	static final String F = "f";

	final IUltimateServiceProvider mServices;
	final ILogger mLogger;
	final Script mScript;
	final ManagedScript mMgdScript;
	final DefaultIcfgSymbolTable mSymbolTable = new DefaultIcfgSymbolTable();
	final IProgramNonOldVar mX;
	final PredicateFactory mPredicateFactory;
	final BasicIcfg<IcfgLocation> mIcfg;

	final IcfgLocation mL0;
	final IcfgLocation mL1;
	final IcfgLocation mL2;
	final IcfgLocation mErr;
	final IcfgLocation mFEntry;
	final IcfgLocation mFExit;

	final IcfgEdge mInc;
	final IcfgCallTransition mCall;
	final IcfgEdge mSkip;
	final IcfgReturnTransition mReturn;
	final IcfgEdge mAssume;
	final VpAlphabet<IcfgEdge> mAlphabet;
	final IPredicate mEmptyStack;

	TestProgram() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.INFO);
		mLogger = mServices.getLoggingService().getLogger(TestProgram.class);
		mScript = new HistoryRecordingScript(UltimateMocks.createZ3Script(LogLevel.INFO));
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mX = ProgramVarUtils.constructGlobalProgramVarPair("x", SmtSortUtils.getIntSort(mScript), mMgdScript, null);
		mSymbolTable.add(mX);
		mPredicateFactory = new PredicateFactory(mServices, mMgdScript, mSymbolTable);

		final HashRelation<String, IProgramNonOldVar> modifiable = new HashRelation<>();
		modifiable.addPair(MAIN, mX);
		final IcfgEdgeFactory edgeFactory = new IcfgEdgeFactory(new SerialProvider());
		final CfgSmtToolkit toolkit = new CfgSmtToolkit(new ModifiableGlobalsTable(modifiable), mMgdScript,
				mSymbolTable, Set.of(MAIN, F), Collections.emptyMap(), Collections.emptyMap(), edgeFactory,
				new ConcurrencyInformation(Collections.emptyMap(), Collections.emptyMap(), Collections.emptySet()),
				new SmtFunctionsAndAxioms(mMgdScript));
		mIcfg = new BasicIcfg<>("test", toolkit, IcfgLocation.class);
		mIcfg.addProcedure(MAIN);
		mIcfg.addProcedure(F);
		mL0 = location(MAIN, "l0", true, false, true, false);
		mL1 = location(MAIN, "l1", false, false, false, false);
		mL2 = location(MAIN, "l2", false, false, false, true);
		mErr = location(MAIN, "err", false, true, false, false);
		mFEntry = location(F, "entry", false, false, true, false);
		mFExit = location(F, "exit", false, false, false, true);

		final UnmodifiableTransFormula skip = TransFormulaBuilder.getTrivialTransFormula(mMgdScript);
		final UnmodifiableTransFormula assume = TransFormulaBuilder.constructTransFormulaFromTerm(
				SmtParserUtils.parseWithVariables("(> x 1)", mServices, mMgdScript, mSymbolTable), Set.of(mX),
				mMgdScript);
		mInc = connect(edgeFactory.createInternalTransition(mL0, mL1, null, skip));
		mCall = edgeFactory.createCallTransition(mL1, mFEntry, null, skip);
		connect(mCall);
		mSkip = connect(edgeFactory.createInternalTransition(mFEntry, mFExit, null, skip));
		mReturn = edgeFactory.createReturnTransition(mFExit, mL2, mCall, null, skip, skip);
		connect(mReturn);
		mAssume = connect(edgeFactory.createInternalTransition(mL2, mErr, null, assume));
		mAlphabet = new VpAlphabet<>(Set.of(mInc, mSkip, mAssume), Set.of(mCall), Set.of(mReturn));
		mEmptyStack = mPredicateFactory.newEmptyStackPredicate();
	}

	private IcfgLocation location(final String proc, final String name, final boolean initial, final boolean error,
			final boolean entry, final boolean exit) {
		final IcfgLocation loc = new IcfgLocation(new StringDebugIdentifier(name), proc);
		mIcfg.addLocation(loc, initial, error, entry, exit, false, false);
		return loc;
	}

	private static <E extends IcfgEdge> E connect(final E edge) {
		edge.getSource().addOutgoing(edge);
		edge.getTarget().addIncoming(edge);
		return edge;
	}

	AutomataLibraryServices automataServices() {
		return new AutomataLibraryServices(mServices);
	}

	IEmptyStackStateFactory<IPredicate> emptyStackFactory() {
		return new IEmptyStackStateFactory<>() {
			@Override
			public IPredicate createEmptyStackState() {
				return mEmptyStack;
			}
		};
	}

	/**
	 * The abstraction of the program: one state per location, the program's edges as transitions.
	 */
	NestedWordAutomaton<IcfgEdge, IPredicate> abstraction() {
		final NestedWordAutomaton<IcfgEdge, IPredicate> nwa =
				new NestedWordAutomaton<>(automataServices(), mAlphabet, emptyStackFactory());
		final IPredicate l0 = state(mL0);
		final IPredicate l1 = state(mL1);
		final IPredicate l2 = state(mL2);
		final IPredicate err = state(mErr);
		final IPredicate fEntry = state(mFEntry);
		final IPredicate fExit = state(mFExit);
		nwa.addState(true, false, l0);
		nwa.addState(false, false, l1);
		nwa.addState(false, false, l2);
		nwa.addState(false, true, err);
		nwa.addState(false, false, fEntry);
		nwa.addState(false, false, fExit);
		nwa.addInternalTransition(l0, mInc, l1);
		nwa.addCallTransition(l1, mCall, fEntry);
		nwa.addInternalTransition(fEntry, mSkip, fExit);
		nwa.addReturnTransition(fExit, l1, mReturn, l2);
		nwa.addInternalTransition(l2, mAssume, err);
		return nwa;
	}

	IPredicate state(final IcfgLocation loc) {
		return mPredicateFactory.newSPredicate(loc, mScript.term("true"));
	}

	IPredicate formula(final String smt) {
		return mPredicateFactory
				.newPredicate(SmtParserUtils.parseWithVariables(smt, mServices, mMgdScript, mSymbolTable));
	}
}
