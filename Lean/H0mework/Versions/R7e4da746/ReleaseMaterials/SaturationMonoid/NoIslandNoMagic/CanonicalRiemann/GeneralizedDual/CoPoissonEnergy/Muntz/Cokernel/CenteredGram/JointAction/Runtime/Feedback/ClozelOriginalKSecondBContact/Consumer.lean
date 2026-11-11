import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSecondBContact.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxErrors 1
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalSecondBGammaConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace G
export OriginalSecondBGammaSource.Generated (reader result)
end G
namespace P
export OriginalSecondBGammaProgram (code environment)
end P
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace Price
export OriginalConstantFourierPriceMath (scalarLift scalarRead scalar_lift)
end Price
namespace Gamma
export OriginalWholeDebtRJointMobiusContactPsiPriceSource (nativeGamma)
end Gamma
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (targetFace state terminalValue)
end Adapter
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value)
end OC
open private normalizedTrace paid expression state_source trace_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private value_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Action
namespace EndRead
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (root:SourceNativeLivingRootClosure W V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7:U7ProducerCalculus W) (calculus:U7ObstructionEvolutionCalculus W u7)
variable (c:BurnolCompletedMellinCoordinate) (second:BurnolL2)
local notation "reader"=>(fun _=>G.reader root.toAuthoritativeRoot c second (root.emitted visit.current))
local notation "actualValue"=>Adapter.terminalValue (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader
include root visit u7 calculus c second in
private theorem terminal_value : @Eq BurnolL2 actualValue
    (OC.value (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root.toAuthoritativeRoot visit.current reader) := by
  unfold Adapter.terminalValue
  rw [expression (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader]
  rfl
include root visit u7 calculus c second in
private theorem terminal_expr :
    (.const (OC.value (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root.toAuthoritativeRoot visit.current reader):Prog.E)=
      .const actualValue :=
  congrArg (fun value:BurnolL2=>(.const value:Prog.E)) (terminal_value root visit u7 calculus c second).symm
noncomputable def actualTrace : Trace (P.environment second) (P.code c c) (.const actualValue) :=
  Eq.mp (congrArg (Trace (P.environment second) (P.code c c)) (terminal_expr root visit u7 calculus c second))
    (normalizedTrace (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader)
noncomputable def secondReceipt := OriginalSecondBGammaProgram.Traced.secondReceipt c c (actualTrace root visit u7 calculus c second)
include root visit u7 calculus c second in
theorem paid_all : (Adapter.state (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader).2.length=2 :=
  (paid (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader).trans (OriginalSecondBGammaProgram.code_budget c c)
include root visit u7 calculus c second in
theorem result_value : @Eq BurnolL2 actualValue ((G.result root.toAuthoritativeRoot visit.current c second).2.2.1) :=
  (terminal_value root visit u7 calculus c second).trans
    (value_source root.toAuthoritativeRoot visit.current (G.reader root.toAuthoritativeRoot c second))
include root visit u7 calculus c second in
theorem second_read : @Eq BurnolL2 (secondReceipt root visit u7 calculus c second).value second :=
  OriginalSecondBGammaProgram.Traced.second_read c c (actualTrace root visit u7 calculus c second)
include root visit u7 calculus c second in
theorem source_equation : Price.scalarRead actualValue=
    (-2*OriginalWholeDebtRAdjointContactSource.sigma c c)*
      OriginalKForcedInverseSourceCalculation.matrixRead c second := by
  have literal : @Eq BurnolL2 actualValue (OriginalSecondBGammaProgram.operation c c second) :=
    (actualTrace root visit u7 calculus c second).sound.symm.trans
      (OriginalSecondBGammaProgram.code_eval c c second)
  exact (congrArg Price.scalarRead literal).trans (Price.scalar_lift _)
include root visit u7 calculus c second in
theorem output (actual:second=burnolQuarterZeroExtension (OriginalKPairedBEulerJunctionSource.sourceSecond c:BurnolQuarterIntervalL2)) :
    @Eq BurnolL2 actualValue (Price.scalarLift (Gamma.nativeGamma c c)) :=
  (result_value root visit u7 calculus c second).trans
    (OriginalSecondBGammaSource.Generated.output root.toAuthoritativeRoot visit.current c second actual)
include root visit u7 calculus c second in
theorem gamma_read (actual:second=burnolQuarterZeroExtension (OriginalKPairedBEulerJunctionSource.sourceSecond c:BurnolQuarterIntervalL2)) :
    Price.scalarRead actualValue=Gamma.nativeGamma c c :=
  (congrArg Price.scalarRead (output root visit u7 calculus c second actual)).trans (Price.scalar_lift _)
include root visit u7 calculus c second in
theorem complete_C (correction first:BurnolL2)
    (complete:correction=first+fourierL2 second) :
    correction=first+fourierL2 (secondReceipt root visit u7 calculus c second).value :=
  complete.trans (congrArg (fun value:BurnolL2=>first+fourierL2 value)
    (second_read root visit u7 calculus c second).symm)
end EndRead
attribute [local irreducible] OriginalSecondBGammaSource.Generated.result
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ) (N:Nat)
local notation "src"=>OriginalSecondBGammaAction.sourceRoot observation nontrivial half depth ordinal t N
local notation "here"=>OriginalSecondBGammaAction.sourceVisit observation nontrivial half depth ordinal t N
local notation "u7"=>OriginalSecondBGammaAction.sourceU7 observation nontrivial half depth ordinal t N
local notation "calculus"=>OriginalSecondBGammaAction.sourceCalculus observation nontrivial half depth ordinal t N
local notation "reader"=>OriginalSecondBGammaAction.sourceReader observation nontrivial half depth ordinal t N
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "second"=>OriginalSecondBContactOrigin.secondValue observation nontrivial half depth ordinal t N
noncomputable def nextFace := Adapter.targetFace (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextState : SourceOperationExecutionDebt.State (P.environment second) (P.code c c) :=
  Adapter.state (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextValue : BurnolL2 := Adapter.terminalValue (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextTrace : Trace (P.environment second) (P.code c c)
    (.const (nextValue observation nontrivial half depth ordinal t N)) :=
  EndRead.actualTrace src here u7 calculus c second
noncomputable def secondReceipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) (.var (0:Fin 2)) :=
  EndRead.secondReceipt src here u7 calculus c second
noncomputable abbrev next_state_source := state_source (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable abbrev next_trace_source := trace_source (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable abbrev next_paid := EndRead.paid_all src here u7 calculus c second
noncomputable abbrev next_value_source := EndRead.result_value src here u7 calculus c second
noncomputable abbrev actual_second_read := EndRead.second_read src here u7 calculus c second
noncomputable abbrev actual_output := EndRead.output src here u7 calculus c second
  (OriginalSecondBContactOrigin.second_actual observation nontrivial half depth ordinal t N)
noncomputable abbrev actual_source_equation := EndRead.source_equation src here u7 calculus c second
noncomputable abbrev actual_Gamma := EndRead.gamma_read src here u7 calculus c second
  (OriginalSecondBContactOrigin.second_actual observation nontrivial half depth ordinal t N)
noncomputable abbrev originalCorrectionTrace := OriginalSecondBContactOrigin.correctionTrace observation nontrivial half depth ordinal t N
noncomputable abbrev firstLineage := OriginalSecondBContactOrigin.firstReceipt observation nontrivial half depth ordinal t N
noncomputable abbrev secondLineage := OriginalSecondBContactOrigin.secondReceipt observation nontrivial half depth ordinal t N
noncomputable abbrev original_first_address := OriginalSecondBContactOrigin.first_address observation nontrivial half depth ordinal t N
noncomputable abbrev original_second_address := OriginalSecondBContactOrigin.second_address observation nontrivial half depth ordinal t N
noncomputable abbrev actual_complete_C := EndRead.complete_C src here u7 calculus c second
  (OriginalSecondBContactOrigin.correctionValue observation nontrivial half depth ordinal t N)
  (OriginalSecondBContactOrigin.firstValue observation nontrivial half depth ordinal t N)
  (OriginalSecondBContactOrigin.complete_equation observation nontrivial half depth ordinal t N)
noncomputable def retainedInputState := (OriginalSecondBGammaAction.actualInputFace observation nontrivial half depth ordinal t N).rootRead
noncomputable abbrev retained_input_state := OriginalSecondBGammaAction.target_input_state observation nontrivial half depth ordinal t N
noncomputable abbrev retained_origin_payload := OriginalSecondBGammaAction.target_source_payload observation nontrivial half depth ordinal t N
end OriginalSecondBGammaConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalSecondBGammaConsumer"
