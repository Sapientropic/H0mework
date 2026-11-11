import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedSecondB.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxErrors 1
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalPairedSecondBConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace G
export OriginalPairedSecondBSource.Generated (reader result)
end G
namespace P
export OriginalPairedSecondBProgram (code b2Code wholeB2 environment)
end P
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace Price
export OriginalConstantFourierPriceMath (read scalarLift scalarRead scalar_lift)
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
private theorem trace_sound_value (env:Env Prog.Value Prog.Var) (e:Prog.E) (value:BurnolL2)
    (actual:Trace env e (.const value)) : @Eq BurnolL2 value (e.eval env) := by
  have source : @Eq BurnolL2 (e.eval env) value := Trace.sound actual
  exact source.symm
namespace EndRead
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (root:SourceNativeLivingRootClosure W V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7:U7ProducerCalculus W) (calculus:U7ObstructionEvolutionCalculus W u7)
variable (c:BurnolCompletedMellinCoordinate) (paired:BurnolL2)
local notation "reader"=>(fun _=>G.reader root.toAuthoritativeRoot c paired (root.emitted visit.current))
local notation "actualValue"=>Adapter.terminalValue (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader
include root visit u7 calculus c paired in
private theorem terminal_value : @Eq BurnolL2 actualValue
    (OC.value (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root.toAuthoritativeRoot visit.current reader) := by
  unfold Adapter.terminalValue
  rw [expression (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader]
  rfl
include root visit u7 calculus c paired in
private theorem terminal_expr :
    (.const (OC.value (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root.toAuthoritativeRoot visit.current reader):Prog.E)=
      .const actualValue :=
  congrArg (fun value:BurnolL2=>(.const value:Prog.E)) (terminal_value root visit u7 calculus c paired).symm
noncomputable def actualTrace : Trace (P.environment paired) (P.code c) (.const actualValue) :=
  Eq.mp (congrArg (Trace (P.environment paired) (P.code c)) (terminal_expr root visit u7 calculus c paired))
    (normalizedTrace (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader)
noncomputable def pairedReceipt := OriginalPairedSecondBProgram.Traced.pairedReceipt c (actualTrace root visit u7 calculus c paired)
noncomputable def b2Receipt := OriginalPairedSecondBProgram.Traced.b2Receipt c (actualTrace root visit u7 calculus c paired)
include root visit u7 calculus c paired in
theorem paid_all : (Adapter.state (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader).2.length=3 :=
  (paid (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader).trans (OriginalPairedSecondBProgram.code_budget c)
include root visit u7 calculus c paired in
theorem result_value : @Eq BurnolL2 actualValue ((G.result root.toAuthoritativeRoot visit.current c paired).2.2.1) :=
  (terminal_value root visit u7 calculus c paired).trans
    (value_source root.toAuthoritativeRoot visit.current (G.reader root.toAuthoritativeRoot c paired))
include root visit u7 calculus c paired in
theorem paired_read : @Eq BurnolL2 (pairedReceipt root visit u7 calculus c paired).value paired :=
  OriginalPairedSecondBProgram.Traced.paired_read c (actualTrace root visit u7 calculus c paired)
include root visit u7 calculus c paired in
theorem b2_read : @Eq BurnolL2 (b2Receipt root visit u7 calculus c paired).value (P.wholeB2 paired) :=
  OriginalPairedSecondBProgram.Traced.b2_read c (actualTrace root visit u7 calculus c paired)
include root visit u7 calculus c paired in
private theorem trace_value : @Eq BurnolL2 actualValue ((P.code c).eval (P.environment paired)) :=
  trace_sound_value (P.environment paired) (P.code c) actualValue (actualTrace root visit u7 calculus c paired)
include root visit u7 calculus c paired in
theorem source_equation : Price.scalarRead actualValue=
    (-2*OriginalWholeDebtRAdjointContactSource.sigma c c)*
      OriginalKForcedInverseSourceCalculation.matrixRead c (b2Receipt root visit u7 calculus c paired).value := by
  have literal : @Eq BurnolL2 actualValue (OriginalSecondBGammaProgram.operation c c (P.wholeB2 paired)) :=
    (trace_value root visit u7 calculus c paired).trans (OriginalPairedSecondBProgram.code_eval c paired)
  have read : Price.scalarRead actualValue=(-2*OriginalWholeDebtRAdjointContactSource.sigma c c)*
      OriginalKForcedInverseSourceCalculation.matrixRead c (P.wholeB2 paired) :=
    (congrArg Price.scalarRead literal).trans (Price.scalar_lift _)
  exact read.trans (congrArg (fun value:BurnolL2=>(-2*OriginalWholeDebtRAdjointContactSource.sigma c c)*
    OriginalKForcedInverseSourceCalculation.matrixRead c value) (b2_read root visit u7 calculus c paired).symm)
include root visit u7 calculus c paired in
theorem output (actual:paired=OriginalKPairedBEulerJunctionSource.sourceAction c) :
    @Eq BurnolL2 actualValue (Price.scalarLift (Gamma.nativeGamma c c)) :=
  (trace_value root visit u7 calculus c paired).trans (OriginalPairedSecondBProgram.code_actual c paired actual)
include root visit u7 calculus c paired in
theorem gamma_read (actual:paired=OriginalKPairedBEulerJunctionSource.sourceAction c) :
    Price.scalarRead actualValue=Gamma.nativeGamma c c :=
  (congrArg Price.scalarRead (output root visit u7 calculus c paired actual)).trans (Price.scalar_lift _)
include root visit u7 calculus c paired in
theorem b2_actual (actual:paired=OriginalKPairedBEulerJunctionSource.sourceAction c) :
    (b2Receipt root visit u7 calculus c paired).value=
      burnolQuarterZeroExtension (OriginalKPairedBEulerJunctionSource.sourceSecond c:BurnolQuarterIntervalL2) :=
  (b2_read root visit u7 calculus c paired).trans (OriginalPairedSecondBProgram.wholeB2_actual c paired actual)
include root visit u7 calculus c paired in
theorem first_block : burnolAmbientMeanZeroFirstCorrection paired+
    burnolMeanZeroTruncatedFourier (Price.read (b2Receipt root visit u7 calculus c paired).value)=burnolAmbientMeanZeroPosition paired :=
  (congrArg (fun value:BurnolL2=>burnolAmbientMeanZeroFirstCorrection paired+burnolMeanZeroTruncatedFourier (Price.read value))
    (b2_read root visit u7 calculus c paired)).trans (OriginalPairedSecondBProgram.first_block paired)
include root visit u7 calculus c paired in
theorem second_block : burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection paired)+
    Price.read (b2Receipt root visit u7 calculus c paired).value=burnolAmbientMeanZeroFourier paired :=
  (congrArg (fun value:BurnolL2=>burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection paired)+Price.read value)
    (b2_read root visit u7 calculus c paired)).trans (OriginalPairedSecondBProgram.second_block paired)
include root visit u7 calculus c paired in
theorem first_full_block :
    ((burnolAmbientMeanZeroFirstCorrection paired+burnolMeanZeroTruncatedFourier
      (Price.read (b2Receipt root visit u7 calculus c paired).value):BurnolQuarterMeanZeroCarrier):BurnolQuarterIntervalL2)+
      OriginalPairedSecondBProgram.positionMean paired • intervalConstant (1/4:ℝ)=OriginalPairedSecondBProgram.positionInput paired :=
  (congrArg (fun value:BurnolL2=>((burnolAmbientMeanZeroFirstCorrection paired+burnolMeanZeroTruncatedFourier
      (Price.read value):BurnolQuarterMeanZeroCarrier):BurnolQuarterIntervalL2)+
        OriginalPairedSecondBProgram.positionMean paired • intervalConstant (1/4:ℝ))
    (b2_read root visit u7 calculus c paired)).trans (OriginalPairedSecondBProgram.first_full_block paired)
include root visit u7 calculus c paired in
theorem second_full_block :
    ((burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection paired)+
      Price.read (b2Receipt root visit u7 calculus c paired).value:BurnolQuarterMeanZeroCarrier):BurnolQuarterIntervalL2)+
      OriginalPairedSecondBProgram.fourierMean paired • intervalConstant (1/4:ℝ)=OriginalPairedSecondBProgram.fourierInput paired :=
  (congrArg (fun value:BurnolL2=>((burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection paired)+
      Price.read value:BurnolQuarterMeanZeroCarrier):BurnolQuarterIntervalL2)+
        OriginalPairedSecondBProgram.fourierMean paired • intervalConstant (1/4:ℝ))
    (b2_read root visit u7 calculus c paired)).trans (OriginalPairedSecondBProgram.second_full_block paired)
include root visit u7 calculus c paired in
theorem material_value_transport (actual:paired=OriginalKPairedBEulerJunctionSource.sourceAction c) (material:BurnolL2)
    (material_source:material=burnolQuarterZeroExtension (OriginalKPairedBEulerJunctionSource.sourceSecond c:BurnolQuarterIntervalL2)) :
    (b2Receipt root visit u7 calculus c paired).value=material :=
  (b2_actual root visit u7 calculus c paired actual).trans material_source.symm
end EndRead
attribute [local irreducible] OriginalPairedSecondBSource.Generated.result
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ) (N:Nat)
local notation "src"=>OriginalPairedSecondBAction.sourceRoot observation nontrivial half depth ordinal t N
local notation "here"=>OriginalPairedSecondBAction.sourceVisit observation nontrivial half depth ordinal t N
local notation "u7"=>OriginalPairedSecondBAction.sourceU7 observation nontrivial half depth ordinal t N
local notation "calculus"=>OriginalPairedSecondBAction.sourceCalculus observation nontrivial half depth ordinal t N
local notation "reader"=>OriginalPairedSecondBAction.sourceReader observation nontrivial half depth ordinal t N
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "paired"=>OriginalPairedSecondBOrigin.pairedValue observation nontrivial half depth ordinal t N
noncomputable def nextFace := Adapter.targetFace (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextState : SourceOperationExecutionDebt.State (P.environment paired) (P.code c) :=
  Adapter.state (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextValue : BurnolL2 := Adapter.terminalValue (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextTrace : Trace (P.environment paired) (P.code c) (.const (nextValue observation nontrivial half depth ordinal t N)) :=
  EndRead.actualTrace src here u7 calculus c paired
noncomputable def pairedReceipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) (.var (0:Fin 2)) :=
  EndRead.pairedReceipt src here u7 calculus c paired
noncomputable def b2Receipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) P.b2Code :=
  EndRead.b2Receipt src here u7 calculus c paired
noncomputable def b2Value : BurnolL2 := (b2Receipt observation nontrivial half depth ordinal t N).value
noncomputable abbrev next_state_source := state_source (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable abbrev next_trace_source := trace_source (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable abbrev next_paid := EndRead.paid_all src here u7 calculus c paired
noncomputable abbrev next_value_source := EndRead.result_value src here u7 calculus c paired
noncomputable abbrev actual_paired_read := EndRead.paired_read src here u7 calculus c paired
noncomputable abbrev actual_b2_read := EndRead.b2_read src here u7 calculus c paired
noncomputable abbrev actual_source_equation := EndRead.source_equation src here u7 calculus c paired
noncomputable abbrev actual_output := EndRead.output src here u7 calculus c paired
  (OriginalPairedSecondBOrigin.paired_actual observation nontrivial half depth ordinal t N)
noncomputable abbrev actual_Gamma := EndRead.gamma_read src here u7 calculus c paired
  (OriginalPairedSecondBOrigin.paired_actual observation nontrivial half depth ordinal t N)
noncomputable abbrev actual_b2 := EndRead.b2_actual src here u7 calculus c paired
  (OriginalPairedSecondBOrigin.paired_actual observation nontrivial half depth ordinal t N)
noncomputable abbrev actual_first_block := EndRead.first_block src here u7 calculus c paired
noncomputable abbrev actual_second_block := EndRead.second_block src here u7 calculus c paired
noncomputable abbrev actual_first_full_block := EndRead.first_full_block src here u7 calculus c paired
noncomputable abbrev actual_second_full_block := EndRead.second_full_block src here u7 calculus c paired
noncomputable abbrev old_material_value_transport := EndRead.material_value_transport src here u7 calculus c paired
  (OriginalPairedSecondBOrigin.paired_actual observation nontrivial half depth ordinal t N)
  (OriginalSecondBContactOrigin.secondValue observation nontrivial half depth ordinal t N)
  (OriginalSecondBContactOrigin.second_actual observation nontrivial half depth ordinal t N)
noncomputable abbrev sourceParentTrace := OriginalPairedSecondBOrigin.parentTrace observation nontrivial half depth
noncomputable abbrev sourceBoundaryReceipt := OriginalPairedSecondBOrigin.boundaryReceipt observation nontrivial half depth
noncomputable abbrev sourcePlusKernelReceipt := OriginalPairedSecondBOrigin.plusKernelReceipt observation nontrivial half depth
noncomputable abbrev sourceMinusKernelReceipt := OriginalPairedSecondBOrigin.minusKernelReceipt observation nontrivial half depth
noncomputable abbrev sourceCursor := OriginalPairedSecondBOrigin.actualCursor observation nontrivial half depth
noncomputable abbrev sourceIndex := OriginalPairedSecondBOrigin.actualIndex observation nontrivial half depth
noncomputable abbrev source_index_position := OriginalPairedSecondBOrigin.actual_index_position observation nontrivial half depth
noncomputable abbrev sourceOccurrence := OriginalPairedSecondBOrigin.actualOccurrence observation nontrivial half depth ordinal
noncomputable abbrev source_occurrence_word := OriginalPairedSecondBOrigin.actual_word observation nontrivial half depth ordinal
noncomputable abbrev sourceHistory := OriginalPairedSecondBOrigin.currentHistory observation nontrivial half depth ordinal t N
noncomputable abbrev sourceWord := OriginalPairedSecondBOrigin.pairedWord observation nontrivial half depth ordinal t N
noncomputable abbrev source_word_source := OriginalPairedSecondBOrigin.paired_word_source observation nontrivial half depth ordinal t N
noncomputable abbrev sourcePairedReceipt := OriginalPairedSecondBOrigin.pairedReceipt observation nontrivial half depth ordinal t N
noncomputable abbrev sourcePairedTrace := OriginalPairedSecondBOrigin.pairedTrace observation nontrivial half depth ordinal t N
noncomputable abbrev source_paired_address := OriginalPairedSecondBOrigin.paired_address observation nontrivial half depth
noncomputable abbrev source_plus_kernel := OriginalPairedSecondBOrigin.plus_kernel_actual observation nontrivial half depth
noncomputable abbrev source_minus_kernel := OriginalPairedSecondBOrigin.minus_kernel_actual observation nontrivial half depth
noncomputable abbrev actual_input_source_lineage :=
  (actual_paired_read observation nontrivial half depth ordinal t N).trans
    (OriginalPairedSecondBOrigin.paired_receipt_read observation nontrivial half depth ordinal t N).symm
noncomputable def retainedInputState := (OriginalPairedSecondBAction.actualInputFace observation nontrivial half depth ordinal t N).rootRead
noncomputable abbrev retained_input_state := OriginalPairedSecondBAction.target_input_state observation nontrivial half depth ordinal t N
noncomputable abbrev retained_origin_payload := OriginalPairedSecondBAction.target_source_payload observation nontrivial half depth ordinal t N
end OriginalPairedSecondBConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalPairedSecondBConsumer"
