import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryGamma.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxErrors 1
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalBoundaryGammaConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace G
export OriginalBoundaryGammaSource.Generated (reader result)
end G
namespace P
export OriginalBoundaryGammaProgram (code physicalCode recoveredCode pairedCode b2Code physical wholeInverse dilation environment)
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
private theorem inverse_fibre (c:BurnolCompletedMellinCoordinate) (raw:BurnolL2) :
    OriginalBoundaryGammaResolvent.boundaryOperator c
      (burnolEvenAmbientProjection (P.wholeInverse c (P.physical raw)))=
        burnolEvenAmbientProjection (P.physical raw) := by
  have projected (value:BurnolPaAmbientCarrier) : burnolEvenAmbientProjection (value:BurnolL2)=value :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  have recovered : burnolEvenAmbientProjection (P.wholeInverse c (P.physical raw))=
      OriginalBoundaryGammaResolvent.inverse c c.rightHalf (burnolEvenAmbientProjection raw) :=
    (congrArg burnolEvenAmbientProjection (OriginalBoundaryGammaProgram.inverse_physical c raw)).trans (projected _)
  have input : burnolEvenAmbientProjection (P.physical raw)=burnolEvenAmbientProjection raw := projected _
  exact (congrArg (OriginalBoundaryGammaResolvent.boundaryOperator c) recovered).trans
    ((OriginalBoundaryGammaResolvent.inverse_right c c.rightHalf (burnolEvenAmbientProjection raw)).trans input.symm)

namespace EndRead
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (root:SourceNativeLivingRootClosure W V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7:U7ProducerCalculus W) (calculus:U7ObstructionEvolutionCalculus W u7)
variable (c:BurnolCompletedMellinCoordinate) (raw:BurnolL2)
local notation "reader"=>(fun _=>G.reader root.toAuthoritativeRoot c raw (root.emitted visit.current))
local notation "actualValue"=>Adapter.terminalValue (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader
include root visit u7 calculus c raw in
private theorem terminal_value : @Eq BurnolL2 actualValue
    (OC.value (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root.toAuthoritativeRoot visit.current reader) := by
  unfold Adapter.terminalValue
  rw [expression (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader]
  rfl
include root visit u7 calculus c raw in
private theorem terminal_expr :
    (.const (OC.value (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root.toAuthoritativeRoot visit.current reader):Prog.E)=
      .const actualValue :=
  congrArg (fun value:BurnolL2=>(.const value:Prog.E)) (terminal_value root visit u7 calculus c raw).symm
noncomputable def actualTrace : Trace (P.environment raw) (P.code c) (.const actualValue) :=
  Eq.mp (congrArg (Trace (P.environment raw) (P.code c)) (terminal_expr root visit u7 calculus c raw))
    (normalizedTrace (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader)
noncomputable def rawReceipt := OriginalBoundaryGammaProgram.Traced.rawReceipt c (actualTrace root visit u7 calculus c raw)
noncomputable def physicalReceipt := OriginalBoundaryGammaProgram.Traced.physicalReceipt c (actualTrace root visit u7 calculus c raw)
noncomputable def recoveredReceipt := OriginalBoundaryGammaProgram.Traced.recoveredReceipt c (actualTrace root visit u7 calculus c raw)
noncomputable def pairedReceipt := OriginalBoundaryGammaProgram.Traced.pairedReceipt c (actualTrace root visit u7 calculus c raw)
noncomputable def b2Receipt := OriginalBoundaryGammaProgram.Traced.b2Receipt c (actualTrace root visit u7 calculus c raw)
include root visit u7 calculus c raw in
theorem paid_all : (Adapter.state (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader).2.length=6 :=
  (paid (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader).trans (OriginalBoundaryGammaProgram.code_budget c)
include root visit u7 calculus c raw in
theorem result_value : @Eq BurnolL2 actualValue ((G.result root.toAuthoritativeRoot visit.current c raw).2.2.1) :=
  (terminal_value root visit u7 calculus c raw).trans
    (value_source root.toAuthoritativeRoot visit.current (G.reader root.toAuthoritativeRoot c raw))
include root visit u7 calculus c raw in
theorem raw_read : @Eq BurnolL2 (rawReceipt root visit u7 calculus c raw).value (raw) :=
  OriginalBoundaryGammaProgram.Traced.raw_read c (actualTrace root visit u7 calculus c raw)
include root visit u7 calculus c raw in
theorem physical_read : @Eq BurnolL2 (physicalReceipt root visit u7 calculus c raw).value (P.physical raw) :=
  OriginalBoundaryGammaProgram.Traced.physical_read c (actualTrace root visit u7 calculus c raw)
include root visit u7 calculus c raw in
theorem recovered_read : @Eq BurnolL2 (recoveredReceipt root visit u7 calculus c raw).value (P.wholeInverse c (P.physical raw)) :=
  OriginalBoundaryGammaProgram.Traced.recovered_read c (actualTrace root visit u7 calculus c raw)
include root visit u7 calculus c raw in
theorem paired_read : @Eq BurnolL2 (pairedReceipt root visit u7 calculus c raw).value (P.dilation (P.wholeInverse c (P.physical raw))) :=
  OriginalBoundaryGammaProgram.Traced.paired_read c (actualTrace root visit u7 calculus c raw)
include root visit u7 calculus c raw in
theorem b2_read : @Eq BurnolL2 (b2Receipt root visit u7 calculus c raw).value (OriginalPairedSecondBProgram.wholeB2 (P.dilation (P.wholeInverse c (P.physical raw)))) :=
  OriginalBoundaryGammaProgram.Traced.b2_read c (actualTrace root visit u7 calculus c raw)
include root visit u7 calculus c raw in
private theorem trace_value : @Eq BurnolL2 actualValue ((P.code c).eval (P.environment raw)) :=
  trace_sound_value (P.environment raw) (P.code c) actualValue (actualTrace root visit u7 calculus c raw)
include root visit u7 calculus c raw in
theorem b2_from_paired : (b2Receipt root visit u7 calculus c raw).value=
    OriginalPairedSecondBProgram.wholeB2 (pairedReceipt root visit u7 calculus c raw).value :=
  (b2_read root visit u7 calculus c raw).trans
    (congrArg OriginalPairedSecondBProgram.wholeB2 (paired_read root visit u7 calculus c raw).symm)
include root visit u7 calculus c raw in
theorem source_equation : Price.scalarRead actualValue=
    (-2*OriginalWholeDebtRAdjointContactSource.sigma c c)*
      OriginalKForcedInverseSourceCalculation.matrixRead c (b2Receipt root visit u7 calculus c raw).value := by
  have literal : @Eq BurnolL2 actualValue (OriginalSecondBGammaProgram.operation c c
      (OriginalPairedSecondBProgram.wholeB2 (P.dilation (P.wholeInverse c (P.physical raw))))) :=
    (trace_value root visit u7 calculus c raw).trans (OriginalBoundaryGammaProgram.code_eval c raw)
  have read : Price.scalarRead actualValue=(-2*OriginalWholeDebtRAdjointContactSource.sigma c c)*
      OriginalKForcedInverseSourceCalculation.matrixRead c
        (OriginalPairedSecondBProgram.wholeB2 (P.dilation (P.wholeInverse c (P.physical raw)))) :=
    (congrArg Price.scalarRead literal).trans (Price.scalar_lift _)
  exact read.trans (congrArg (fun value:BurnolL2=>(-2*OriginalWholeDebtRAdjointContactSource.sigma c c)*
    OriginalKForcedInverseSourceCalculation.matrixRead c value) (b2_read root visit u7 calculus c raw).symm)
include root visit u7 calculus c raw in
theorem output (zero:riemannZeta c.value=0) (actual:burnolEvenAmbientProjection raw=burnolZeroPairedFixedAnnulusBoundary c zero OriginalKPairedBEulerJunctionSource.junctionShift) :
    @Eq BurnolL2 actualValue (Price.scalarLift (Gamma.nativeGamma c c)) :=
  (trace_value root visit u7 calculus c raw).trans (OriginalBoundaryGammaProgram.code_actual c zero raw actual)
include root visit u7 calculus c raw in
theorem gamma_read (zero:riemannZeta c.value=0) (actual:burnolEvenAmbientProjection raw=burnolZeroPairedFixedAnnulusBoundary c zero OriginalKPairedBEulerJunctionSource.junctionShift) :
    Price.scalarRead actualValue=Gamma.nativeGamma c c :=
  (congrArg Price.scalarRead (output root visit u7 calculus c raw zero actual)).trans (Price.scalar_lift _)
include root visit u7 calculus c raw in
theorem recovered_actual (zero:riemannZeta c.value=0) (actual:burnolEvenAmbientProjection raw=burnolZeroPairedFixedAnnulusBoundary c zero OriginalKPairedBEulerJunctionSource.junctionShift) :
    (recoveredReceipt root visit u7 calculus c raw).value=(burnolCompletedMellinRieszVector c:BurnolL2) :=
  (recovered_read root visit u7 calculus c raw).trans (OriginalBoundaryGammaProgram.recovered_actual c zero raw actual)
include root visit u7 calculus c raw in
theorem paired_actual (zero:riemannZeta c.value=0) (actual:burnolEvenAmbientProjection raw=burnolZeroPairedFixedAnnulusBoundary c zero OriginalKPairedBEulerJunctionSource.junctionShift) :
    (pairedReceipt root visit u7 calculus c raw).value=OriginalKPairedBEulerJunctionSource.sourceAction c :=
  (paired_read root visit u7 calculus c raw).trans (OriginalBoundaryGammaProgram.paired_actual c zero raw actual)
include root visit u7 calculus c raw in
theorem b2_actual (zero:riemannZeta c.value=0) (actual:burnolEvenAmbientProjection raw=burnolZeroPairedFixedAnnulusBoundary c zero OriginalKPairedBEulerJunctionSource.junctionShift) :
    (b2Receipt root visit u7 calculus c raw).value=burnolQuarterZeroExtension
      (OriginalKPairedBEulerJunctionSource.sourceSecond c:BurnolQuarterIntervalL2) :=
  (b2_read root visit u7 calculus c raw).trans (OriginalBoundaryGammaProgram.b2_actual c zero raw actual)
include root visit u7 calculus c raw in
theorem physical_actual (zero:riemannZeta c.value=0) (actual:burnolEvenAmbientProjection raw=burnolZeroPairedFixedAnnulusBoundary c zero OriginalKPairedBEulerJunctionSource.junctionShift) :
    (physicalReceipt root visit u7 calculus c raw).value=(burnolZeroPairedFixedAnnulusBoundary c zero OriginalKPairedBEulerJunctionSource.junctionShift:BurnolL2) :=
  (physical_read root visit u7 calculus c raw).trans (congrArg (fun value:BurnolPaAmbientCarrier=>(value:BurnolL2)) actual)
include root visit u7 calculus c raw in
theorem inverse_equation : OriginalBoundaryGammaResolvent.boundaryOperator c
    (burnolEvenAmbientProjection (recoveredReceipt root visit u7 calculus c raw).value)=
      burnolEvenAmbientProjection (physicalReceipt root visit u7 calculus c raw).value :=
  (congrArg (fun value:BurnolL2=>OriginalBoundaryGammaResolvent.boundaryOperator c
      (burnolEvenAmbientProjection value)) (recovered_read root visit u7 calculus c raw)).trans
    ((inverse_fibre c raw).trans (congrArg burnolEvenAmbientProjection
      (physical_read root visit u7 calculus c raw)).symm)
include root visit u7 calculus c raw in
theorem B0_read : burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
    (burnolEvenAmbientProjection (physicalReceipt root visit u7 calculus c raw).value)=
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius (burnolEvenAmbientProjection raw) := by
  have fixed : burnolEvenAmbientProjection (P.physical raw)=burnolEvenAmbientProjection raw :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  exact (congrArg (fun value:BurnolL2=>burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
    (burnolEvenAmbientProjection value)) (physical_read root visit u7 calculus c raw)).trans
    (congrArg (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius) fixed)
include root visit u7 calculus c raw in
theorem first_full_block :
    ((burnolAmbientMeanZeroFirstCorrection (pairedReceipt root visit u7 calculus c raw).value+burnolMeanZeroTruncatedFourier
      (Price.read (b2Receipt root visit u7 calculus c raw).value):BurnolQuarterMeanZeroCarrier):BurnolQuarterIntervalL2)+
      OriginalPairedSecondBProgram.positionMean (pairedReceipt root visit u7 calculus c raw).value • intervalConstant (1/4:ℝ)=OriginalPairedSecondBProgram.positionInput (pairedReceipt root visit u7 calculus c raw).value :=
  (congrArg (fun value:BurnolL2=>((burnolAmbientMeanZeroFirstCorrection (pairedReceipt root visit u7 calculus c raw).value+burnolMeanZeroTruncatedFourier
      (Price.read value):BurnolQuarterMeanZeroCarrier):BurnolQuarterIntervalL2)+
        OriginalPairedSecondBProgram.positionMean (pairedReceipt root visit u7 calculus c raw).value • intervalConstant (1/4:ℝ))
    (b2_from_paired root visit u7 calculus c raw)).trans (OriginalPairedSecondBProgram.first_full_block (pairedReceipt root visit u7 calculus c raw).value)
include root visit u7 calculus c raw in
theorem second_full_block :
    ((burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection (pairedReceipt root visit u7 calculus c raw).value)+
      Price.read (b2Receipt root visit u7 calculus c raw).value:BurnolQuarterMeanZeroCarrier):BurnolQuarterIntervalL2)+
      OriginalPairedSecondBProgram.fourierMean (pairedReceipt root visit u7 calculus c raw).value • intervalConstant (1/4:ℝ)=OriginalPairedSecondBProgram.fourierInput (pairedReceipt root visit u7 calculus c raw).value :=
  (congrArg (fun value:BurnolL2=>((burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection (pairedReceipt root visit u7 calculus c raw).value)+
      Price.read value:BurnolQuarterMeanZeroCarrier):BurnolQuarterIntervalL2)+
        OriginalPairedSecondBProgram.fourierMean (pairedReceipt root visit u7 calculus c raw).value • intervalConstant (1/4:ℝ))
    (b2_from_paired root visit u7 calculus c raw)).trans (OriginalPairedSecondBProgram.second_full_block (pairedReceipt root visit u7 calculus c raw).value)
end EndRead
attribute [local irreducible] OriginalBoundaryGammaSource.Generated.result
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ) (N:Nat)
local notation "src"=>OriginalBoundaryGammaAction.sourceRoot observation nontrivial half depth ordinal t N
local notation "here"=>OriginalBoundaryGammaAction.sourceVisit observation nontrivial half depth ordinal t N
local notation "u7"=>OriginalBoundaryGammaAction.sourceU7 observation nontrivial half depth ordinal t N
local notation "calculus"=>OriginalBoundaryGammaAction.sourceCalculus observation nontrivial half depth ordinal t N
local notation "reader"=>OriginalBoundaryGammaAction.sourceReader observation nontrivial half depth ordinal t N
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "raw"=>OriginalBoundaryGammaOrigin.rawValue observation nontrivial half depth ordinal t N
private noncomputable abbrev sourceZero : riemannZeta (c).value=0 := observation.mathlibZero
noncomputable def nextFace := Adapter.targetFace (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextState : SourceOperationExecutionDebt.State (P.environment raw) (P.code c) :=
  Adapter.state (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextValue : BurnolL2 := Adapter.terminalValue (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextTrace : Trace (P.environment raw) (P.code c) (.const (nextValue observation nontrivial half depth ordinal t N)) :=
  EndRead.actualTrace src here u7 calculus c raw
noncomputable def rawReceipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) (.var (0:Fin 2)) :=
  EndRead.rawReceipt src here u7 calculus c raw
noncomputable def physicalReceipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) P.physicalCode :=
  EndRead.physicalReceipt src here u7 calculus c raw
noncomputable def recoveredReceipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) (P.recoveredCode c) :=
  EndRead.recoveredReceipt src here u7 calculus c raw
noncomputable def pairedReceipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) (P.pairedCode c) :=
  EndRead.pairedReceipt src here u7 calculus c raw
noncomputable def b2Receipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) (P.b2Code c) :=
  EndRead.b2Receipt src here u7 calculus c raw
noncomputable abbrev next_state_source := state_source (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable abbrev next_trace_source := trace_source (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable abbrev next_paid := EndRead.paid_all src here u7 calculus c raw
noncomputable abbrev next_value_source := EndRead.result_value src here u7 calculus c raw
noncomputable abbrev actual_raw_read := EndRead.raw_read src here u7 calculus c raw
noncomputable abbrev actual_physical_read := EndRead.physical_read src here u7 calculus c raw
noncomputable abbrev actual_recovered_read := EndRead.recovered_read src here u7 calculus c raw
noncomputable abbrev actual_paired_read := EndRead.paired_read src here u7 calculus c raw
noncomputable abbrev actual_b2_read := EndRead.b2_read src here u7 calculus c raw
noncomputable abbrev actual_b2_from_paired := EndRead.b2_from_paired src here u7 calculus c raw
noncomputable abbrev actual_source_equation := EndRead.source_equation src here u7 calculus c raw
noncomputable abbrev actual_inverse_equation := EndRead.inverse_equation src here u7 calculus c raw
noncomputable abbrev actual_B0_read := EndRead.B0_read src here u7 calculus c raw
noncomputable abbrev actual_first_full_block := EndRead.first_full_block src here u7 calculus c raw
noncomputable abbrev actual_second_full_block := EndRead.second_full_block src here u7 calculus c raw
noncomputable abbrev actual_output := EndRead.output src here u7 calculus c raw
  (sourceZero observation nontrivial half)
  (OriginalBoundaryGammaOrigin.projected_actual observation nontrivial half depth ordinal t N (sourceZero observation nontrivial half))
noncomputable abbrev actual_Gamma := EndRead.gamma_read src here u7 calculus c raw
  (sourceZero observation nontrivial half)
  (OriginalBoundaryGammaOrigin.projected_actual observation nontrivial half depth ordinal t N (sourceZero observation nontrivial half))
noncomputable abbrev actual_physical := EndRead.physical_actual src here u7 calculus c raw
  (sourceZero observation nontrivial half)
  (OriginalBoundaryGammaOrigin.projected_actual observation nontrivial half depth ordinal t N (sourceZero observation nontrivial half))
noncomputable abbrev actual_recovered := EndRead.recovered_actual src here u7 calculus c raw
  (sourceZero observation nontrivial half)
  (OriginalBoundaryGammaOrigin.projected_actual observation nontrivial half depth ordinal t N (sourceZero observation nontrivial half))
noncomputable abbrev actual_paired := EndRead.paired_actual src here u7 calculus c raw
  (sourceZero observation nontrivial half)
  (OriginalBoundaryGammaOrigin.projected_actual observation nontrivial half depth ordinal t N (sourceZero observation nontrivial half))
noncomputable abbrev actual_b2 := EndRead.b2_actual src here u7 calculus c raw
  (sourceZero observation nontrivial half)
  (OriginalBoundaryGammaOrigin.projected_actual observation nontrivial half depth ordinal t N (sourceZero observation nontrivial half))
noncomputable abbrev sourceParentTrace := OriginalBoundaryGammaOrigin.parentTrace observation nontrivial half depth
noncomputable abbrev sourceRawReceipt := OriginalBoundaryGammaOrigin.rawReceipt observation nontrivial half depth ordinal t N
noncomputable abbrev sourceRawTrace := OriginalBoundaryGammaOrigin.rawTrace observation nontrivial half depth ordinal t N
noncomputable abbrev sourceLeftKernelReceipt := OriginalBoundaryGammaOrigin.leftKernelReceipt observation nontrivial half depth
noncomputable abbrev sourcePlusKernelReceipt := OriginalBoundaryGammaOrigin.plusKernelReceipt observation nontrivial half depth
noncomputable abbrev sourceMinusKernelReceipt := OriginalBoundaryGammaOrigin.minusKernelReceipt observation nontrivial half depth
noncomputable abbrev sourceCursor := OriginalBoundaryGammaOrigin.actualCursor observation nontrivial half depth
noncomputable abbrev sourceIndex := OriginalBoundaryGammaOrigin.actualIndex observation nontrivial half depth
noncomputable abbrev sourceOccurrence := OriginalBoundaryGammaOrigin.actualOccurrence observation nontrivial half depth ordinal
noncomputable abbrev sourceHistory := OriginalBoundaryGammaOrigin.currentHistory observation nontrivial half depth ordinal t N
noncomputable abbrev sourceWord := OriginalBoundaryGammaOrigin.rawWord observation nontrivial half depth ordinal t N
noncomputable abbrev sourceBoundaryB0 := OriginalBoundaryGammaOrigin.boundaryB0 observation nontrivial half depth ordinal t N
noncomputable abbrev sourcePairedReceipt := OriginalBoundaryGammaOrigin.originalPairedReceipt observation nontrivial half depth ordinal t N
noncomputable abbrev source_index_position := OriginalBoundaryGammaOrigin.actual_index_position observation nontrivial half depth
noncomputable abbrev source_raw_address := OriginalBoundaryGammaOrigin.raw_address observation nontrivial half depth
noncomputable abbrev source_word_source := OriginalBoundaryGammaOrigin.raw_word_source observation nontrivial half depth ordinal t N
noncomputable abbrev actual_input_source_lineage :=
  (actual_raw_read observation nontrivial half depth ordinal t N).trans
    (OriginalBoundaryGammaOrigin.raw_receipt_read observation nontrivial half depth ordinal t N).symm
noncomputable abbrev recovered_old_K_value_transport :=
  (actual_recovered observation nontrivial half depth ordinal t N).trans
    (OriginalBoundaryGammaOrigin.left_kernel_actual observation nontrivial half depth).symm
noncomputable abbrev paired_old_value_transport :=
  (actual_paired observation nontrivial half depth ordinal t N).trans
    (OriginalPairedSecondBOrigin.paired_actual observation nontrivial half depth ordinal t N).symm
noncomputable def retainedInputState := (OriginalBoundaryGammaAction.actualInputFace observation nontrivial half depth ordinal t N).rootRead
noncomputable abbrev retained_input_state := OriginalBoundaryGammaAction.target_input_state observation nontrivial half depth ordinal t N
noncomputable abbrev retained_origin_payload := OriginalBoundaryGammaAction.target_source_payload observation nontrivial half depth ordinal t N
end OriginalBoundaryGammaConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env=>Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalBoundaryGammaConsumer"
