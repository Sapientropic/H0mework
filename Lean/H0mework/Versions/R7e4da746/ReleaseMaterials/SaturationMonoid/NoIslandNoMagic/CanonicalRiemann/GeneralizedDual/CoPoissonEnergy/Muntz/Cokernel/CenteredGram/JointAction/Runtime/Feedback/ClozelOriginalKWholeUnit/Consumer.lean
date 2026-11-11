import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholeUnit.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeUnitGreen

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxErrors 1
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeUnitConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution MeasureTheory
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
namespace G
export OriginalWholeUnitSource.Generated (reader result)
end G
namespace P
export OriginalWholeUnitProgram (code environment)
end P
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var)
end Prog
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (targetFace state terminalValue)
end Adapter
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value)
end OC
namespace WTrace
export OriginalKElementaryArithmeticAction.WholeTrace (value velocity countedRaw counted_read counted_continuous actual_derivative)
end WTrace
open private normalizedTrace paid expression state_source trace_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private value_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Action
run_cmd IO.eprintln "whole-unit Consumer: generic target begins"
namespace EndRead
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (root:SourceNativeLivingRootClosure W V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7:U7ProducerCalculus W) (calculus:U7ObstructionEvolutionCalculus W u7)
variable (N:ℕ) (kernel alpha beta:BurnolL2)
local notation "reader"=>(fun _=>G.reader root.toAuthoritativeRoot N kernel alpha beta (root.emitted visit.current))
local notation "actualValue"=>Adapter.terminalValue (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader
include root visit u7 calculus N kernel alpha beta in
private theorem terminal_value : @Eq BurnolL2 actualValue (OC.value (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root.toAuthoritativeRoot visit.current reader) := by
  unfold Adapter.terminalValue
  rw [expression (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader]
  rfl
include root visit u7 calculus N kernel alpha beta in
private theorem terminal_expr :
    (.const (OC.value (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root.toAuthoritativeRoot visit.current reader) : OriginalKPaNativePortSourceCalculation.E)=
      .const actualValue :=
  congrArg (fun value:BurnolL2=>(.const value:OriginalKPaNativePortSourceCalculation.E))
    (terminal_value root visit u7 calculus N kernel alpha beta).symm
noncomputable def actualTrace : Trace (P.environment kernel) (P.code N alpha beta) (.const actualValue) :=
  Eq.mp (congrArg (Trace (P.environment kernel) (P.code N alpha beta))
    (terminal_expr root visit u7 calculus N kernel alpha beta))
    (normalizedTrace (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader)
noncomputable def kernelReceipt := OriginalWholeUnitProgram.Traced.kernelReceipt N alpha beta (actualTrace root visit u7 calculus N kernel alpha beta)
noncomputable def alphaReceipt := OriginalWholeUnitProgram.Traced.alphaReceipt N alpha beta (actualTrace root visit u7 calculus N kernel alpha beta)
noncomputable def betaReceipt := OriginalWholeUnitProgram.Traced.betaReceipt N alpha beta (actualTrace root visit u7 calculus N kernel alpha beta)
include root visit u7 calculus N kernel alpha beta in
theorem paid_all : (Adapter.state (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader).2.length=6 :=
  (paid (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) root visit u7 calculus reader).trans (OriginalWholeUnitProgram.code_budget N alpha beta)
include root visit u7 calculus N kernel alpha beta in
theorem result_value : @Eq BurnolL2 actualValue ((G.result root.toAuthoritativeRoot visit.current N kernel alpha beta).2.2.1) :=
  (terminal_value root visit u7 calculus N kernel alpha beta).trans
    (value_source root.toAuthoritativeRoot visit.current (G.reader root.toAuthoritativeRoot N kernel alpha beta))
include root visit u7 calculus N kernel alpha beta in
theorem kernel_read : (kernelReceipt root visit u7 calculus N kernel alpha beta).value=kernel :=
  OriginalWholeUnitProgram.Traced.kernel_read N alpha beta (actualTrace root visit u7 calculus N kernel alpha beta)
include root visit u7 calculus N kernel alpha beta in
theorem alpha_read : (alphaReceipt root visit u7 calculus N kernel alpha beta).value=alpha :=
  OriginalWholeUnitProgram.Traced.alpha_read N alpha beta (actualTrace root visit u7 calculus N kernel alpha beta)
include root visit u7 calculus N kernel alpha beta in
theorem beta_read : (betaReceipt root visit u7 calculus N kernel alpha beta).value=beta :=
  OriginalWholeUnitProgram.Traced.beta_read N alpha beta (actualTrace root visit u7 calculus N kernel alpha beta)
include root visit u7 calculus N kernel alpha beta in
theorem output (c:BurnolCompletedMellinCoordinate)
    (kernelSource:kernel=(burnolCompletedMellinRieszVector c:BurnolL2))
    (alphaSource:alpha=Kernel.A c • ConstantDual.seed)
    (betaSource:beta=Kernel.beta c • ConstantDual.seed) :
    @Eq BurnolL2 actualValue (WTrace.value c N) :=
  (result_value root visit u7 calculus N kernel alpha beta).trans
    (OriginalWholeUnitSource.Generated.output root.toAuthoritativeRoot visit.current N kernel alpha beta c
      kernelSource alphaSource betaSource)
end EndRead
run_cmd IO.eprintln "whole-unit Consumer: generic target complete"

namespace ContinuousFace
variable (c:BurnolCompletedMellinCoordinate) (N:ℕ) (actual:BurnolL2)
variable (source:actual=WTrace.value c N)
include source
theorem raw_read : (actual:ℝ→ℂ)=ᵐ[volume] WTrace.countedRaw c N := source.symm ▸ WTrace.counted_read c N
theorem derivative : HasDerivAt (fun h:ℝ=>burnolMultiplicativeDilation h actual) (WTrace.velocity c N) 0 :=
  source.symm ▸ WTrace.actual_derivative c N

theorem stock_green (h:ℝ) :
    inner ℂ (WTrace.velocity c N) (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h
      (Kernel.A c • DualSource.source N ConstantDual.seed-
        Kernel.beta c • burnolTateReciprocalL2 (DualSource.source N ConstantDual.seed)))-
    (1/2:ℂ)*inner ℂ actual (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h
      (Kernel.A c • DualSource.source N ConstantDual.seed+
        Kernel.beta c • burnolTateReciprocalL2 (DualSource.source N ConstantDual.seed)))=
    Kernel.A c*OriginalKElementaryArithmeticAction.WholeUnitGreen.boundaryEdge c h (WTrace.countedRaw c N) N+
      Kernel.beta c*OriginalKElementaryArithmeticAction.WholeUnitGreen.boundaryEdge c h
        (burnolTateReciprocalRaw (WTrace.countedRaw c N)) N :=
  source.symm ▸ OriginalKElementaryArithmeticAction.WholeUnitGreen.actual_stock_green c N h

end ContinuousFace
run_cmd IO.eprintln "whole-unit Consumer: continuous/graph/stock faces complete"

attribute [local irreducible] OriginalWholeUnitSource.Generated.result
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ) (N:ℕ)
local notation "src"=>OriginalWholeUnitAction.sourceRoot observation nontrivial half depth ordinal t
local notation "here"=>OriginalWholeUnitAction.sourceVisit observation nontrivial half depth ordinal t
local notation "u7"=>OriginalWholeUnitAction.sourceU7 observation nontrivial half depth ordinal t
local notation "calculus"=>OriginalWholeUnitAction.sourceCalculus observation nontrivial half depth ordinal t
local notation "reader"=>OriginalWholeUnitAction.sourceReader observation nontrivial half depth ordinal t N
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "kernel"=>OriginalWholeUnitInput.kernelValue observation nontrivial half depth ordinal t
local notation "alpha"=>OriginalWholeUnitInput.alphaLift observation nontrivial half depth ordinal t
local notation "beta"=>OriginalWholeUnitInput.betaLift observation nontrivial half depth ordinal t
run_cmd IO.eprintln "whole-unit Consumer: actual target begins"
noncomputable def nextFace := Adapter.targetFace (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextState : SourceOperationExecutionDebt.State (P.environment kernel) (P.code N alpha beta) :=
  Adapter.state (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextValue : BurnolL2 := Adapter.terminalValue (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable def nextTrace : Trace (P.environment kernel) (P.code N alpha beta)
    (.const (nextValue observation nontrivial half depth ordinal t N)) :=
  EndRead.actualTrace src here u7 calculus N kernel alpha beta
noncomputable def kernelReceipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) (.var (0:Fin 2)) :=
  EndRead.kernelReceipt src here u7 calculus N kernel alpha beta
noncomputable def alphaReceipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) (.const alpha) :=
  EndRead.alphaReceipt src here u7 calculus N kernel alpha beta
noncomputable def betaReceipt : Trace.SourceReceipt (nextTrace observation nontrivial half depth ordinal t N) (.const beta) :=
  EndRead.betaReceipt src here u7 calculus N kernel alpha beta
noncomputable abbrev next_state_source :=
  state_source (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable abbrev next_trace_source :=
  trace_source (Value:=Prog.Value) (Var:=Prog.Var) (sort:=()) src here u7 calculus reader
noncomputable abbrev next_paid :=
  EndRead.paid_all src here u7 calculus N kernel alpha beta
noncomputable abbrev next_value_source :=
  EndRead.result_value src here u7 calculus N kernel alpha beta
noncomputable abbrev actual_kernel_read :=
  EndRead.kernel_read src here u7 calculus N kernel alpha beta
noncomputable abbrev actual_alpha_read :=
  EndRead.alpha_read src here u7 calculus N kernel alpha beta
noncomputable abbrev actual_beta_read :=
  EndRead.beta_read src here u7 calculus N kernel alpha beta
noncomputable abbrev actual_output := EndRead.output src here u7 calculus N kernel alpha beta c
  (OriginalWholeUnitInput.kernel_actual observation nontrivial half depth ordinal t)
  (OriginalWholeUnitInput.alpha_actual observation nontrivial half depth ordinal t)
  (OriginalWholeUnitInput.beta_actual observation nontrivial half depth ordinal t)
noncomputable abbrev actual_raw_read :=
  ContinuousFace.raw_read c N _ (actual_output observation nontrivial half depth ordinal t N)
noncomputable abbrev actual_raw_continuous :=
  WTrace.counted_continuous c N
noncomputable abbrev actual_derivative :=
  ContinuousFace.derivative c N _ (actual_output observation nontrivial half depth ordinal t N)
noncomputable abbrev actual_stock_green (h:ℝ) :=
  ContinuousFace.stock_green c N _ (actual_output observation nontrivial half depth ordinal t N) h
noncomputable def retainedInputState := (OriginalWholeUnitAction.actualInputFace observation nontrivial half depth ordinal t N).rootRead
noncomputable abbrev retained_input_state :=
  OriginalWholeUnitAction.target_input_state observation nontrivial half depth ordinal t N
noncomputable abbrev retained_price_state :=
  OriginalWholeUnitAction.target_price_state observation nontrivial half depth ordinal t N
noncomputable abbrev retained_contact_state :=
  OriginalWholeUnitAction.target_contact_state observation nontrivial half depth ordinal t N
noncomputable abbrev retained_adjoint_state :=
  OriginalWholeUnitAction.target_adjoint_state observation nontrivial half depth ordinal t N
run_cmd IO.eprintln "whole-unit Consumer: actual target complete"
end OriginalWholeUnitConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeUnitConsumer"
