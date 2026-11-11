import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteContactPrice.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCompleteFeeConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open scoped InnerProductSpace
namespace A
export OriginalCompleteFeeAction (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader)
end A
namespace S
export OriginalCompleteFeeSource (result actual_output)
end S
namespace G
export OriginalCompleteFeeSource.Generated (reader result)
end G
namespace Input
export OriginalCompleteFeeInput (kernelValue bValue kernel_actual b_actual)
end Input
namespace M
export OriginalConstantFourierPriceMath (scalarLift scalarRead scalar_lift)
end M
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (targetFace state terminalValue)
end Adapter
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value)
end OC
open private state_source trace_source expression normalizedTrace paid from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private value_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Action
namespace EndRead
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (root:SourceNativeLivingRootClosure W V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7:U7ProducerCalculus W) (calculus:U7ObstructionEvolutionCalculus W u7)
variable (c:BurnolCompletedMellinCoordinate) (h:ℝ) (kernel b:BurnolL2)
local notation "reader"=>(fun _=>G.reader root.toAuthoritativeRoot c h kernel b (root.emitted visit.current))
local notation "actualValue"=>Adapter.terminalValue root visit u7 calculus reader
noncomputable def actualTrace := normalizedTrace root visit u7 calculus reader
noncomputable def split := Trace.splitBilinear (actualTrace root visit u7 calculus c h kernel b)
noncomputable def columnValue := (split root visit u7 calculus c h kernel b).leftValue
noncomputable def defectValue := (split root visit u7 calculus c h kernel b).rightValue
noncomputable def columnTrace := (split root visit u7 calculus c h kernel b).leftTrace
noncomputable def defectTrace := (split root visit u7 calculus c h kernel b).rightTrace
noncomputable def defectSplit := Trace.splitAdd (defectTrace root visit u7 calculus c h kernel b)
noncomputable def mobius := Trace.splitLinear (defectSplit root visit u7 calculus c h kernel b).leftTrace
noncomputable def kernelInput := originalInput (mobius root visit u7 calculus c h kernel b).trace
noncomputable def pairSplit := Trace.splitAdd (columnTrace root visit u7 calculus c h kernel b)
noncomputable def sampling := Trace.splitLinear (pairSplit root visit u7 calculus c h kernel b).leftTrace
noncomputable def columnSplit := Trace.splitAdd (sampling root visit u7 calculus c h kernel b).trace
noncomputable def bInput := originalInput (columnSplit root visit u7 calculus c h kernel b).leftTrace
theorem paid_all : (Adapter.state root visit u7 calculus reader).2.length=24 :=
  (paid root visit u7 calculus reader).trans (OriginalCompleteFeeProgram.code_budget c h)
private theorem terminal_value : actualValue=OC.value root.toAuthoritativeRoot visit.current reader := by
  unfold Adapter.terminalValue
  rw [expression root visit u7 calculus reader]
  rfl
theorem result_value : actualValue=(G.result root.toAuthoritativeRoot visit.current c h kernel b).2.2.1 :=
  (terminal_value root visit u7 calculus c h kernel b).trans
    (value_source root.toAuthoritativeRoot visit.current (G.reader root.toAuthoritativeRoot c h kernel b))
theorem kernel_read : (kernelInput root visit u7 calculus c h kernel b).1=kernel :=
  (kernelInput root visit u7 calculus c h kernel b).2.1.sound.symm
theorem b_read : (bInput root visit u7 calculus c h kernel b).1=b :=
  (bInput root visit u7 calculus c h kernel b).2.1.sound.symm
theorem defect_action : defectValue root visit u7 calculus c h kernel b=FiniteMobiusResolventFlux.D kernel :=
  (defectTrace root visit u7 calculus c h kernel b).sound.symm.trans
    (OriginalCompleteFeeProgram.defect_eval (OriginalCompleteFeeProgram.environment kernel b))
theorem column_equation : columnValue root visit u7 calculus c h kernel b=
    (OriginalCompleteFeeProgram.pairedCode c h).eval (OriginalCompleteFeeProgram.environment kernel b) :=
  (columnTrace root visit u7 calculus c h kernel b).sound.symm
theorem pair_action : actualValue=M.scalarLift
    (inner ℂ (columnValue root visit u7 calculus c h kernel b) (defectValue root visit u7 calculus c h kernel b)) :=
  (terminal_value root visit u7 calculus c h kernel b).trans
    (split root visit u7 calculus c h kernel b).interleaving.total_eq
end EndRead

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "src"=>A.sourceRoot observation nontrivial half depth ordinal t
local notation "here"=>A.sourceVisit observation nontrivial half depth ordinal t
local notation "u7"=>A.sourceU7 observation nontrivial half depth ordinal t
local notation "calculus"=>A.sourceCalculus observation nontrivial half depth ordinal t
local notation "reader"=>A.sourceReader observation nontrivial half depth ordinal t
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h"=>OriginalKBFiniteCalculation.fixedShift
local notation "kernel"=>Input.kernelValue observation nontrivial half depth ordinal t
local notation "b"=>Input.bValue observation nontrivial half depth ordinal t
noncomputable def nextFace := Adapter.targetFace src here u7 calculus reader
noncomputable def nextState := Adapter.state src here u7 calculus reader
noncomputable def nextValue := Adapter.terminalValue src here u7 calculus reader
noncomputable def nextTrace := EndRead.actualTrace src here u7 calculus c h kernel b
noncomputable def split := EndRead.split src here u7 calculus c h kernel b
noncomputable def columnValue := EndRead.columnValue src here u7 calculus c h kernel b
noncomputable def defectValue := EndRead.defectValue src here u7 calculus c h kernel b
noncomputable def columnTrace := EndRead.columnTrace src here u7 calculus c h kernel b
noncomputable def defectTrace := EndRead.defectTrace src here u7 calculus c h kernel b
noncomputable def kernelInput := EndRead.kernelInput src here u7 calculus c h kernel b
noncomputable def bInput := EndRead.bInput src here u7 calculus c h kernel b
noncomputable def actualPrice : ℂ := M.scalarRead (nextValue observation nontrivial half depth ordinal t)
theorem next_state_source : type_of% (state_source src here u7 calculus reader) := state_source src here u7 calculus reader
theorem next_trace_source : type_of% (trace_source src here u7 calculus reader) := trace_source src here u7 calculus reader
theorem next_paid : type_of% (EndRead.paid_all src here u7 calculus c h kernel b) := EndRead.paid_all src here u7 calculus c h kernel b
theorem next_value_source : nextValue observation nontrivial half depth ordinal t=
    (S.result observation nontrivial half depth ordinal t).2.2.1 := EndRead.result_value src here u7 calculus c h kernel b
theorem actual_kernel_read : type_of% (EndRead.kernel_read src here u7 calculus c h kernel b) := EndRead.kernel_read src here u7 calculus c h kernel b
theorem actual_b_read : type_of% (EndRead.b_read src here u7 calculus c h kernel b) := EndRead.b_read src here u7 calculus c h kernel b
theorem actual_defect_action : type_of% (EndRead.defect_action src here u7 calculus c h kernel b) := EndRead.defect_action src here u7 calculus c h kernel b
theorem actual_column_equation : type_of% (EndRead.column_equation src here u7 calculus c h kernel b) := EndRead.column_equation src here u7 calculus c h kernel b
theorem actual_pair_action : type_of% (EndRead.pair_action src here u7 calculus c h kernel b) := EndRead.pair_action src here u7 calculus c h kernel b
theorem actual_output : nextValue observation nontrivial half depth ordinal t=
    M.scalarLift (OriginalContactFeedbackSource.completeContactPrice observation nontrivial half h) :=
  (next_value_source observation nontrivial half depth ordinal t).trans (S.actual_output observation nontrivial half depth ordinal t)
theorem actual_price : actualPrice observation nontrivial half depth ordinal t=
    OriginalContactFeedbackSource.completeContactPrice observation nontrivial half h :=
  (congrArg M.scalarRead (actual_output observation nontrivial half depth ordinal t)).trans (M.scalar_lift _)
theorem actual_fixed_residual :
    -burnolPaFixedShiftResidual c
      (by rw [OriginalKCombCofinalTwoDirection.coordinate_value];exact observation.mathlibZero)=
      (pairedMellinTranslationCharacter observation.coordinate h-
        pairedMellinTranslationCharacter (star observation.coordinate) h)*
          OriginalRieszFinitePairing.kernelSelfSource c-
      (1/2:ℂ)*star (OriginalRieszFiniteColumns.firstSourceRead c h (burnolCompletedMellinRieszVector c)+
        OriginalRieszFiniteColumns.firstSourceRead c (-h) (burnolCompletedMellinRieszVector c)+
        actualPrice observation nontrivial half depth ordinal t) :=
  (OriginalContactFeedbackSource.original_fixed_residual_contact_price observation nontrivial half).trans
    (congrArg (fun price=>
      (pairedMellinTranslationCharacter observation.coordinate h-
        pairedMellinTranslationCharacter (star observation.coordinate) h)*
          OriginalRieszFinitePairing.kernelSelfSource c-
      (1/2:ℂ)*star (OriginalRieszFiniteColumns.firstSourceRead c h (burnolCompletedMellinRieszVector c)+
        OriginalRieszFiniteColumns.firstSourceRead c (-h) (burnolCompletedMellinRieszVector c)+price))
      (actual_price observation nontrivial half depth ordinal t).symm)
noncomputable def retainedContactState := (OriginalCompleteFeeAction.actualParentFace observation nontrivial half depth ordinal t).rootRead
theorem retained_contact_state : type_of% (OriginalCompleteFeeAction.target_parent_state observation nontrivial half depth ordinal t) :=
  OriginalCompleteFeeAction.target_parent_state observation nontrivial half depth ordinal t
theorem retained_price_state : type_of% (OriginalCompleteFeeAction.target_input_state observation nontrivial half depth ordinal t) :=
  OriginalCompleteFeeAction.target_input_state observation nontrivial half depth ordinal t
theorem retained_adjoint_state : type_of% (OriginalCompleteFeeAction.target_adjoint_state observation nontrivial half depth ordinal t) :=
  OriginalCompleteFeeAction.target_adjoint_state observation nontrivial half depth ordinal t

end OriginalCompleteFeeConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalCompleteFeeConsumer"
