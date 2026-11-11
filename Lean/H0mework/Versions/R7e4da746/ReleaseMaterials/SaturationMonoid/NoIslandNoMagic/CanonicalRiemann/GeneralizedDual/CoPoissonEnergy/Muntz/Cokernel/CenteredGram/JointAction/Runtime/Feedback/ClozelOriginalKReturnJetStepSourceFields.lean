import H0mework.Realization.Operations.Execution.LinearInput
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcedInverseSourceWriteback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReturnJetStepSourceOccurrences

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJetStepSourceCalculation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKReturnJetStepSourceWriteback
open Complex BurnolPhysicalState RootInquiryCompletion
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
local instance levelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
  L.groups (PairValue OriginalKCombReceiptFeedback.Value) grade target
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (native oldStock oldEnvironment beforeStock beforeEnvironment sourceFrame sourceBase packetAdmission)
end WN
namespace AR
export SourceInventoryExecutionFeed.AdmissionReceipt (Admission)
end AR
namespace Engine
export ActualNativeRelationTransport.AS (stockScalar)
end Engine
namespace C
export OriginalKCombReceiptFeedback
  (receipt returnJetSourceBinding returnJetSourceCode returnJetStepCode returnJetPrefixCode
   returnJetSourceTrace return_jet_source_preserved)
end C
namespace Prog
export OriginalKCombReceiptFeedback (Value Var)
end Prog
namespace JP
export OriginalKReturnJetStepSourceCalculation (code stepCode prefixCode)
end JP
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (bornWordMap wordMapAt)
end R
namespace Born
export OriginalKBFiniteCalculation.BornInventory
  (packetAt sourceBornHistory actualBornHistory actual_source_relations_in_born)
end Born
namespace NW
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback (admissionWord)
end NW
namespace PT
export SourceOperationPaidRelations (words exposure paid_boundary events_trace complete_steps)
end PT
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
  (request generatedAction nextOriginFace sourceWord nextFullValue
   source_effect source_inverse same_ledger same_visit compiles whole_first canonical_next next_source_occurrences)
end SN
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "raw" => C.returnJetSourceCode observation nontrivial depth half
local notation "trace" => C.returnJetSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)
private abbrev emittedAt := (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence
private abbrev environmentAt (field : Fin 2) :=
  (runtimeReturnJetCalculationResultAt observation nontrivial depth half field).1.environment
local notation "occurrence" => emittedAt observation nontrivial depth
local notation "nativeEnv" => environmentAt observation nontrivial half depth

theorem bound_code_value (field : Fin 2) (environment : Env Prog.Value Prog.Var) :
    (raw field).eval environment = (JP.code c m field).eval (nativeEnv field) := by
  unfold C.returnJetSourceCode
  rw [Expr.eval_subst]
  rfl

def actualValue (field : Fin 2) : BurnolL2 :=
  (raw field).eval (C.receipt observation nontrivial depth half).1.environment

theorem actual_value_runtime (field : Fin 2) : actualValue observation nontrivial half depth field =
    (runtimeReturnJetCalculationResultAt observation nontrivial depth half field).2.2.1 := by
  rw [actualValue, bound_code_value]
  fin_cases field
  · exact (OriginalKWholeDebtRCalculationFace.return_jet_result_value observation nontrivial half 0 occurrence).symm
  · exact (OriginalKWholeDebtRCalculationFace.return_jet_result_value observation nontrivial half 1 occurrence).symm

def borrowedFullJetInput := OriginalKWholeDebtRCalculationFace.returnFullJetInput
  observation nontrivial half occurrence

theorem actual_borrowed_jet : nativeEnv 0 () 0 =
    (borrowedFullJetInput observation nontrivial half depth).1 := rfl

theorem borrowed_jet_value : (borrowedFullJetInput observation nontrivial half depth).1 =
    OriginalWholeDebtRJointMobiusReturnJordanSource.jet observation nontrivial half m := by
  have value := (borrowedFullJetInput observation nontrivial half depth).2.1.sound.symm
  change (borrowedFullJetInput observation nontrivial half depth).1 =
    (OriginalKReturnJordanSourceCalculation.jetCode c m).eval
      (OriginalKWholeDebtRCalculationFace.returnEnvironment observation nontrivial half occurrence) at value
  have response : OriginalKWholeDebtRCalculationFace.returnEnvironment
      observation nontrivial half occurrence () 0 = OriginalWholeDebtRJointMobiusUnitSource.response c :=
    (OriginalKWholeDebtRCalculationFace.jointRResponseInput observation nontrivial half occurrence).2.1.sound.symm.trans
      (OriginalKJointMobiusRSourceCalculation.actual_response_code c)
  have result : OriginalKWholeDebtRCalculationFace.returnEnvironment
      observation nontrivial half occurrence () 1 =
      OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half :=
    (OriginalKWholeDebtRCalculationFace.joint_result_value observation nontrivial half 1 occurrence).trans
      (OriginalKJointMobiusRSourceCalculation.actual_code_field observation nontrivial half)
  exact value.trans (OriginalKReturnJordanSourceCalculation.actual_jet_code observation nontrivial half
    (OriginalKWholeDebtRCalculationFace.returnEnvironment observation nontrivial half occurrence)
    response result m)

def actualPaInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (C.returnJetStepCode observation nontrivial depth half) (.const point) ×
      PLift (OriginalKReturnJordanSourceCalculation.paAction point =
        actualValue observation nontrivial half depth 0) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear OriginalKReturnJordanSourceCalculation.paAction.toLinearMap.toAddMonoidHom
        (C.returnJetStepCode observation nontrivial depth half))
      (.const (actualValue observation nontrivial half depth 0)) := trace 0
  exact SourceOperationExecution.originalInput executed

def actualStepInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        ((Expr.var (0 : Fin 2) : OriginalKReturnJetStepSourceCalculation.E).subst
          (C.returnJetSourceBinding observation nontrivial depth half 0)) (.const point) ×
      PLift ((burnolDirectRightResolventCLM c).adjoint point =
        (actualPaInput observation nontrivial half depth).1) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear (burnolDirectRightResolventCLM c).adjoint.toLinearMap.toAddMonoidHom
        ((Expr.var (0 : Fin 2) : OriginalKReturnJetStepSourceCalculation.E).subst (C.returnJetSourceBinding observation nontrivial depth half 0)))
      (.const (actualPaInput observation nontrivial half depth).1) :=
    (actualPaInput observation nontrivial half depth).2.1
  exact SourceOperationExecution.originalInput executed

theorem actual_step_input_value : (actualStepInput observation nontrivial half depth).1 =
    (borrowedFullJetInput observation nontrivial half depth).1 := by
  exact (actualStepInput observation nontrivial half depth).2.1.sound.symm.trans
    (actual_borrowed_jet observation nontrivial half depth)

theorem actual_pa_input_value : (actualPaInput observation nontrivial half depth).1 =
    OriginalWholeDebtRJointMobiusJetFeedbackSource.nextWhole observation nontrivial half := by
  have value := (actualPaInput observation nontrivial half depth).2.1.sound.symm
  change (actualPaInput observation nontrivial half depth).1 =
    (C.returnJetStepCode observation nontrivial depth half).eval
      (C.receipt observation nontrivial depth half).1.environment at value
  unfold C.returnJetStepCode at value
  rw [Expr.eval_subst] at value
  exact value.trans ((OriginalKReturnJetStepSourceCalculation.actual_step_code observation nontrivial half
    (nativeEnv 0) ((actual_borrowed_jet observation nontrivial half depth).trans
      (borrowed_jet_value observation nontrivial half depth))).trans
    (OriginalWholeDebtRJointMobiusJetFeedbackSource.actual_next_whole observation nontrivial half))

theorem actual_pa_value : actualValue observation nontrivial half depth 0 =
    (OriginalWholeDebtRJointMobiusJetFeedbackSource.nextPa observation nontrivial half : BurnolL2) := by
  rw [actualValue, bound_code_value]
  exact OriginalKReturnJetStepSourceCalculation.actual_pa_code observation nontrivial half (nativeEnv 0)
    ((actual_borrowed_jet observation nontrivial half depth).trans
      (borrowed_jet_value observation nontrivial half depth))

def actualPrefixInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (C.returnJetPrefixCode observation nontrivial depth half) (.const point) ×
      PLift (burnolDirectRightResolventCLM c point = actualValue observation nontrivial half depth 1) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
        (C.returnJetPrefixCode observation nontrivial depth half))
      (.const (actualValue observation nontrivial half depth 1)) := trace 1
  exact SourceOperationExecution.originalInput executed

theorem actual_prefix_pa : nativeEnv 1 () 0 = actualValue observation nontrivial half depth 0 := by
  calc
    _ = (runtimeReturnJetCalculationResultAt observation nontrivial depth half 0).2.2.1 := rfl
    _ = _ := (actual_value_runtime observation nontrivial half depth 0).symm

theorem actual_prefix_value : (actualPrefixInput observation nontrivial half depth).1 =
    CombSource.Division.rawIterate observation half.down m
      (OriginalWholeDebtRJointMobiusJetFeedbackSource.nextPa observation nontrivial half : BurnolL2) := by
  have value := (actualPrefixInput observation nontrivial half depth).2.1.sound.symm
  change (actualPrefixInput observation nontrivial half depth).1 =
    (C.returnJetPrefixCode observation nontrivial depth half).eval
      (C.receipt observation nontrivial depth half).1.environment at value
  unfold C.returnJetPrefixCode at value
  rw [Expr.eval_subst] at value
  exact value.trans (OriginalKReturnJetStepSourceCalculation.actual_prefix_code observation nontrivial half
    (nativeEnv 1) ((actual_prefix_pa observation nontrivial half depth).trans
      (actual_pa_value observation nontrivial half depth)))

theorem actual_next_value : actualValue observation nontrivial half depth 1 =
    CombSource.Division.rawIterate observation half.down (m+1)
      (OriginalWholeDebtRJointMobiusJetFeedbackSource.nextPa observation nontrivial half : BurnolL2) := by
  rw [actualValue, bound_code_value]
  exact OriginalKReturnJetStepSourceCalculation.actual_next_code observation nontrivial half (nativeEnv 1)
    ((actual_prefix_pa observation nontrivial half depth).trans (actual_pa_value observation nontrivial half depth))

def boundary (field : Fin 2) : Formal ℤ Prog.Value Prog.Var () :=
  relationMap (R := ℤ) (C.receipt observation nontrivial depth half).1.environment (trace field).relationWords

theorem actual_boundary (field : Fin 2) : boundary observation nontrivial half depth field =
    Finsupp.single (raw field) (1 : ℤ) -
      Finsupp.single (.const (actualValue observation nontrivial half depth field)) 1 :=
  (trace field).relation_boundary (R := ℤ)

end OriginalKReturnJetStepSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
