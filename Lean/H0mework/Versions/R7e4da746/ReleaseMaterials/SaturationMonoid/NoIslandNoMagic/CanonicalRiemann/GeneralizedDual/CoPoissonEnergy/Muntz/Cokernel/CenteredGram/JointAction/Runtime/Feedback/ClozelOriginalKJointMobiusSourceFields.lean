import H0mework.Realization.Operations.Execution.LinearInput
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPrimitiveMobiusSourceWriteback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJointMobiusSourceOccurrences

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusRSourceCalculation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKJointMobiusSourceWriteback
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
  (receipt wholeDebtRJointMobiusSourceBinding wholeDebtRJointMobiusSourceInputCode wholeDebtRJointMobiusRInputCode wholeDebtRJointMobiusRResponseCode wholeDebtRJointMobiusSourceCode
   wholeDebtRJointMobiusSourceTrace whole_debt_R_joint_mobius_source_preserved)
end C
namespace Prog
export OriginalKJointMobiusSourceCalculation (Value Var sourceCode fixedShift sourceEnvironment)
abbrev code := OriginalKWholeDebtRCalculationFace.jointCode
end Prog
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
local notation "raw" => C.wholeDebtRJointMobiusSourceCode observation nontrivial depth half
local notation "trace" => C.wholeDebtRJointMobiusSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)

theorem bound_code_value (field : Fin 2) (environment : Env Prog.Value Prog.Var) :
    (raw field).eval environment = (Prog.code c field).eval Prog.sourceEnvironment := by
  unfold C.wholeDebtRJointMobiusSourceCode
  rw [Expr.eval_subst]
  have bindingSource : (fun sort name =>
      ((C.wholeDebtRJointMobiusSourceBinding observation nontrivial depth half field) sort name).eval
        environment) = Prog.sourceEnvironment := by
    funext sort name
    change (runtimeJointMobiusFieldCalculationResultAt observation nontrivial depth half field).1.environment
      sort name = _
    rw [runtimeJointMobiusFieldCalculationResultAt_source]
    rfl
  rw [bindingSource]
  rfl

def actualValue (field : Fin 2) : BurnolL2 :=
  (raw field).eval (C.receipt observation nontrivial depth half).1.environment

theorem actual_value_runtime (field : Fin 2) : actualValue observation nontrivial half depth field =
    (runtimeJointMobiusFieldCalculationResultAt observation nontrivial depth half field).2.2.1 := by
  rw [actualValue, bound_code_value, runtimeJointMobiusFieldCalculationResultAt_source]
  exact (OriginalKWholeDebtRCalculationFace.joint_result_value observation nontrivial half field
    (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence).symm

def sourceValue : BurnolL2 :=
  (C.wholeDebtRJointMobiusSourceInputCode observation nontrivial depth half).eval
    (C.receipt observation nontrivial depth half).1.environment

def actualSourceInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (C.wholeDebtRJointMobiusSourceInputCode observation nontrivial depth half) (.const point) ×
      PLift ((burnolMobiusSourceL2.comp burnolEvenAmbientProjection).toLinearMap.toAddMonoidHom point =
        actualValue observation nontrivial half depth 0) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear (burnolMobiusSourceL2.comp burnolEvenAmbientProjection).toLinearMap.toAddMonoidHom
        (C.wholeDebtRJointMobiusSourceInputCode observation nontrivial depth half))
      (.const (actualValue observation nontrivial half depth 0)) := trace 0
  exact SourceOperationExecution.originalInput executed

theorem actual_source_input_value :
    (actualSourceInput observation nontrivial half depth).1 =
      sourceValue observation nontrivial half depth :=
  (actualSourceInput observation nontrivial half depth).2.1.sound.symm

theorem source_value_evaluated : sourceValue observation nontrivial half depth =
    (Prog.sourceCode c).eval Prog.sourceEnvironment := by
  unfold sourceValue C.wholeDebtRJointMobiusSourceInputCode
  rw [Expr.eval_subst]
  have bindingSource : (fun sort name =>
      ((C.wholeDebtRJointMobiusSourceBinding observation nontrivial depth half 0) sort name).eval
        (C.receipt observation nontrivial depth half).1.environment) = Prog.sourceEnvironment := by
    funext sort name
    change (runtimeJointMobiusCalculationResultAt observation nontrivial depth half).1.environment
      sort name = _
    rw [runtimeJointMobiusCalculationResultAt_source]
    rfl
  rw [bindingSource]
  rfl

theorem source_value_generated : sourceValue observation nontrivial half depth =
    OriginalKSourceFiniteUpdate.OriginalBFiniteRAction.calculatedSourceNormal c Prog.fixedShift :=
  (source_value_evaluated observation nontrivial half depth).trans
    (OriginalKJointMobiusSourceCalculation.actual_source_code c)

theorem source_projection_joint :
    burnolEvenAmbientProjection (sourceValue observation nontrivial half depth) =
      OriginalWholeDebtRJointMobiusSource.jointValue c := by
  rw [source_value_evaluated]
  rfl

theorem source_input_effect :
    burnolMobiusSourceL2 (burnolEvenAmbientProjection
      (sourceValue observation nontrivial half depth)) = actualValue observation nontrivial half depth 0 := by
  rw [← actual_source_input_value]
  exact (actualSourceInput observation nontrivial half depth).2.2.down

def actualRInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (C.wholeDebtRJointMobiusRInputCode observation nontrivial depth half) (.const point) ×
      PLift (burnolDirectRightResolventCLM c point =
        actualValue observation nontrivial half depth 1) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
        (C.wholeDebtRJointMobiusRInputCode observation nontrivial depth half))
      (.const (actualValue observation nontrivial half depth 1)) := trace 1
  exact SourceOperationExecution.originalInput executed

def actualRResponseInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (C.wholeDebtRJointMobiusRResponseCode observation nontrivial depth half) (.const point) ×
      PLift (fourierL2 point = (actualRInput observation nontrivial half depth).1) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap.toAddMonoidHom
        (C.wholeDebtRJointMobiusRResponseCode observation nontrivial depth half))
      (.const (actualRInput observation nontrivial half depth).1) :=
    (actualRInput observation nontrivial half depth).2.1
  exact SourceOperationExecution.originalInput executed

theorem actual_R_response_value :
    (actualRResponseInput observation nontrivial half depth).1 =
      OriginalWholeDebtRJointMobiusUnitSource.response c := by
  have value := (actualRResponseInput observation nontrivial half depth).2.1.sound.symm
  change (actualRResponseInput observation nontrivial half depth).1 =
    (C.wholeDebtRJointMobiusRResponseCode observation nontrivial depth half).eval
      (C.receipt observation nontrivial depth half).1.environment at value
  unfold C.wholeDebtRJointMobiusRResponseCode at value
  rw [Expr.eval_subst] at value
  have bindingSource : (fun sort name =>
      ((C.wholeDebtRJointMobiusSourceBinding observation nontrivial depth half 1) sort name).eval
        (C.receipt observation nontrivial depth half).1.environment) = Prog.sourceEnvironment := by
    funext sort name
    change (runtimeJointMobiusRCalculationResultAt observation nontrivial depth half).1.environment
      sort name = _
    rw [runtimeJointMobiusRCalculationResultAt_source]
    rfl
  rw [bindingSource] at value
  exact value.trans (OriginalKJointMobiusRSourceCalculation.actual_response_code c)

theorem actual_R_input_value :
    (actualRInput observation nontrivial half depth).1 =
      fourierL2 (OriginalWholeDebtRJointMobiusUnitSource.response c) := by
  have value := (actualRInput observation nontrivial half depth).2.1.sound.symm
  change (actualRInput observation nontrivial half depth).1 =
    (C.wholeDebtRJointMobiusRInputCode observation nontrivial depth half).eval
      (C.receipt observation nontrivial depth half).1.environment at value
  unfold C.wholeDebtRJointMobiusRInputCode at value
  rw [Expr.eval_subst] at value
  have bindingSource : (fun sort name =>
      ((C.wholeDebtRJointMobiusSourceBinding observation nontrivial depth half 1) sort name).eval
        (C.receipt observation nontrivial depth half).1.environment) = Prog.sourceEnvironment := by
    funext sort name
    change (runtimeJointMobiusRCalculationResultAt observation nontrivial depth half).1.environment
      sort name = _
    rw [runtimeJointMobiusRCalculationResultAt_source]
    rfl
  rw [bindingSource] at value
  exact value.trans (OriginalKJointMobiusRSourceCalculation.actual_input_code c)

def boundary (field : Fin 2) : Formal ℤ Prog.Value Prog.Var () :=
  relationMap (R := ℤ) (C.receipt observation nontrivial depth half).1.environment (trace field).relationWords

theorem actual_boundary (field : Fin 2) : boundary observation nontrivial half depth field =
    Finsupp.single (raw field) (1 : ℤ)-
      Finsupp.single (.const (actualValue observation nontrivial half depth field)) 1 :=
  (trace field).relation_boundary (R := ℤ)


end OriginalKJointMobiusSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
