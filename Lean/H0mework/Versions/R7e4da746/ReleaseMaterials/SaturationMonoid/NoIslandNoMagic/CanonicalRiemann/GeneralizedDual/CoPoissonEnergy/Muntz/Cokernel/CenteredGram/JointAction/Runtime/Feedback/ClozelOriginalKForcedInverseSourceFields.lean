import H0mework.Realization.Operations.Execution.LinearInput
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReturnJordanSourceWriteback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcedInverseSourceOccurrences

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKForcedInverseSourceCalculation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKForcedInverseSourceWriteback
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
  (receipt forcedSourceBinding forcedSourceCode forcedInputCode forcedResponseCode forcedForcingCode
   forcedGammaFieldCode forcedEffectCode forcedSourceTrace forced_source_preserved)
end C
namespace Prog
export OriginalKCombReceiptFeedback (Value Var)
end Prog
namespace JP
export OriginalKForcedInverseSourceCalculation
  (code inputCode responseCode forcingCode gammaFieldCode effectCode sourceEnvironment sourceCoupling)
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
local notation "raw" => C.forcedSourceCode observation nontrivial depth half
local notation "trace" => C.forcedSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)
private abbrev emittedAt := (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence
private abbrev environmentAt :=
  (runtimeForcedInverseCalculationResultAt observation nontrivial depth half).1.environment
local notation "occurrence" => emittedAt observation nontrivial depth
local notation "nativeEnv" => environmentAt observation nontrivial half depth
open private addInputs from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKWholeDebtRCalculationFace

theorem bound_code_value (environment : Env Prog.Value Prog.Var) :
    (raw).eval environment = (JP.code c).eval nativeEnv := by
  unfold C.forcedSourceCode
  rw [Expr.eval_subst]
  rfl

def actualValue : BurnolL2 := (raw).eval (C.receipt observation nontrivial depth half).1.environment

theorem actual_value_runtime : actualValue observation nontrivial half depth =
    (runtimeForcedInverseCalculationResultAt observation nontrivial depth half).2.2.1 := by
  rw [actualValue,bound_code_value,runtimeForcedInverseCalculationResultAt_source]
  exact (OriginalKWholeDebtRCalculationFace.forced_result_value observation nontrivial half occurrence).symm

theorem native_environment_source : nativeEnv = JP.sourceEnvironment c
    (OriginalKWholeDebtRCalculationFace.jointRPaInput observation nontrivial half occurrence).1
    (OriginalKWholeDebtRCalculationFace.jointRUnitInput observation nontrivial half occurrence).1 := by
  have sourceRaw := congrArg Prod.fst
    (runtimeForcedInverseCalculationResultAt_source observation nontrivial depth half)
  exact congrArg (fun source : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := OriginalKForcedInverseSourceCalculation.Value)
    (Var := OriginalKForcedInverseSourceCalculation.Var) (sort := ()) => source.environment) sourceRaw

theorem actual_original_pa : nativeEnv () (0,11)=OriginalWholeDebtRJointMobiusSource.paWave c := by
  rw [native_environment_source]
  exact OriginalKWholeDebtRCalculationFace.joint_r_pa_input_value observation nontrivial half occurrence

theorem actual_original_unit : nativeEnv () (0,12)=burnolUnitTailResponse c 4 := by
  rw [native_environment_source]
  exact OriginalKWholeDebtRCalculationFace.joint_r_unit_input_value observation nontrivial half occurrence

def actualInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (C.forcedInputCode observation nontrivial depth half) (.const point) ×
      PLift (burnolDirectRightResolventCLM c point = actualValue observation nontrivial half depth) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
        (C.forcedInputCode observation nontrivial depth half))
      (.const (actualValue observation nontrivial half depth)) := trace
  exact SourceOperationExecution.originalInput executed

def actualResponseInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (C.forcedResponseCode observation nontrivial depth half) (.const point) ×
      PLift (fourierL2 point=(actualInput observation nontrivial half depth).1) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap.toAddMonoidHom
        (C.forcedResponseCode observation nontrivial depth half))
      (.const (actualInput observation nontrivial half depth).1) :=
    (actualInput observation nontrivial half depth).2.1
  exact SourceOperationExecution.originalInput executed

theorem actual_response_value : (actualResponseInput observation nontrivial half depth).1 =
    OriginalWholeDebtRJointMobiusForcedInverseSource.forcingResponse c := by
  have value := (actualResponseInput observation nontrivial half depth).2.1.sound.symm
  change (actualResponseInput observation nontrivial half depth).1 =
    (C.forcedResponseCode observation nontrivial depth half).eval
      (C.receipt observation nontrivial depth half).1.environment at value
  unfold C.forcedResponseCode at value
  rw [Expr.eval_subst] at value
  change (actualResponseInput observation nontrivial half depth).1 =
    (JP.responseCode c).eval nativeEnv at value
  rw [native_environment_source] at value
  exact value.trans (OriginalKForcedInverseSourceCalculation.actual_response_code c _ _
    (OriginalKWholeDebtRCalculationFace.joint_r_pa_input_value observation nontrivial half occurrence)
    (OriginalKWholeDebtRCalculationFace.joint_r_unit_input_value observation nontrivial half occurrence))

theorem actual_input_value : (actualInput observation nontrivial half depth).1 =
    OriginalWholeDebtRJointMobiusForcedInverseSource.forcingInput c := by
  rw [← (actualResponseInput observation nontrivial half depth).2.2.down,actual_response_value]
  rfl

theorem actual_value_generated : actualValue observation nontrivial half depth =
    OriginalWholeDebtRJointMobiusForcedInverseSource.forcingNext c := by
  rw [← (actualInput observation nontrivial half depth).2.2.down,actual_input_value]
  rfl

/-- The two forcing inputs are restrictions of the single inverse-source execution. -/
def actualInverseInput := SourceOperationExecution.originalInput
  (actualResponseInput observation nontrivial half depth).2.1
private def forcingBranches := addInputs (actualInverseInput observation nontrivial half depth).2.1

def actualForcing (side : Fin 2) :
    Σ point : BurnolL2, Trace (C.receipt observation nontrivial depth half).1.environment
      (C.forcedForcingCode observation nontrivial depth half side) (.const point) := by
  refine Fin.cases ?_ (fun rest => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) rest) side
  · let branch := SourceOperationExecution.originalInput
      (forcingBranches observation nontrivial half depth).2.2.2.1
    exact ⟨branch.1,branch.2.1⟩
  · let scaled := SourceOperationExecution.originalInput
      (forcingBranches observation nontrivial half depth).2.2.1
    let branch := SourceOperationExecution.originalInput scaled.2.1
    exact ⟨branch.1,branch.2.1⟩

theorem actual_forcing_value (side : Fin 2) :
    (actualForcing observation nontrivial half depth side).1 =
      OriginalWholeDebtRJointMobiusForcedInverseSource.calculatedForcing
        (OriginalKForcedInverseSourceCalculation.atCoordinate c side) := by
  have value := (actualForcing observation nontrivial half depth side).2.sound.symm
  unfold C.forcedForcingCode at value
  rw [Expr.eval_subst] at value
  change (actualForcing observation nontrivial half depth side).1 =
    (JP.forcingCode c side).eval nativeEnv at value
  rw [native_environment_source] at value
  exact value.trans (OriginalKForcedInverseSourceCalculation.actual_forcing_code c _ _
    (OriginalKWholeDebtRCalculationFace.joint_r_pa_input_value observation nontrivial half occurrence)
    (OriginalKWholeDebtRCalculationFace.joint_r_unit_input_value observation nontrivial half occurrence) side)

private def effectBranch (side : Fin 2) :=
  (addInputs (addInputs (addInputs
    (actualForcing observation nontrivial half depth side).2).2.2.1).2.2.1).2.2.2.1
private def actualEffectSum (side : Fin 2) :=
  SourceOperationExecution.originalInput (effectBranch observation nontrivial half depth side)
private def effectChildren (side : Fin 2) :=
  addInputs (actualEffectSum observation nontrivial half depth side).2.1

def actualGammaInput (side : Fin 2) :
    Σ point : BurnolL2, Trace (C.receipt observation nontrivial depth half).1.environment
      (C.forcedGammaFieldCode observation nontrivial depth half side) (.const point) :=
  ⟨(effectChildren observation nontrivial half depth side).1,
    (effectChildren observation nontrivial half depth side).2.2.1⟩

def actualEffectInput (side : Fin 2) :
    Σ point : BurnolL2, Trace (C.receipt observation nontrivial depth half).1.environment
      (C.forcedEffectCode observation nontrivial depth half side) (.const point) := by
  let branch := SourceOperationExecution.originalInput
    (effectChildren observation nontrivial half depth side).2.2.2.1
  exact ⟨branch.1,branch.2.1⟩

theorem actual_gamma_value (side : Fin 2) :
    (actualGammaInput observation nontrivial half depth side).1 =
      OriginalWholeDebtRJointMobiusContactPsiPriceSource.nativeGamma
        (OriginalKForcedInverseSourceCalculation.atCoordinate c side)
        (OriginalPrimitiveRankBalance.conjugateCoordinate
          (OriginalKForcedInverseSourceCalculation.atCoordinate c side)) •
        fourierL2 (OriginalKSourceResolventReconstruction.generatedK
          (OriginalPrimitiveRankBalance.conjugateCoordinate
            (OriginalKForcedInverseSourceCalculation.atCoordinate c side))) := by
  have value := (actualGammaInput observation nontrivial half depth side).2.sound.symm
  unfold C.forcedGammaFieldCode at value
  rw [Expr.eval_subst] at value
  change (actualGammaInput observation nontrivial half depth side).1 =
    (JP.gammaFieldCode c side).eval nativeEnv at value
  rw [native_environment_source] at value
  exact value.trans (OriginalKForcedInverseSourceCalculation.actual_gamma_field_code c _ _ side)

theorem actual_effect_value (side : Fin 2) :
    (actualEffectInput observation nontrivial half depth side).1 =
      OriginalWholeDebtRAdjointContactSource.sourceEffect
        (OriginalKForcedInverseSourceCalculation.atCoordinate c side)
        (OriginalPrimitiveRankBalance.conjugateCoordinate
          (OriginalKForcedInverseSourceCalculation.atCoordinate c side)) := by
  have value := (actualEffectInput observation nontrivial half depth side).2.sound.symm
  unfold C.forcedEffectCode at value
  rw [Expr.eval_subst] at value
  change (actualEffectInput observation nontrivial half depth side).1 =
    (JP.effectCode c side).eval nativeEnv at value
  rw [native_environment_source] at value
  exact value.trans (OriginalKForcedInverseSourceCalculation.actual_effect_code c _ _ side)

def boundary : Formal ℤ Prog.Value Prog.Var () :=
  relationMap (R := ℤ) (C.receipt observation nontrivial depth half).1.environment (trace).relationWords

theorem actual_boundary : boundary observation nontrivial half depth =
    Finsupp.single raw (1 : ℤ)-Finsupp.single (.const (actualValue observation nontrivial half depth)) 1 :=
  (trace).relation_boundary (R := ℤ)

end OriginalKForcedInverseSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKForcedInverseSourceWriteback"
