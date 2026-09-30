import H0mework.Versions.X.Fock.HistoryConditional.InformationLossRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInformationLoss

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem parity_amount_positive (runtime : LivingRuntimeState process) (enough : 1 ≤ inventoryBound runtime) :
    0 < amount runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll :=
  (amount_positive_iff_gap runtime _ _).mpr (SourceConditionalMergeLoss.parity_gap_positive runtime enough)

theorem parity_budget (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalInventory.cost (inventoryBound runtime) (fun _actor : Actors runtime => ()) /
      (inventoryBound runtime + 1 : ℝ) +
    (Real.exp (2 * (SourceConditionalModel.dynamicInformation runtime depth +
      amount runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll)) - 1) / 12 ≤
      SourceConditionalVector.dynamicError runtime depth (SourceConditionalNativeKeys.decoder runtime depth) +
        SourceConditionalMergeLoss.gap runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll := by
  have paid := recovery_budget runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll
  rw [SourceInformationReadback.model_information] at paid
  have information := SourceInformationReadback.dynamic_information_code runtime depth
  have query : SourceInformationReadback.parityCode runtime = (fun actor : Actors runtime => (actor.val : ZMod 2)) := rfl
  rw [query] at information
  rw [← information] at paid
  simp only [SourceConditionalMergeLoss.fine_field runtime depth, SourceConditionalMergeLoss.forgetAll] at paid
  exact paid


end
end SourceConditionalInformationLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
