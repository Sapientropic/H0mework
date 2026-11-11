import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalStrongAction.Consumer
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalInverseAction
open Complex MeasureTheory Set Filter
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace D
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFirstFullSourceDynamics
  (factory initial firstCfg packet input raw raw_successor next_pair)
end D
namespace P
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction
  (R physicalProjection physicalRemainder)
end P
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalRAction
  (parameter_rightQuarter original_R_direct)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalStrongAction
  (sourceRecover actual_source_recovery)
end Paid

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

theorem original_R_injective : Function.Injective (P.R observation nontrivial half) := by
  intro left right same
  have zero : P.R observation nontrivial half (left - right) = 0 := by
    rw [map_sub, same, sub_self]
  rw [Paid.original_R_direct] at zero
  exact sub_eq_zero.mp (burnolDirectRightResolvent_reflects_zero (observation.coordinate / 2)
    (Paid.parameter_rightQuarter observation half) _ zero)

theorem original_R_ker_bot : (P.R observation nontrivial half).toLinearMap.ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (original_R_injective observation nontrivial half)

def inverse : BurnolL2 →ₗ[ℂ] BurnolL2 := (P.R observation nontrivial half).toLinearMap.leftInverse

theorem inverse_R (value : BurnolL2) : inverse observation nontrivial half (P.R observation nontrivial half value) = value :=
  LinearMap.leftInverse_apply_of_inj (original_R_ker_bot observation nontrivial half) value

variable (depth : Nat)
theorem actual_source_readback (ordinal : Nat) :
    inverse observation nontrivial half (D.raw observation nontrivial half depth (ordinal + 1)) =
      D.raw observation nontrivial half depth ordinal := by
  rw [D.raw_successor, inverse_R]

theorem inverse_matches_strong_read (ordinal : Nat) :
    inverse observation nontrivial half (D.raw observation nontrivial half depth (ordinal + 1)) =
      Paid.sourceRecover observation (D.raw observation nontrivial half depth (ordinal + 1)) :=
  (actual_source_readback observation nontrivial half depth ordinal).trans
    (Paid.actual_source_recovery observation nontrivial half depth ordinal).symm

def pairTotal : (BurnolL2 × BurnolL2) →ₗ[ℂ] BurnolL2 :=
  LinearMap.fst ℂ BurnolL2 BurnolL2 + LinearMap.snd ℂ BurnolL2 BurnolL2

def inversePair : (BurnolL2 × BurnolL2) →ₗ[ℂ] (BurnolL2 × BurnolL2) :=
  ((P.physicalProjection.toLinearMap.comp (inverse observation nontrivial half)).comp pairTotal).prod
    ((P.physicalRemainder.toLinearMap.comp (inverse observation nontrivial half)).comp pairTotal)

theorem inverse_pair_total (value : BurnolL2 × BurnolL2) :
    (inversePair observation nontrivial half value).1 + (inversePair observation nontrivial half value).2 =
      inverse observation nontrivial half (value.1 + value.2) :=
  Submodule.starProjection_add_starProjection_orthogonal _

def actionPair : ((BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) →ₗ[ℂ]
    ((BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) :=
  ((inversePair observation nontrivial half).comp (LinearMap.fst ℂ _ _)).prod
    ((inversePair observation nontrivial half).comp (LinearMap.snd ℂ _ _))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalInverseAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
