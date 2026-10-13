import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceBalance.Actual

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceReturn
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
attribute [local instance 1100] NormedSpace.complexToReal
namespace S
export OriginalKSourceBalance
  (contactCorrection correctedField regularSource correctedVelocity corrected_source_strong source_R_ordinary_strong)
end S
namespace Prior
export OriginalKCombCofinalTwoDirection (coordinate coordinate_value originalK originalFourierK)
end Prior
namespace P
export OriginalKCombPhysicalAction (R)
end P

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

-- This source is fixed by the original K field and both paid endpoint channels.
def sourceInput : BurnolL2 :=
  ((star observation.coordinate - observation.coordinate) / 2) •
      S.correctedField (Prior.coordinate observation nontrivial half) -
    (1 / 2 : ℂ) • S.regularSource (Prior.coordinate observation nontrivial half)

def returnedField : BurnolL2 := P.R observation nontrivial half (sourceInput observation nontrivial half)

def sourceDifference : BurnolL2 :=
  returnedField observation nontrivial half - S.correctedField (Prior.coordinate observation nontrivial half)

theorem source_difference_strong :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation shift (sourceDifference observation nontrivial half))
      (-(observation.coordinate - 1 / 2) • sourceDifference observation nontrivial half) 0 := by
  have generated := (S.source_R_ordinary_strong observation nontrivial half
    (sourceInput observation nontrivial half)).sub
    (S.corrected_source_strong (Prior.coordinate observation nontrivial half))
  convert! generated using 1
  · funext shift
    simp only [sourceDifference, returnedField, map_sub, Pi.sub_apply]
  · simp only [sourceDifference, returnedField, sourceInput, S.correctedVelocity, Prior.coordinate_value]
    module

-- The original unitary action identifies the return from its actual source equation.
theorem source_return_corrected_field :
    returnedField observation nontrivial half = S.correctedField (Prior.coordinate observation nontrivial half) := by
  let difference := sourceDifference observation nontrivial half
  have equation := source_difference_strong observation nontrivial half
  have generated := equation.inner ℂ equation
  simp only [burnolMultiplicativeDilation_zero] at generated
  have constant : (fun shift : ℝ => inner ℂ
      (burnolMultiplicativeDilation shift difference) (burnolMultiplicativeDilation shift difference)) =
      fun _ : ℝ => inner ℂ difference difference := by
    funext shift
    exact (burnolMultiplicativeDilation shift).inner_map_map _ _
  change HasDerivAt (fun shift : ℝ => inner ℂ
      (burnolMultiplicativeDilation shift difference) (burnolMultiplicativeDilation shift difference))
    (inner ℂ difference (-(observation.coordinate - 1 / 2) • difference) +
      inner ℂ (-(observation.coordinate - 1 / 2) • difference) difference) 0 at generated
  rw [constant] at generated
  have conservation := generated.unique (hasDerivAt_const (0 : ℝ) (inner ℂ difference difference))
  simp only [inner_smul_left, inner_smul_right, starRingEnd_apply] at conservation
  have actual := congrArg (RCLike.re (K := ℂ)) conservation
  norm_num [RCLike.mul_re, RCLike.conj_re, inner_self_im, inner_self_eq_norm_sq] at actual
  rcases actual with impossible | normSquare
  · linarith [half.down]
  have normSquareReal : ‖difference‖ ^ 2 = 0 := by exact_mod_cast normSquare
  have positive : 0 < observation.coordinate.re - 1 / 2 := sub_pos.mpr half.down
  have normZero : ‖difference‖ = 0 := by
    nlinarith [norm_nonneg difference]
  have zero : sourceDifference observation nontrivial half = 0 := norm_eq_zero.mp normZero
  exact sub_eq_zero.mp zero

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceReturn
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
