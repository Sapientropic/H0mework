import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceBalance.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceBalance
open Complex
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

-- The original K read is returned with all original endpoint compensation.
theorem actual_R_originalK_source_equation :
    (2 * observation.coordinate - 1) *
      inner ℂ (Prior.originalK observation nontrivial half)
        (D.raw observation nontrivial half depth (ordinal + 1)) +
    2 * inner ℂ (Prior.originalK observation nontrivial half)
      (D.raw observation nontrivial half depth ordinal) =
    inner ℂ (regularSource (Prior.coordinate observation nontrivial half))
      (D.raw observation nontrivial half depth (ordinal + 1)) -
    ((2 * observation.coordinate - 1) *
      inner ℂ (contactCorrection (Prior.coordinate observation nontrivial half))
        (D.raw observation nontrivial half depth (ordinal + 1)) +
    2 * inner ℂ (contactCorrection (Prior.coordinate observation nontrivial half))
      (D.raw observation nontrivial half depth ordinal)) := by
  have actual := actual_R_cross_ward observation nontrivial half depth ordinal
  simp only [correctedVelocity, correctedField, inner_add_left, inner_smul_left,
    inner_sub_right, inner_smul_right, starRingEnd_apply, star_neg, star_sub,
    star_div₀, star_one, star_ofNat, star_star, Prior.coordinate_value] at actual
  change (2 * observation.coordinate - 1) *
      inner ℂ (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half) : BurnolL2)
        (D.raw observation nontrivial half depth (ordinal + 1)) +
    2 * inner ℂ (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half) : BurnolL2)
      (D.raw observation nontrivial half depth ordinal) = _
  linear_combination -actual

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceBalance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
