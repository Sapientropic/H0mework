import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceBalance.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceBalance
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
attribute [local instance 1100] NormedSpace.complexToReal
namespace P
export OriginalKCombPhysicalAction (R)
end P
namespace Paid
export OriginalKCombCofinalRAction (parameter_rightQuarter original_R_direct)
end Paid

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

-- This is the actual operator on the supplied source input, including a material increment.
theorem source_R_ordinary_strong (input : BurnolL2) :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation shift
      (P.R observation nontrivial half input))
      (-(observation.coordinate - 1 / 2) • P.R observation nontrivial half input -
        (2 : ℂ) • input) 0 := by
  have actual := burnolDirectRightResolventOrbit_hasDerivAt (observation.coordinate / 2)
    (Paid.parameter_rightQuarter observation half) input
  rw [← Paid.original_R_direct observation nontrivial half input] at actual
  have scalar : HasDerivAt (fun shift : ℝ => -2 * shift) (-2 : ℝ) 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul (-2)
  have composed := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) actual.hasFDerivAt scalar (by norm_num)
  convert! composed using 1
  · funext shift
    change burnolMultiplicativeDilation shift _ = burnolMultiplicativeDilation (-(-2 * shift) / 2) _
    rw [show -(-2 * shift) / 2 = shift by ring]
  · change _ = (-2 : ℝ) • ((observation.coordinate / 2 - 1 / 4) •
      P.R observation nontrivial half input + input)
    rw [← algebraMap_smul ℂ (-2 : ℝ)]
    simp only [map_neg, map_ofNat]
    module

theorem source_R_cross_ward (input : BurnolL2) :
    inner ℂ (correctedVelocity (Prior.coordinate observation nontrivial half))
      (P.R observation nontrivial half input) +
    inner ℂ (correctedField (Prior.coordinate observation nontrivial half))
      (-(observation.coordinate - 1 / 2) • P.R observation nontrivial half input -
        (2 : ℂ) • input) = 0 := by
  have generated := (corrected_source_strong (Prior.coordinate observation nontrivial half)).inner ℂ
    (source_R_ordinary_strong observation nontrivial half input)
  simp only [burnolMultiplicativeDilation_zero] at generated
  have fixed : (fun shift : ℝ =>
      inner ℂ (burnolMultiplicativeDilation shift (correctedField (Prior.coordinate observation nontrivial half)))
        (burnolMultiplicativeDilation shift (P.R observation nontrivial half input))) =
      fun _ : ℝ => inner ℂ (correctedField (Prior.coordinate observation nontrivial half))
        (P.R observation nontrivial half input) := by
    funext shift
    exact (burnolMultiplicativeDilation shift).inner_map_map _ _
  rw [fixed] at generated
  simpa only [add_comm] using generated.unique
    (hasDerivAt_const (0 : ℝ) (inner ℂ (correctedField (Prior.coordinate observation nontrivial half))
      (P.R observation nontrivial half input)))

-- The unchanged original K is read after both real contact sources have been paid.
theorem source_R_originalK_equation (input : BurnolL2) :
    (2 * observation.coordinate - 1) *
      inner ℂ (Prior.originalK observation nontrivial half) (P.R observation nontrivial half input) +
    2 * inner ℂ (Prior.originalK observation nontrivial half) input =
    inner ℂ (regularSource (Prior.coordinate observation nontrivial half))
      (P.R observation nontrivial half input) -
    ((2 * observation.coordinate - 1) *
      inner ℂ (contactCorrection (Prior.coordinate observation nontrivial half))
        (P.R observation nontrivial half input) +
    2 * inner ℂ (contactCorrection (Prior.coordinate observation nontrivial half)) input) := by
  have actual := source_R_cross_ward observation nontrivial half input
  simp only [correctedVelocity, correctedField, inner_add_left, inner_smul_left,
    inner_sub_right, inner_smul_right, starRingEnd_apply, star_neg, star_sub,
    star_div₀, star_one, star_ofNat, star_star, Prior.coordinate_value] at actual
  change (2 * observation.coordinate - 1) *
      inner ℂ (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half) : BurnolL2)
        (P.R observation nontrivial half input) +
    2 * inner ℂ (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half) : BurnolL2)
      input = _
  linear_combination -actual

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceBalance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
