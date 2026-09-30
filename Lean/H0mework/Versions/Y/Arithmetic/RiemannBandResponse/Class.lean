import H0mework.Versions.Y.Arithmetic.RiemannBandResponse.PhysicalLanding
import H0mework.Versions.Y.Arithmetic.RiemannUnitFourier.ActionPhysical

/-! Every paired native response reads the same original Z, with its generated nonzero Mellin coefficient. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolPaCombPairedPhysicalResponse {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) : BurnolPaAmbientCarrier :=
  (1 / 2 : ℂ) • (burnolPaCombPhysicalResponse observation nontrivial rightHalf n +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolPaCombPhysicalResponse observation nontrivial rightHalf n))

theorem burnolPaCombPairedPhysicalResponse_scaledQ {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    (observation.coordinate / 2) •
        burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
          (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n) =
      (((n : ℂ) + 2) / 2 * (Complex.exp (observation.coordinate *
        (Real.log (1 + burnolPaCombSourceWidth n) : ℂ)) - 1)) •
        (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) := by
  let Q := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  let response := burnolPaCombPhysicalResponse observation nontrivial rightHalf n
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  have covariance (value : BurnolPaAmbientCarrier) : Q (F value) = F (Q value) := by
    exact (congrArg (fun result : SourceGeneratedHilbertCokernel.OrthogonalResidual
      burnolCompactCoPoissonLanding => (result : BurnolPaAmbientCarrier))
        (burnolCompactCoPoissonActionSquare.orthogonalAction_residual value)).symm
  have same := burnolUnitOne_fourierClass observation nontrivial rightHalf
  change Q (one + F one) = _ at same
  rw [← same]
  change (observation.coordinate / 2) • Q ((1 / 2 : ℂ) • (response + F response)) =
    _ • Q (one + F one)
  simp only [map_smul, map_add, covariance]
  have primary := burnolPaCombPhysicalResponse_scaledQ observation nontrivial rightHalf n
  change (observation.coordinate / 2) • Q response = _ • Q one at primary
  have reflected := congrArg F primary
  simp only [map_smul] at reflected
  calc
    _ = (1 / 2 : ℂ) • ((observation.coordinate / 2) • Q response +
        (observation.coordinate / 2) • F (Q response)) := by module
    _ = _ := by rw [primary, reflected]; module

def burnolPaCombResponseCoefficient (coordinate : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 2) / coordinate *
    (Complex.exp (coordinate * (Real.log (1 + burnolPaCombSourceWidth n) : ℂ)) - 1)

theorem burnolPaCombPairedPhysicalResponse_Q {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n) =
        burnolPaCombResponseCoefficient observation.coordinate n •
          (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) := by
  have sNe : observation.coordinate ≠ 0 := by
    intro zero
    rw [zero] at rightHalf
    norm_num at rightHalf
  have zNe : observation.coordinate / 2 ≠ 0 := div_ne_zero sNe (by norm_num)
  have generated := congrArg (fun value : BurnolPaAmbientCarrier =>
      (observation.coordinate / 2)⁻¹ • value)
    (burnolPaCombPairedPhysicalResponse_scaledQ observation nontrivial rightHalf n)
  rw [inv_smul_smul₀ zNe, smul_smul] at generated
  convert generated using 1
  congr 1
  unfold burnolPaCombResponseCoefficient
  field_simp

theorem burnolPaCombResponseCoefficient_ne_zero (coordinate : ℂ)
    (positive : 0 < coordinate.re) (n : ℕ) :
    burnolPaCombResponseCoefficient coordinate n ≠ 0 := by
  have sNe : coordinate ≠ 0 := by
    intro zero
    rw [zero] at positive
    norm_num at positive
  have massNe : (n : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show (n : ℝ) + 2 ≠ 0 by positivity)
  have width := (burnolPaCombSourceWidth_bounds n).1
  have logPositive : 0 < Real.log (1 + burnolPaCombSourceWidth n) :=
    Real.log_pos (by linarith)
  have exponentialNe : Complex.exp (coordinate * (Real.log (1 + burnolPaCombSourceWidth n) : ℂ)) ≠ 1 := by
    intro one
    have magnitude := congrArg norm one
    rw [Complex.norm_exp, norm_one] at magnitude
    have positiveExponent : 0 < (coordinate * (Real.log (1 + burnolPaCombSourceWidth n) : ℂ)).re := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
        mul_pos positive logPositive
    have larger := Real.one_lt_exp_iff.mpr positiveExponent
    linarith
  exact mul_ne_zero (div_ne_zero massNe sNe) (sub_ne_zero.mpr exponentialNe)

theorem burnolPaCombPairedPhysicalResponse_Q_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n) ≠ 0 := by
  rw [burnolPaCombPairedPhysicalResponse_Q observation nontrivial rightHalf n]
  apply smul_ne_zero
  · exact burnolPaCombResponseCoefficient_ne_zero observation.coordinate
      (lt_trans (by norm_num) rightHalf) n
  · intro zero
    exact burnolZeroOwnedUnitFourierPaState_nonzero observation nontrivial rightHalf (Subtype.ext zero)
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
