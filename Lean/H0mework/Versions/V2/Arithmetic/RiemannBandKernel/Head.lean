import H0mework.Versions.V2.Arithmetic.RiemannBandKernel.Orbit
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Class

/-! The original Pa projection of the actual first response consumes its counted-harmonic source kernel normal equation. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolPaFourierBandProbe_resolvent_read (a b : ℝ) (aStrict : (1 / 4 : ℝ) < a)
    (ordered : a ≤ b) (bounded : b < 4) (n : ℕ)
    (z : ℂ) (rightQuarter : 1 / 4 < z.re) :
    inner ℂ (burnolPaFourierBandProbe a b aStrict ordered bounded : BurnolL2)
      (burnolDirectRightResolvent z (burnolPaCombApproximation n : BurnolL2)) =
      -(∫ t : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight z t *
        ∫ x : ℝ, star (burnolPaFourierBandProbeRaw a b x) * burnolPaCombOrbitRaw n (-t / 2) x) := by
  let probe := burnolPaFourierBandProbe a b aStrict ordered bounded
  have integrable := burnolDirectRightResolventIntegrand_integrableOn z rightQuarter
    (burnolPaCombApproximation n : BurnolL2)
  have mapped := (innerSL ℂ (probe : BurnolL2)).integral_comp_comm integrable
  change (∫ t : ℝ in Ioi 0, inner ℂ (probe : BurnolL2)
    (burnolDirectRightResolventIntegrand z (burnolPaCombApproximation n : BurnolL2) t)) =
      inner ℂ (probe : BurnolL2) (∫ t : ℝ in Ioi 0,
        burnolDirectRightResolventIntegrand z (burnolPaCombApproximation n : BurnolL2) t) at mapped
  unfold burnolDirectRightResolvent
  rw [inner_neg_right, ← mapped]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [burnolDirectRightResolventIntegrand, probe]
  rw [inner_smul_right (𝕜 := ℂ) (E := BurnolL2),
    burnolPaFourierBandProbe_orbit_inner a b aStrict ordered bounded n (-t / 2)]

theorem burnolPaFourierBandProbe_projection_response_inner {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (a b : ℝ) (aStrict : (1 / 4 : ℝ) < a) (ordered : a ≤ b) (bounded : b < 4) (n : ℕ) :
    inner ℂ (burnolPaFourierBandProbe a b aStrict ordered bounded)
      (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
        (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n)) =
      inner ℂ (burnolPaFourierBandProbe a b aStrict ordered bounded : BurnolL2)
        (burnolDirectRightResolvent (observation.coordinate / 2)
          (burnolPaCombApproximation n : BurnolL2)) := by
  let probe := burnolPaFourierBandProbe a b aStrict ordered bounded
  let response := burnolPaCombPhysicalResponse observation nontrivial rightHalf n
  have belongs := burnolPaFourierBandProbe_mem a b aStrict ordered bounded
  have normal := burnolCompactCoPoissonClosedRange.toSubmodule
    |>.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨probe, belongs⟩
      (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n)
  change inner ℂ probe (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n)) =
    inner ℂ probe (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n) at normal
  have fourier := (evenFaceFourierEquiv burnolUnscaledCommonGapRadius).inner_map_map probe response
  rw [burnolPaFourierBandProbe_fourier_fixed a b aStrict ordered bounded] at fourier
  calc
    _ = inner ℂ probe (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n) := normal
    _ = inner ℂ probe response := by
      unfold burnolPaCombPairedPhysicalResponse
      rw [inner_smul_right (𝕜 := ℂ) (E := BurnolPaAmbientCarrier), inner_add_right, fourier]
      ring

/-- The original infinite Pa projection is tested, not replaced by a finite Gram inverse. -/
theorem burnolPaFourierBandProbe_head_normalEquation {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (a b : ℝ) (aStrict : (1 / 4 : ℝ) < a) (ordered : a ≤ b) (bounded : b < 4) :
    inner ℂ (burnolPaFourierBandProbe a b aStrict ordered bounded)
      (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
        (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0)) =
      -(∫ t : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (observation.coordinate / 2) t *
        ∫ x : ℝ, star (burnolPaFourierBandProbeRaw a b x) * burnolPaCombOrbitRaw 0 (-t / 2) x) := by
  rw [burnolPaFourierBandProbe_projection_response_inner]
  apply burnolPaFourierBandProbe_resolvent_read
  rw [Complex.div_re]
  norm_num
  linarith
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
