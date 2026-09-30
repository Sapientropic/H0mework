import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.SamplingEven

/-! The full original source sampling pairing is the original physical Hilbert pairing. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private def tatePairingIsometry : BurnolL2 →ₗᵢ[ℂ] BurnolL2 where
  toLinearMap := burnolTateReciprocalL2.toLinearMap
  norm_map' := burnolTateReciprocalValue_norm

theorem originalContactKernel_physical_pairing {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    2 * inner ℂ (originalContactKernel observation nontrivial rightHalf)
      (contactRestriction (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))) =
        inner ℂ W (p : BurnolL2) := by
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let wave : BurnolPaAmbientCarrier := one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one
  let W : BurnolL2 := wave
  let kernel := burnolPaSamplingKernel W
  let sigma := burnolTateReciprocalL2 (burnolMobiusSourceL2 p)
  have moment : MemLp (fun x : ℝ => (x : ℂ) * W x) 2 volume := by
    apply burnolPhysicalStrong_firstMoment wave
    exact burnolUnitFourierPair_hasDerivAt
      (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
  have evenWave : reflectL2 W = W := mem_evenL2ClosedFace_iff.mp wave.property.2
  have evenKernel : reflectL2 (burnolTateReciprocalL2 kernel) = burnolTateReciprocalL2 kernel := by
    rw [← burnolTateReciprocal_reflect, pa_sampling_kernel_even W evenWave moment]
  have evenSource : reflectL2 sigma = sigma := by
    rw [← burnolTateReciprocal_reflect, burnolMobiusSourceL2_even]
  have paired := even_contact_inner (burnolTateReciprocalL2 kernel) sigma evenKernel evenSource
    (pa_tate_source_annulus p inside)
  have tate := tatePairingIsometry.inner_map_map kernel (burnolMobiusSourceL2 p)
  change inner ℂ (burnolTateReciprocalL2 kernel) sigma =
    inner ℂ kernel (burnolMobiusSourceL2 p) at tate
  have mean := even_contact_window_integral sigma evenSource (pa_tate_source_annulus p inside)
  have actual := burnolPaSamplingKernel_fullPa W
    (burnolZeroOwnedUnitOnePair_integrable observation nontrivial rightHalf) moment p inside
  rw [burnolPaPositionMean_from_source p inside, mean, ← tate, paired] at actual
  dsimp only
  change 2 * inner ℂ
    (contactRestriction (burnolTateReciprocalL2 kernel) -
      ((1 / 2 : ℂ) * ∫ x : ℝ, W x) •
        Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ))
    (contactRestriction sigma) = inner ℂ W (p : BurnolL2)
  rw [inner_sub_left, inner_smul_left, actual]
  simp only [map_mul, Complex.star_def, map_div₀, map_ofNat, map_one]
  ring

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
