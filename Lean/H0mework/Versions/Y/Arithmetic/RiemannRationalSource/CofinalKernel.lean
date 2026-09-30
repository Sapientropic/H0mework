import H0mework.Versions.Y.Arithmetic.RiemannWholeWard.WholeClosedRange
import H0mework.Versions.Y.Arithmetic.RiemannBandKernel.TransposeKernel

/-! The original first moment generates the cofinal Ward kernel; no contact series is separately assumed. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def originalContactKernel {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) : ContactIntervalL2 :=
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let W : BurnolL2 := (one +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
  contactRestriction (burnolTateReciprocalL2 (burnolPaSamplingKernel W)) -
    ((1 / 2 : ℂ) * ∫ x : ℝ, W x) •
      Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)

theorem originalFiniteContactKernel_tendsto {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    Tendsto (originalFiniteContactKernel observation nontrivial rightHalf) atTop
      (𝓝 (originalContactKernel observation nontrivial rightHalf)) := by
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let W : BurnolL2 := (one +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
  let transform := contactRestriction.comp burnolTateReciprocalL2
  let mean : ContactIntervalL2 := ((1 / 2 : ℂ) * ∫ x : ℝ, W x) •
    Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)
  have moment : MemLp (fun x : ℝ => (x : ℂ) * W x) 2 volume := by
    apply burnolPhysicalStrong_firstMoment
      (one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one)
    exact burnolUnitFourierPair_hasDerivAt
      (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
  have series := (burnolAnnulusSamplingL2_summable W moment).hasSum.tendsto_sum_nat
  have generated := ((transform.continuous.tendsto _).comp series).sub_const mean
  convert! generated using 1
  funext N
  change (∑ n ∈ Finset.range N, transform (burnolAnnulusSamplingL2 W n)) - mean =
    transform (∑ n ∈ Finset.range N, burnolAnnulusSamplingL2 W n) - mean
  rw [map_sum]

theorem originalPa_source_ward_tendsto {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius p = p) :
    Tendsto (fun N : ℕ => originalFiniteSourceWard observation nontrivial rightHalf N ⟨p, inside⟩)
      atTop (𝓝 (4 * contactBilinearRead (originalContactKernel observation nontrivial rightHalf)
        (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) := by
  let sigma := burnolTateReciprocalL2 (burnolMobiusSourceL2 p)
  have regular : Continuous (fun kernel : ContactIntervalL2 => contactBilinearRead kernel sigma) := by
    have swap (kernel : ContactIntervalL2) : contactBilinearRead kernel sigma =
        inner ℂ (star (contactRestriction sigma)) kernel := by
      change inner ℂ (star kernel) (contactRestriction sigma) = _
      rw [L2.inner_def, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_star kernel, Lp.coeFn_star (contactRestriction sigma)] with t first second
      simp only [RCLike.inner_apply, first, second, Pi.star_apply, Complex.star_def, Complex.conj_conj]
      ring
    have identifies : (fun kernel : ContactIntervalL2 => contactBilinearRead kernel sigma) =
        (fun kernel => inner ℂ (star (contactRestriction sigma)) kernel) := funext swap
    rw [identifies]
    exact continuous_const.inner continuous_id
  have generated := (regular.tendsto _).comp
    (originalFiniteContactKernel_tendsto observation nontrivial rightHalf)
  exact (generated.const_mul 4).congr
    (fun N => originalPa_fixed_finite_ward observation nontrivial rightHalf N p inside fixed)

theorem original_head_source_ward_tendsto {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    Tendsto (fun N : ℕ => originalFiniteSourceWard observation nontrivial rightHalf N
      ⟨p, Submodule.starProjection_apply_mem _ _⟩) atTop
        (𝓝 (4 * contactBilinearRead (originalContactKernel observation nontrivial rightHalf)
          (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) :=
  originalPa_source_ward_tendsto observation nontrivial rightHalf _
    (Submodule.starProjection_apply_mem _ _)
    (burnolPaProjectedHead_fourier_fixed observation nontrivial rightHalf)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
