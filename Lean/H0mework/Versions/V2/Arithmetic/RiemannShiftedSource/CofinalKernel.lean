import H0mework.Versions.V2.Arithmetic.RiemannShiftedSource.FirstMoment
import H0mework.Versions.V2.Arithmetic.RiemannRationalSource.CofinalKernel

/-! Actual shifted samples generate the finite and cofinal contact kernels with the full mean. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def originalShiftedFiniteContactKernel {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ) (N : ℕ) : ContactIntervalL2 :=
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let W : BurnolL2 := (one +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
  (∑ n ∈ Finset.range N, contactRestriction
    (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 (burnolMultiplicativeDilation h W) n))) -
      ((1 / 2 : ℂ) * ∫ x : ℝ, burnolMultiplicativeDilation h W x) •
        Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)

def originalShiftedContactKernel {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ) : ContactIntervalL2 :=
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let W : BurnolL2 := (one +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
  contactRestriction
    (burnolTateReciprocalL2 (burnolPaSamplingKernel (burnolMultiplicativeDilation h W))) -
      ((1 / 2 : ℂ) * ∫ x : ℝ, burnolMultiplicativeDilation h W x) •
        Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)

theorem originalShiftedFiniteContactKernel_tendsto {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ) :
    Tendsto (originalShiftedFiniteContactKernel observation nontrivial rightHalf h) atTop
      (𝓝 (originalShiftedContactKernel observation nontrivial rightHalf h)) := by
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let W : BurnolL2 := (one +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
  let shifted := burnolMultiplicativeDilation h W
  let transform := contactRestriction.comp burnolTateReciprocalL2
  let mean : ContactIntervalL2 := ((1 / 2 : ℂ) * ∫ x : ℝ, shifted x) •
    Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)
  have moment : MemLp (fun x : ℝ => (x : ℂ) * shifted x) 2 volume :=
    original_shifted_wave_firstMoment observation nontrivial rightHalf h
  have series := (burnolAnnulusSamplingL2_summable shifted moment).hasSum.tendsto_sum_nat
  have generated := ((transform.continuous.tendsto _).comp series).sub_const mean
  convert! generated using 1
  funext N
  change (∑ n ∈ Finset.range N, transform (burnolAnnulusSamplingL2 shifted n)) - mean =
    transform (∑ n ∈ Finset.range N, burnolAnnulusSamplingL2 shifted n) - mean
  rw [map_sum]

theorem originalShiftedFiniteContactKernel_coeFn {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ) (N : ℕ) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    (originalShiftedFiniteContactKernel observation nontrivial rightHalf h N : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (1 / 4 : ℝ) 4)] fun t =>
        (∑ n ∈ Finset.range N, burnolTateReciprocalL2
          (burnolAnnulusSamplingL2 (burnolMultiplicativeDilation h W) n) t) -
            ((1 / 2 : ℂ) * ∫ x : ℝ, burnolMultiplicativeDilation h W x) := by
  intro one W
  let shifted := burnolMultiplicativeDilation h W
  let samples := fun n =>
    contactRestriction (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 shifted n))
  let mean : ℂ := (1 / 2 : ℂ) * ∫ x : ℝ, shifted x
  let constant : ContactIntervalL2 :=
    Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)
  change (((∑ n ∈ Finset.range N, samples n) - mean • constant : ContactIntervalL2) : ℝ → ℂ)
    =ᵐ[volume.restrict (Ioc (1 / 4 : ℝ) 4)] _
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.range N, samples n) (mean • constant),
    Lp.coeFn_finsetSum (Finset.range N) samples, Lp.coeFn_smul mean constant,
    Lp.coeFn_const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ),
    ae_all_iff.mpr (fun n => LpToLpRestrictCLM_coeFn ℂ (Ioc (1 / 4 : ℝ) 4)
      (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 shifted n)))]
        with t subRead sumRead scaleRead constRead allRead
  rw [subRead, Pi.sub_apply, sumRead, scaleRead, Pi.smul_apply, constRead]
  simp only [Function.const_apply, smul_eq_mul, mul_one, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact allRead n

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
