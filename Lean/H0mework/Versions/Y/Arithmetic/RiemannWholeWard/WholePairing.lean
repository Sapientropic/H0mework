import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.CompleteMean
import H0mework.Versions.Y.Arithmetic.RiemannWholeWard.SecondWindow

/-! Fixed-annulus continuous reads of the original source and its generated window. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

abbrev ContactIntervalL2 := Lp ℂ 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4))

def contactRestriction : BurnolL2 →L[ℂ] ContactIntervalL2 :=
  LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Ioc (1 / 4 : ℝ) 4)

def contactBilinearRead (kernel : ContactIntervalL2) : BurnolL2 →L[ℂ] ℂ :=
  (innerSL ℂ (star kernel)).comp contactRestriction

theorem contactBilinearRead_eq_integral (kernel : ContactIntervalL2) (value : BurnolL2) :
    contactBilinearRead kernel value =
      ∫ t : ℝ in (1 / 4)..4, value t * kernel t := by
  change inner ℂ (star kernel) (contactRestriction value) = _
  rw [L2.inner_def, intervalIntegral.integral_of_le (by norm_num)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star kernel,
    LpToLpRestrictCLM_coeFn ℂ (Ioc (1 / 4 : ℝ) 4) value] with t starRead restricted
  change inner ℂ ((star kernel : ContactIntervalL2) t) (contactRestriction value t) = _
  rw [starRead]
  change inner ℂ (star (kernel t)) (contactRestriction value t) = _
  change contactRestriction value t = value t at restricted
  rw [restricted]
  simp only [RCLike.inner_apply, Complex.star_def, Complex.conj_conj]

def contactIntegral : BurnolL2 →L[ℂ] ℂ :=
  contactBilinearRead (Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ))

theorem contactIntegral_eq_integral (value : BurnolL2) :
    contactIntegral value = ∫ t : ℝ in (1 / 4)..4, value t := by
  rw [contactIntegral, contactBilinearRead_eq_integral,
    intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)] with t constant
  rw [constant]
  exact mul_one _

def contactReciprocalIntegral : BurnolL2 →L[ℂ] ℂ :=
  burnolRadiusMellinTailEvaluator (1 / 4) (by norm_num) 1 (by norm_num) -
    burnolRadiusMellinTailEvaluator 4 (by norm_num) 1 (by norm_num)

theorem contactReciprocalIntegral_eq_integral (value : BurnolL2) :
    contactReciprocalIntegral value =
      ∫ t : ℝ in (1 / 4)..4, value t / (t : ℂ) := by
  simp only [contactReciprocalIntegral, sub_apply, burnolRadiusMellinTailEvaluator_eq_integral]
  rw [intervalIntegral.integral_Ioi_sub_Ioi
    (burnolRadiusMellinWeight_integrableOn_tail (1 / 4) (by norm_num) 1 (by norm_num) value)
      (by norm_num : (1 / 4 : ℝ) ≤ 4)]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [Complex.cpow_neg_one]
  ring

def originalFiniteContactKernel {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ) : ContactIntervalL2 :=
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let W : BurnolL2 := (one +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
  (∑ n ∈ Finset.range N, contactRestriction
    (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n))) -
      ((1 / 2 : ℂ) * ∫ x : ℝ, W x) •
        Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)

theorem originalFiniteContactKernel_coeFn {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    (originalFiniteContactKernel observation nontrivial rightHalf N : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (1 / 4 : ℝ) 4)] fun t =>
        (∑ n ∈ Finset.range N, burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t) -
          ((1 / 2 : ℂ) * ∫ x : ℝ, W x) := by
  intro one W
  let samples := fun n => contactRestriction (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n))
  let mean : ℂ := (1 / 2 : ℂ) * ∫ x : ℝ, W x
  let constant : ContactIntervalL2 := Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)
  change (((∑ n ∈ Finset.range N, samples n) - mean • constant : ContactIntervalL2) : ℝ → ℂ)
    =ᵐ[volume.restrict (Ioc (1 / 4 : ℝ) 4)] _
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.range N, samples n) (mean • constant),
    Lp.coeFn_finsetSum (Finset.range N) samples, Lp.coeFn_smul mean constant,
    Lp.coeFn_const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ),
    ae_all_iff.mpr (fun n => LpToLpRestrictCLM_coeFn ℂ (Ioc (1 / 4 : ℝ) 4)
      (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n)))] with t subRead sumRead scaleRead constRead allRead
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
