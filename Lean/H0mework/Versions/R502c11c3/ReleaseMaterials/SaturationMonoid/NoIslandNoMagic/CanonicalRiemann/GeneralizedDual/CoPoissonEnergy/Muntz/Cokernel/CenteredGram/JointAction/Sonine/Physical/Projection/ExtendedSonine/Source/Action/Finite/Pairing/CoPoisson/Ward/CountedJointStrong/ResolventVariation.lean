import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointQuantitative
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong

open Complex Filter Set
open scoped Topology InnerProductSpace

open private dilation_derivative from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong

local notation "D" => burnolMultiplicativeDilation
local notation "C" => ConstantDual.seed
local notation "R" => burnolDirectRightResolventCLM
local notation "v₀" => fun (c : BurnolCompletedMellinCoordinate) (input : BurnolL2) =>
  -((BurnolCompletedMellinCoordinate.value c-1/2) • R c input+(2 : ℂ) • input)

theorem actual_resolvent_dilation_derivative (c : BurnolCompletedMellinCoordinate) (input : BurnolL2) :
    HasDerivAt (fun h : ℝ => D h (R c input)) (v₀ c input) 0 := by
  have right : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have actual := (burnolDirectRightResolventOrbit_hasDerivAt (c.value/2) right input).scomp_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).const_mul (-2)) (by norm_num)
  simp only [mul_one, Function.comp_def, id_eq] at actual
  have path : (fun h : ℝ => D (-(-2*h)/2) (burnolDirectRightResolvent (c.value/2) input)) =
      fun h => D h (R c input) := by
    funext h
    rw [show -(-2*h)/2=h by ring]
    rfl
  change HasDerivAt _ ((-2 : ℝ) • ((c.value/2-1/4) • R c input+input)) 0 at actual
  have velocity : (-2 : ℝ) • ((c.value/2-1/4) • R c input+input) = v₀ c input := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    push_cast
    module
  rwa [path, velocity] at actual

private theorem seed_dilation_variation (h : ℝ) (nonnegative : 0 ≤ h) :
    ‖D h C-C‖ ≤ Real.sqrt h := by
  have gap : burnolQuarterRestriction C = (1 : ℂ) • intervalConstant (1/4) := by
    rw [ConstantDual.seed, burnolQuarterRestriction_zeroExtension, one_smul]
  have pairing (t : ℝ) (positive : 0 ≤ t) :
      inner ℂ C (D t C) = ((Real.exp (-t/2)/2 : ℝ) : ℂ) := by
    rw [CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction.inward_constant_contact C 1 gap t positive]
    simp only [star_one, mul_one, Complex.ofReal_div, Complex.ofReal_ofNat]
  have self : inner ℂ C C = (1/2 : ℂ) := by
    simpa only [burnolMultiplicativeDilation_zero, neg_zero, zero_div, Real.exp_zero,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using pairing 0 le_rfl
  have mass : ‖C‖^2 = (1/2 : ℝ) := by
    apply Complex.ofReal_injective
    push_cast
    exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) C).symm.trans self
  have square : ‖C-D h C‖^2 = 1-Real.exp (-h/2) := by
    rw [norm_sub_sq (𝕜 := ℂ), LinearIsometryEquiv.norm_map, mass, pairing h nonnegative]
    change 1/2-2*(Real.exp (-h/2)/2)+1/2 = _
    ring
  rw [norm_sub_rev]
  nlinarith [Real.add_one_le_exp (-h/2), Real.sq_sqrt nonnegative, Real.sqrt_nonneg h,
    norm_nonneg (C-D h C)]

private theorem resolvent_dilation_variation (c : BurnolCompletedMellinCoordinate) (input : BurnolL2)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    ‖D h (R c input)-R c input‖ ≤ ‖v₀ c input‖*h := by
  have derivative := actual_resolvent_dilation_derivative c input
  have rate := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := h)
    (fun t _ => (dilation_derivative _ _ derivative t).hasDerivWithinAt)
    (fun t _ => (LinearIsometryEquiv.norm_map (D t) (v₀ c input)).le)
    h ⟨nonnegative, le_rfl⟩
  simpa only [burnolMultiplicativeDilation_zero, sub_zero] using rate

private theorem seed_resolvent_variation (c : BurnolCompletedMellinCoordinate) (a : ℂ) (input : BurnolL2)
    (h : ℝ) (within : h ∈ Icc (0 : ℝ) 1) :
    ‖D h (a • C+R c input)-(a • C+R c input)‖ ≤ (‖a‖+‖v₀ c input‖)*Real.sqrt h := by
  have upper : Real.sqrt h ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt within.2
  have root : h ≤ Real.sqrt h := by
    nlinarith [Real.sq_sqrt within.1, mul_nonneg (Real.sqrt_nonneg h) (sub_nonneg.mpr upper)]
  rw [map_add, map_smul, add_sub_add_comm, ← smul_sub]
  apply (norm_add_le _ _).trans
  rw [norm_smul, add_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (seed_dilation_variation h within.1) (norm_nonneg _))
    ((resolvent_dilation_variation c input h within.1).trans (mul_le_mul_of_nonneg_left root (norm_nonneg _)))

/-- A literal seed plus a generated R image supplies the velocity variation
for the original reverse count, including the seed's moving contact. -/
theorem seed_resolvent_counted_endpoint_rate (c : BurnolCompletedMellinCoordinate)
    (a : ℂ) (drive : BurnolL2) :
    let input := a • C+R c drive
    let acted := R c input
    ∃ limit : BurnolL2, Tendsto (fun N => DualSource.source N acted) atTop (𝓝 limit) ∧
      ∃ budget : ℝ, 0 ≤ budget ∧ ∀ M : Nat, 0 < M →
        ‖limit-DualSource.source (M+1) acted-(1/2 : ℝ) •
          ContinuousChannels.channel 1 ((M : ℝ)+1) acted‖ ≤ budget/(M : ℝ) := by
  dsimp only
  let input := a • C+R c drive
  let acted := R c input
  let velocity := v₀ c input
  let forcing := -c.value • input-(2 : ℂ) • drive
  let cost := ‖-(2 : ℂ)*a‖+‖v₀ c forcing‖
  have cost₀ : 0 ≤ cost := by dsimp only [cost]; positivity
  have split : (1 : ℝ) • velocity-(1/2 : ℝ) • acted =
      (-(2 : ℂ)*a) • C+R c forcing := by
    rw [one_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    dsimp only [velocity, acted, forcing]
    rw [map_sub, map_smul, map_smul]
    have given : input = a • C+R c drive := rfl
    linear_combination (norm := module) -(2 : ℂ) • given
  obtain ⟨limit, counted, rate⟩ := directional_source_endpoint_rate 1 acted velocity
    (actual_resolvent_dilation_derivative c input) cost cost₀ (by
      intro h within
      rw [one_mul, split]
      exact seed_resolvent_variation c _ _ h within)
  exact ⟨limit, counted, 2*(cost+(3/2)*‖(1 : ℝ) • velocity-(1/2 : ℝ) • acted‖),
    by positivity, rate⟩

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
