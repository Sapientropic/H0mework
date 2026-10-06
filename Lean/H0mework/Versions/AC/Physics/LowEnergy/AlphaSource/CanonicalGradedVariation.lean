import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalGradedCurrentSource

/-! Perturbation derivatives are constructed on the original finite families
before their common source lift. Uniform remainders do not assume continuity of
all completed time orbits. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.CanonicalGradedVariation
open LowEnergy.SourceFiniteUnitary
open scoped Topology InnerProductSpace Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem continuous_time (C : E →L[ℂ] E) : Continuous (time C) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

private theorem derivative_time (C : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (time C) (time C t * ((-Complex.I) • C)) t :=
  hasDerivAt_exp_smul_const ((-Complex.I) • C) t

private theorem time_bound (C : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (t : ℝ) :
    ‖time C t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [time_norm C symmetric, one_mul]

/-- The source ordered perturbation integral retains both actual times. -/
def differenceIntegral (C D : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  ∫ s in (0 : ℝ)..t, time D s * ((-Complex.I) • (D-C)) * time C (t-s)

theorem time_difference (C D : E →L[ℂ] E) (t : ℝ) :
    time D t-time C t = differenceIntegral C D t := by
  let f := fun s : ℝ => time D s * time C (t-s)
  let df := fun s : ℝ => time D s * ((-Complex.I) • (D-C)) * time C (t-s)
  have hd (s : ℝ) : HasDerivAt f (df s) s := by
    have hc := (derivative_time C (t-s)).scomp s ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    have hp := (derivative_time D s).mul hc
    have comm : ((-Complex.I) • C) * time C (t-s) =
        time C (t-s) * ((-Complex.I) • C) :=
      ((time_commutes C C (Commute.refl C) (t-s)).smul_left (-Complex.I)).eq
    have rearrange : time D s * ((-Complex.I) • C) * time C (t-s) =
        time D s * (time C (t-s) * ((-Complex.I) • C)) := by rw [mul_assoc, comm]
    convert hp using 1
    all_goals first | rfl | (simp only [df, Function.comp_apply, zero_sub, neg_one_smul,
      mul_neg, smul_sub, mul_sub, sub_mul, rearrange]; abel)
  have integrable : IntervalIntegrable df MeasureTheory.volume 0 t := by
    exact (((continuous_time D).mul continuous_const).mul
      ((continuous_time C).comp (continuous_const.sub continuous_id))).intervalIntegrable 0 t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) integrable
  simpa only [f, df, sub_zero, sub_self, time_zero, mul_one, one_mul, differenceIntegral] using h.symm

theorem difference_bound (C D : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (hd : IsSelfAdjoint D) (t : ℝ) :
    ‖time D t-time C t‖ ≤ |t| * ‖D-C‖ := by
  rw [time_difference, differenceIntegral]
  have bound (s : ℝ) (_ : s ∈ Ι (0 : ℝ) t) :
      ‖time D s * ((-Complex.I) • (D-C)) * time C (t-s)‖ ≤ ‖D-C‖ := by
    have scalar : ‖(-Complex.I) • (D-C)‖ = ‖D-C‖ := by
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    calc
      _ ≤ (‖time D s‖ * ‖(-Complex.I) • (D-C)‖) * ‖time C (t-s)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖D-C‖)*1 := by
        rw [scalar]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (time_bound D hd s) (norm_nonneg _))
          (time_bound C hc (t-s)) (norm_nonneg _) (by positivity)
      _ = ‖D-C‖ := by ring
  simpa only [sub_zero, mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const bound


def variationBetween (C B : E →L[ℂ] E) (parameter t : ℝ) : E →L[ℂ] E :=
  ∫ s in (0 : ℝ)..t, time (C+parameter • B) s * ((-Complex.I) • B) * time C (t-s)

def variation (C B : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := variationBetween C B 0 t

private theorem integrable_variation (C B : E →L[ℂ] E) (parameter t : ℝ) :
    IntervalIntegrable (fun s => time (C+parameter • B) s * ((-Complex.I) • B) * time C (t-s))
      MeasureTheory.volume 0 t :=
  (((continuous_time (C+parameter • B)).mul continuous_const).mul
    ((continuous_time C).comp (continuous_const.sub continuous_id))).intervalIntegrable 0 t

theorem parameter_difference (C B : E →L[ℂ] E) (parameter t : ℝ) :
    time (C+parameter • B) t-time C t = parameter • variationBetween C B parameter t := by
  rw [time_difference, differenceIntegral, variationBetween, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [add_sub_cancel_left, smul_comm (-Complex.I) parameter, mul_smul_comm, smul_mul_assoc]

theorem variation_bound (C B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (t : ℝ) : ‖variation C B t‖ ≤ |t| * ‖B‖ := by
  rw [variation, variationBetween]
  have bound (s : ℝ) (_ : s ∈ Ι (0 : ℝ) t) :
      ‖time (C+(0 : ℝ) • B) s * ((-Complex.I) • B) * time C (t-s)‖ ≤ ‖B‖ := by
    simp only [zero_smul, add_zero]
    calc
      _ ≤ (‖time C s‖*‖(-Complex.I) • B‖)*‖time C (t-s)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖B‖)*1 := by
        have scalar : ‖(-Complex.I) • B‖ = ‖B‖ := by
          rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
        rw [scalar]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (time_bound C hc s) (norm_nonneg _))
          (time_bound C hc (t-s)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  simpa only [sub_zero, mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const bound

theorem variation_difference_bound (C B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (hb : IsSelfAdjoint B) (parameter t : ℝ) :
    ‖variationBetween C B parameter t-variation C B t‖ ≤ |parameter| * (|t| * ‖B‖)^2 := by
  have hd : IsSelfAdjoint (C+parameter • B) := hc.add ((IsSelfAdjoint.all parameter).smul hb)
  have identity : variationBetween C B parameter t-variation C B t =
      ∫ s in (0 : ℝ)..t, (time (C+parameter • B) s-time C s) * ((-Complex.I) • B) * time C (t-s) := by
    rw [variation, variationBetween, variationBetween,
      ← intervalIntegral.integral_sub (integrable_variation C B parameter t) (integrable_variation C B 0 t)]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [zero_smul, add_zero, sub_mul]
  rw [identity]
  have bound (s : ℝ) (hs : s ∈ Ι (0 : ℝ) t) :
      ‖(time (C+parameter • B) s-time C s) * ((-Complex.I) • B) * time C (t-s)‖ ≤
        |parameter| * |t| * ‖B‖^2 := by
    have st : |s| ≤ |t| := by
      by_cases ht0 : 0 ≤ t
      · rw [Set.uIoc_of_le ht0] at hs
        rw [abs_of_pos hs.1, abs_of_nonneg ht0]
        exact hs.2
      · have htn : t ≤ 0 := le_of_not_ge ht0
        rw [Set.uIoc_of_ge htn] at hs
        rw [abs_of_nonpos hs.2, abs_of_nonpos htn]
        linarith [hs.1]
    have diff := difference_bound C (C+parameter • B) hc hd s
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at diff
    have ds : ‖time (C+parameter • B) s-time C s‖ ≤ |t| * (|parameter| * ‖B‖) :=
      diff.trans (mul_le_mul_of_nonneg_right st (by positivity))
    calc
      _ ≤ (‖time (C+parameter • B) s-time C s‖*‖(-Complex.I) • B‖)*‖time C (t-s)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((|t| * (|parameter| * ‖B‖))*‖B‖)*1 := by
        have scalar : ‖(-Complex.I) • B‖ = ‖B‖ := by
          rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
        rw [scalar]
        exact mul_le_mul (mul_le_mul_of_nonneg_right ds (norm_nonneg _))
          (time_bound C hc (t-s)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have estimate := intervalIntegral.norm_integral_le_of_norm_le_const bound
  calc
    _ ≤ (|parameter| * |t| * ‖B‖^2) * |t| := by simpa only [sub_zero] using estimate
    _ = _ := by ring

theorem parameter_remainder (C B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (hb : IsSelfAdjoint B) (parameter t : ℝ) :
    ‖time (C+parameter • B) t-time C t-parameter • variation C B t‖ ≤
      (|t| * ‖B‖)^2 * ‖parameter‖^2 := by
  rw [parameter_difference, ← smul_sub, norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left (variation_difference_bound C B hc hb parameter t) (abs_nonneg parameter)
  simpa only [Real.norm_eq_abs] using h.trans_eq (by ring)


theorem parameter_derivative (C B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (hb : IsSelfAdjoint B) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => time (C+parameter • B) t) (variation C B t) 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero, zero_smul, add_zero]
  let K := (|t| * ‖B‖)^2
  have convergence : Filter.Tendsto (fun r : ℝ => K*‖r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using
      ((continuous_norm : Continuous (fun r : ℝ => ‖r‖)).tendsto 0).const_mul K
  apply squeeze_zero (fun r => mul_nonneg (inv_nonneg.mpr (norm_nonneg r)) (norm_nonneg _))
    (fun r => ?_) convergence
  have h := mul_le_mul_of_nonneg_left (parameter_remainder C B hc hb r t)
    (inv_nonneg.mpr (norm_nonneg r))
  have scalar : ‖r‖⁻¹*(K*‖r‖^2)=K*‖r‖ := by
    by_cases hz : ‖r‖=0
    · simp [hz]
    · field_simp
  exact h.trans_eq scalar

section Family
open SourceFamilyOperator SourceFamilyHilbert
variable {I : Type*}
local instance (u : Ultrafilter I) : NormedAlgebra ℝ (Hilbert E u →L[ℂ] Hilbert E u) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

omit [CompleteSpace E] in
theorem lift_bound (u : Ultrafilter I) (A : Operator I E) (M : ℝ) (positive : 0≤M)
    (bound : ∀ i, ‖A.component i‖≤M) : ‖lift u A‖≤M := by
  apply ContinuousLinearMap.opNorm_le_bound _ positive
  intro x
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [lift_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  apply le_of_tendsto_of_tendsto (norm_tendsto u (act u A f)) ((norm_tendsto u f).const_mul M)
  apply Filter.Eventually.of_forall
  intro i
  exact ((A.component i).le_opNorm (value f i)).trans
    (mul_le_mul_of_nonneg_right (bound i) (norm_nonneg _))


def timeFamily (C : I → E →L[ℂ] E) (hc : ∀ i, IsSelfAdjoint (C i))
    (B : E →L[ℂ] E) (hb : IsSelfAdjoint B) (parameter t : ℝ) : Operator I E :=
  ⟨fun i => time (C i+parameter • B) t, 1, zero_le_one, fun i x => by
    rw [time_norm _ ((hc i).add ((IsSelfAdjoint.all parameter).smul hb)), one_mul]⟩

def variationFamily (C : I → E →L[ℂ] E) (hc : ∀ i, IsSelfAdjoint (C i))
    (B : E →L[ℂ] E) (t : ℝ) : Operator I E :=
  ⟨fun i => variation (C i) B t, |t| * ‖B‖, by positivity, fun i x =>
    ((variation (C i) B t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (variation_bound (C i) B (hc i) t) (norm_nonneg _))⟩

def remainderFamily (C : I → E →L[ℂ] E) (hc : ∀ i, IsSelfAdjoint (C i))
    (B : E →L[ℂ] E) (hb : IsSelfAdjoint B) (parameter t : ℝ) : Operator I E :=
  ⟨fun i => time (C i+parameter • B) t-time (C i) t-parameter • variation (C i) B t,
    (|t| * ‖B‖)^2 * ‖parameter‖^2, by positivity, fun i x =>
    ((time (C i+parameter • B) t-time (C i) t-parameter • variation (C i) B t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (parameter_remainder (C i) B (hc i) hb parameter t) (norm_nonneg _))⟩

theorem lifted_remainder (u : Ultrafilter I) (C : I → E →L[ℂ] E)
    (hc : ∀ i, IsSelfAdjoint (C i)) (B : E →L[ℂ] E) (hb : IsSelfAdjoint B) (parameter t : ℝ) :
    lift u (remainderFamily C hc B hb parameter t) =
      lift u (timeFamily C hc B hb parameter t)-lift u (timeFamily C hc B hb 0 t)-
        parameter • lift u (variationFamily C hc B t) := by
  apply SourceFamilyOperator.ext u
  intro f
  rw [sub_apply, sub_apply, smul_apply, lift_coe, lift_coe, lift_coe, lift_coe,
    ← UniformSpace.Completion.coe_sub, ← UniformSpace.Completion.coe_smul,
    ← UniformSpace.Completion.coe_sub]
  congr 1
  apply Family.ext
  funext i
  change (time (C i+parameter • B) t-time (C i) t-parameter • variation (C i) B t) (value f i) =
    time (C i+parameter • B) t (value f i)-time (C i+(0 : ℝ) • B) t (value f i)-
      parameter • variation (C i) B t (value f i)
  simp only [zero_smul, add_zero, sub_apply, smul_apply]

theorem lifted_parameter_remainder (u : Ultrafilter I) (C : I → E →L[ℂ] E)
    (hc : ∀ i, IsSelfAdjoint (C i)) (B : E →L[ℂ] E) (hb : IsSelfAdjoint B) (parameter t : ℝ) :
    ‖lift u (timeFamily C hc B hb parameter t)-lift u (timeFamily C hc B hb 0 t)-
        parameter • lift u (variationFamily C hc B t)‖ ≤ (|t| * ‖B‖)^2 * ‖parameter‖^2 := by
  rw [← lifted_remainder]
  exact lift_bound u _ _ (by positivity) (fun i => parameter_remainder (C i) B (hc i) hb parameter t)

set_option synthInstance.maxHeartbeats 200000 in
theorem lifted_parameter_derivative (u : Ultrafilter I) (C : I → E →L[ℂ] E)
    (hc : ∀ i, IsSelfAdjoint (C i)) (B : E →L[ℂ] E) (hb : IsSelfAdjoint B) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => lift u (timeFamily C hc B hb parameter t))
      (lift u (variationFamily C hc B t)) 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero]
  let K := (|t| * ‖B‖)^2
  have convergence : Filter.Tendsto (fun r : ℝ => K*‖r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using
      ((continuous_norm : Continuous (fun r : ℝ => ‖r‖)).tendsto 0).const_mul K
  apply squeeze_zero (fun r => mul_nonneg (inv_nonneg.mpr (norm_nonneg r)) (norm_nonneg _))
    (fun r => ?_) convergence
  have h := mul_le_mul_of_nonneg_left (lifted_parameter_remainder u C hc B hb r t)
    (inv_nonneg.mpr (norm_nonneg r))
  have scalar : ‖r‖⁻¹*(K*‖r‖^2)=K*‖r‖ := by
    by_cases hz : ‖r‖=0
    · simp [hz]
    · field_simp
  exact h.trans_eq scalar

end Family

end LowEnergy.CanonicalGradedVariation
