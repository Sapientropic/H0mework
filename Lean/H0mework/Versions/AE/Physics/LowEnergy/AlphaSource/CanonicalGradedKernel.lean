import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalGradedFrequency

/-! The actual +εJ perturbation generates the ordered two-time impulse kernel.
Age remains explicit; its positive-damping transform is made on each complete
C_F before the original source-family lift. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedKernel
open SourceFiniteUnitary CanonicalGradedVariation
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace Interval

section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem continuous_time (C : E →L[ℂ] E) : Continuous (time C) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

private theorem time_bound (C : E →L[ℂ] E) (hc : IsSelfAdjoint C) (t : ℝ) :
    ‖time C t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [time_norm C hc, one_mul]

def ordered (C A B : E →L[ℂ] E) (t s : ℝ) : E →L[ℂ] E :=
  time C (-t) * A * time C (t-s) * B * time C s

def kernel (C A B : E →L[ℂ] E) (t s : ℝ) : E →L[ℂ] E :=
  Complex.I • (ordered C B A s t - ordered C A B t s)

theorem kernel_at_origin (C A B : E →L[ℂ] E) :
    kernel C A B 0 0 = Complex.I • (B*A-A*B) := by
  simp only [kernel, ordered, neg_zero, sub_self, time_zero, one_mul, mul_one]

theorem ordered_continuous (C A B : E →L[ℂ] E) :
    Continuous (fun p : ℝ × ℝ => ordered C A B p.1 p.2) := by
  unfold ordered
  exact (((((continuous_time C).comp continuous_fst.neg).mul continuous_const).mul
    ((continuous_time C).comp (continuous_fst.sub continuous_snd))).mul continuous_const).mul
      ((continuous_time C).comp continuous_snd)

theorem kernel_continuous (C A B : E →L[ℂ] E) :
    Continuous (fun p : ℝ × ℝ => kernel C A B p.1 p.2) :=
  (((ordered_continuous C B A).comp (continuous_snd.prodMk continuous_fst)).sub
    (ordered_continuous C A B)).const_smul Complex.I

theorem ordered_bound (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C) (t s : ℝ) :
    ‖ordered C A B t s‖ ≤ ‖A‖*‖B‖ := by
  have ha : ‖time C (-t)*A‖ ≤ ‖A‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (time_bound C hc (-t)) (norm_nonneg _)).trans_eq (one_mul _))
  have hb : ‖time C (-t)*A*time C (t-s)‖ ≤ ‖A‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul ha (time_bound C hc (t-s)) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))
  have hc' : ‖time C (-t)*A*time C (t-s)*B‖ ≤ ‖A‖*‖B‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  exact (norm_mul_le _ _).trans ((mul_le_mul hc' (time_bound C hc s)
    (norm_nonneg _) (by positivity)).trans_eq (mul_one _))

theorem kernel_bound (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C) (t s : ℝ) :
    ‖kernel C A B t s‖ ≤ 2*‖A‖*‖B‖ := by
  rw [kernel, norm_smul, Complex.norm_I, one_mul]
  exact (norm_sub_le _ _).trans
    ((add_le_add (ordered_bound C B A hc s t) (ordered_bound C A B hc t s)).trans_eq (by ring))

theorem variation_reverse (C B : E →L[ℂ] E) (t : ℝ) :
    variation C B t = ∫ s in (0 : ℝ)..t, (-Complex.I) • (time C (t-s)*B*time C s) := by
  let f := fun s => time C s*((-Complex.I) • B)*time C (t-s)
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t) f t
  rw [sub_self, sub_zero] at h
  change variation C B t = _
  rw [variation, variationBetween]
  simp only [zero_smul, add_zero]
  change (∫ s in (0 : ℝ)..t, f s) = _
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [f, show t-(t-s)=s by ring, mul_smul_comm, smul_mul_assoc]

theorem variation_negative (C B : E →L[ℂ] E) (t : ℝ) :
    variation C B (-t) = ∫ s in (0 : ℝ)..t, Complex.I • (time C (-s)*B*time C (s-t)) := by
  let f := fun s => time C s*((-Complex.I) • B)*time C (-t-s)
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := t) f
  rw [neg_zero] at h
  change variation C B (-t) = _
  rw [variation, variationBetween]
  simp only [zero_smul, add_zero]
  change (∫ s in (0 : ℝ)..(-t), f s) = _
  calc
    _ = -(∫ s in (-t)..(0 : ℝ), f s) := intervalIntegral.integral_symm (-t) 0
    _ = -(∫ s in (0 : ℝ)..t, f (-s)) := congrArg Neg.neg h.symm
    _ = _ := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [f, show -t-(-s)=s-t by ring, neg_smul, mul_neg, neg_mul, neg_neg,
        mul_smul_comm, smul_mul_assoc]

theorem derivative_kernel_integral (C A B : E →L[ℂ] E) (t : ℝ) :
    CanonicalGradedFrequency.finiteDerivative C A B t = ∫ s in (0 : ℝ)..t, kernel C A B t s := by
  let f := fun s => Complex.I • (time C (-s)*B*time C (s-t))
  let g := fun s => (-Complex.I) • (time C (t-s)*B*time C s)
  have hf : IntervalIntegrable f volume 0 t :=
    (((((continuous_time C).comp continuous_neg).mul continuous_const).mul
      ((continuous_time C).comp (continuous_id.sub continuous_const))).const_smul Complex.I).intervalIntegrable 0 t
  have hg : IntervalIntegrable g volume 0 t :=
    (((((continuous_time C).comp (continuous_const.sub continuous_id)).mul continuous_const).mul
      (continuous_time C)).const_smul (-Complex.I)).intervalIntegrable 0 t
  let L := (ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip (A*time C t)
  let R := ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (time C (-t)*A)
  have hl := L.intervalIntegral_comp_comm hf
  have hr := R.intervalIntegral_comp_comm hg
  have hli : IntervalIntegrable (fun s => L (f s)) volume 0 t := ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩
  have hri : IntervalIntegrable (fun s => R (g s)) volume 0 t := ⟨R.integrable_comp hg.1, R.integrable_comp hg.2⟩
  rw [CanonicalGradedFrequency.finiteDerivative, variation_negative, variation_reverse]
  change (∫ s in (0 : ℝ)..t, f s)*A*time C t+
    (time C (-t)*A)*(∫ s in (0 : ℝ)..t, g s) = _
  rw [mul_assoc]
  change L (∫ s in (0 : ℝ)..t, f s)+R (∫ s in (0 : ℝ)..t, g s) = _
  rw [← hl, ← hr, ← intervalIntegral.integral_add hli hri]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [L, R, ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply,
    f, g, kernel, ordered, neg_smul, mul_neg, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_neg, sub_eq_add_neg, mul_assoc]

def integrand (C A B : E →L[ℂ] E) (age frequency damping lag : ℝ) : E →L[ℂ] E :=
  CanonicalGradedFrequency.weight frequency damping lag • kernel C A B (age+lag) age

theorem integrand_continuous (C A B : E →L[ℂ] E) (age frequency damping : ℝ) :
    Continuous (integrand C A B age frequency damping) := by
  have hfuture : Continuous (fun lag : ℝ => time C (age+lag)) :=
    (continuous_time C).comp (continuous_const.add continuous_id)
  have hback : Continuous (fun lag : ℝ => time C (-(age+lag))) :=
    (continuous_time C).comp (continuous_const.add continuous_id).neg
  have hleft : Continuous (fun lag : ℝ =>
      time C (-age)*B*time C (age-(age+lag))*A*time C (age+lag)) :=
    (((continuous_const.mul continuous_const).mul
      ((continuous_time C).comp (continuous_const.sub (continuous_const.add continuous_id)))).mul
        continuous_const).mul hfuture
  have hright : Continuous (fun lag : ℝ =>
      time C (-(age+lag))*A*time C (age+lag-age)*B*time C age) :=
    (((hback.mul continuous_const).mul
      ((continuous_time C).comp ((continuous_const.add continuous_id).sub continuous_const))).mul
        continuous_const).mul continuous_const
  exact (CanonicalGradedFrequency.weight_continuous frequency damping).smul
    ((hleft.sub hright).const_smul Complex.I)

theorem integrand_bound (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (age frequency damping lag : ℝ) :
    ‖integrand C A B age frequency damping lag‖ ≤ Real.exp (-damping*lag)*(2*‖A‖*‖B‖) := by
  rw [integrand, norm_smul, CanonicalGradedFrequency.weight_norm]
  exact mul_le_mul_of_nonneg_left (kernel_bound C A B hc (age+lag) age) (Real.exp_pos _).le

theorem integrand_integrable (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (age frequency damping : ℝ) (positive : 0<damping) :
    IntegrableOn (integrand C A B age frequency damping) (Ioi 0) :=
  ((integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) 0).mul_const (2*‖A‖*‖B‖)).mono'
    (integrand_continuous C A B age frequency damping).aestronglyMeasurable
    (Filter.Eventually.of_forall (integrand_bound C A B hc age frequency damping))

def finiteResponse (C A B : E →L[ℂ] E) (age frequency damping : ℝ) : E →L[ℂ] E :=
  ∫ lag : ℝ in Ioi 0, integrand C A B age frequency damping lag

theorem finiteResponse_bound (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (age frequency damping : ℝ) (positive : 0<damping) :
    ‖finiteResponse C A B age frequency damping‖ ≤ 2*‖A‖*‖B‖/damping := by
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) 0).mul_const (2*‖A‖*‖B‖))
    (Filter.Eventually.of_forall (integrand_bound C A B hc age frequency damping))
  rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos positive) 0] at h
  simpa [finiteResponse, div_eq_mul_inv, mul_comm] using h

def finiteTruncation (C A B : E →L[ℂ] E) (age frequency damping cutoff : ℝ) : E →L[ℂ] E :=
  ∫ lag in (0 : ℝ)..cutoff, integrand C A B age frequency damping lag

theorem finite_truncation_tail (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (age frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) :
    ‖finiteResponse C A B age frequency damping-finiteTruncation C A B age frequency damping cutoff‖ ≤
      Real.exp (-damping*cutoff)/damping*(2*‖A‖*‖B‖) := by
  have hi := integrand_integrable C A B hc age frequency damping positive
  have ht := hi.mono_set (Ioi_subset_Ioi future)
  have split := intervalIntegral.integral_interval_add_Ioi hi ht
  change ‖(∫ lag in Ioi 0, integrand C A B age frequency damping lag)-
    (∫ lag in (0 : ℝ)..cutoff, integrand C A B age frequency damping lag)‖ ≤ _
  rw [← split, add_sub_cancel_left]
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) cutoff).mul_const (2*‖A‖*‖B‖))
    (Filter.Eventually.of_forall (integrand_bound C A B hc age frequency damping))
  rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos positive) cutoff] at h
  simpa only [neg_mul, neg_div_neg_eq] using h

end Finite

private theorem three_leg_return {R : Type*} [Monoid R]
    (P U₁ U₂ U₃ V₁ V₂ V₃ A B : R)
    (h₁ : P*U₁=P*V₁) (h₂ : P*U₂=P*V₂) (h₃ : P*U₃=P*V₃)
    (v₁ : Commute P V₁) (v₂ : Commute P V₂) (a : Commute P A) (b : Commute P B) :
    P*U₁*A*U₂*B*U₃=P*V₁*A*V₂*B*V₃ := by
  have first := (v₁.mul_right a).eq
  have second := (((v₁.mul_right a).mul_right v₂).mul_right b).eq
  calc
    _ = (P*V₁*A)*U₂*B*U₃ := by rw [h₁]
    _ = (V₁*A)*(P*U₂)*B*U₃ := by
      rw [← mul_assoc] at first
      rw [first]
      simp only [mul_assoc]
    _ = (V₁*A)*(P*V₂)*B*U₃ := by rw [h₂]
    _ = (P*V₁*A*V₂*B)*U₃ := by
      rw [← mul_assoc] at first
      rw [first]
      simp only [mul_assoc]
    _ = (V₁*A*V₂*B)*(P*U₃) := by
      simp only [← mul_assoc] at second
      rw [second]
      simp only [mul_assoc]
    _ = (V₁*A*V₂*B)*(P*V₃) := by rw [h₃]
    _ = _ := by
      simp only [← mul_assoc] at second
      rw [second]
      simp only [mul_assoc]

open GaussCoreHilbert CanonicalGradedCurrent CanonicalGradedGaugeVariation
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceFamilyOperator
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

def kernelFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (t s : ℝ) : Operator Index H where
  component F := kernel (GaussGradedCompression.compression F) (gaugeReader z mu a) (gaugeReader z nu b) t s
  bounded := ⟨2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖, by positivity, fun F x =>
    ((kernel _ _ _ t s).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (kernel_bound _ _ _ (GaussGradedCompression.compression_selfAdjoint F) t s)
        (norm_nonneg x))⟩

def currentKernel (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (t s : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (kernelFamily z mu nu a b t s)

theorem finite_ordered_cutoff_return (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (cut : ℕ) (t s : ℝ) (F : Index) :
    sourceProjection * ordered (GaussGradedCompression.compression F+FullYSourceCutoffVolterra.cutoff cut)
      (gaugeReader z mu a) (gaugeReader z nu b) t s =
    sourceProjection * ordered (GaussGradedCompression.compression F)
      (gaugeReader z mu a) (gaugeReader z nu b) t s := by
  unfold ordered
  simp only [← mul_assoc]
  apply three_leg_return
  · exact finite_left_return cut (-t) F
  · exact finite_left_return cut (t-s) F
  · exact finite_left_return cut s F
  · exact time_commutes _ _ (GaussGradedCompression.compression_commutes F sourceLabel) (-t)
  · exact time_commutes _ _ (GaussGradedCompression.compression_commutes F sourceLabel) (t-s)
  · exact boundedMatrix_blocks (gaugeMatrix z mu a) (gaugeMatrix_preserves z mu a) sourceLabel
  · exact boundedMatrix_blocks (gaugeMatrix z nu b) (gaugeMatrix_preserves z nu b) sourceLabel

def fullKernel (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (t s : ℝ) (F : Index) : H →L[ℂ] H :=
  sourceProjection * kernel (GaussGradedCompression.compression F+FullYSourceCutoffVolterra.cutoff cut)
    (gaugeReader z mu a) (gaugeReader z nu b) t s

theorem fullKernel_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (t s : ℝ) (F : Index) :
    fullKernel z mu nu a b cut t s F = sourceProjection *
      kernel (GaussGradedCompression.compression F) (gaugeReader z mu a) (gaugeReader z nu b) t s := by
  simp only [fullKernel, kernel, mul_smul_comm, mul_sub, finite_ordered_cutoff_return]

def responseFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := finiteResponse (GaussGradedCompression.compression F)
    (gaugeReader z mu a) (gaugeReader z nu b) age frequency damping
  bounded := ⟨2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖/damping, by positivity, fun F x =>
    ((finiteResponse _ _ _ age frequency damping).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right
        (finiteResponse_bound _ _ _ (GaussGradedCompression.compression_selfAdjoint F) age frequency damping positive)
        (norm_nonneg x))⟩

def response (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (responseFamily z mu nu a b age frequency damping positive)

theorem response_bound (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (age frequency damping : ℝ) (positive : 0<damping) :
    ‖response z mu nu a b age frequency damping positive‖ ≤
      2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖/damping :=
  lift_bound sourceFilter _ _ (by positivity) (fun F =>
    finiteResponse_bound _ _ _ (GaussGradedCompression.compression_selfAdjoint F) age frequency damping positive)

def tailFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (age frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) : Operator Index H where
  component F := finiteResponse (GaussGradedCompression.compression F)
    (gaugeReader z mu a) (gaugeReader z nu b) age frequency damping -
      finiteTruncation (GaussGradedCompression.compression F)
        (gaugeReader z mu a) (gaugeReader z nu b) age frequency damping cutoff
  bounded := ⟨Real.exp (-damping*cutoff)/damping*(2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖),
    by positivity, fun F x =>
      ((finiteResponse (GaussGradedCompression.compression F) (gaugeReader z mu a) (gaugeReader z nu b)
          age frequency damping-finiteTruncation (GaussGradedCompression.compression F)
          (gaugeReader z mu a) (gaugeReader z nu b) age frequency damping cutoff).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right
          (finite_truncation_tail _ _ _ (GaussGradedCompression.compression_selfAdjoint F)
            age frequency damping cutoff positive future) (norm_nonneg x))⟩

theorem lifted_tail_bound (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (age frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) :
    ‖lift sourceFilter (tailFamily z mu nu a b age frequency damping cutoff positive future)‖ ≤
      Real.exp (-damping*cutoff)/damping*(2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖) :=
  lift_bound sourceFilter _ _ (by positivity) (fun F =>
    finite_truncation_tail _ _ _ (GaussGradedCompression.compression_selfAdjoint F)
      age frequency damping cutoff positive future)

def fullFiniteResponse (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (age frequency damping : ℝ) (F : Index) : H →L[ℂ] H :=
  ∫ lag : ℝ in Ioi 0, CanonicalGradedFrequency.weight frequency damping lag •
    fullKernel z mu nu a b cut (age+lag) age F

theorem fullFiniteResponse_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (F : Index) :
    fullFiniteResponse z mu nu a b cut age frequency damping F = sourceProjection *
      finiteResponse (GaussGradedCompression.compression F) (gaugeReader z mu a) (gaugeReader z nu b)
        age frequency damping := by
  let L := ContinuousLinearMap.mul ℂ (H →L[ℂ] H) sourceProjection
  have h := L.integral_comp_comm (integrand_integrable (GaussGradedCompression.compression F)
    (gaugeReader z mu a) (gaugeReader z nu b) (GaussGradedCompression.compression_selfAdjoint F)
    age frequency damping positive)
  change (∫ lag : ℝ in Ioi 0, sourceProjection *
    integrand (GaussGradedCompression.compression F) (gaugeReader z mu a) (gaugeReader z nu b)
      age frequency damping lag) = sourceProjection * finiteResponse (GaussGradedCompression.compression F)
        (gaugeReader z mu a) (gaugeReader z nu b) age frequency damping at h
  rw [fullFiniteResponse]
  simp_rw [fullKernel_return]
  simp only [integrand, mul_smul_comm] at h
  exact h

def fullResponseFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := fullFiniteResponse z mu nu a b cut age frequency damping F
  bounded := ⟨2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖/damping, by positivity, fun F x => by
    rw [fullFiniteResponse_return z mu nu a b cut age frequency damping positive F]
    change ‖sourceProjection (finiteResponse (GaussGradedCompression.compression F)
      (gaugeReader z mu a) (gaugeReader z nu b) age frequency damping x)‖ ≤ _
    exact (NativeHistoryGrade.piece_bound sourceLabel _).trans
      (((finiteResponse _ _ _ age frequency damping).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right
          (finiteResponse_bound _ _ _ (GaussGradedCompression.compression_selfAdjoint F)
            age frequency damping positive) (norm_nonneg x)))⟩

def fullResponse (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullResponseFamily z mu nu a b cut age frequency damping positive)

theorem fullResponse_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    fullResponse z mu nu a b cut age frequency damping positive =
      historyProjection * response z mu nu a b age frequency damping positive :=
  (lift_congr sourceFilter _
    (comp (constant sourceProjection) (responseFamily z mu nu a b age frequency damping positive))
    (fun F => fullFiniteResponse_return z mu nu a b cut age frequency damping positive F)).trans
      (lift_comp sourceFilter _ _)

theorem fullResponse_cutoff_independent (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (cut other : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    fullResponse z mu nu a b cut age frequency damping positive =
      fullResponse z mu nu a b other age frequency damping positive := by
  rw [fullResponse_return, fullResponse_return]

theorem fullResponse_bound (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    ‖fullResponse z mu nu a b cut age frequency damping positive‖ ≤
      2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖/damping := by
  rw [fullResponse_return]
  exact (norm_mul_le _ _).trans ((mul_le_mul CanonicalGradedFrequency.historyProjection_bound
    (response_bound z mu nu a b age frequency damping positive) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem fullResponse_source_readback (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (x y : H) :
    Tendsto (fun F : Index => inner ℂ x
      (fullFiniteResponse z mu nu a b cut age frequency damping F (sourceProjection y))) sourceFilter
      (𝓝 (inner ℂ (inclusion x)
        (fullResponse z mu nu a b cut age frequency damping positive (historyProjection (inclusion y))))) := by
  rw [historyProjection, GaussUnitaryHistory.reader_inclusion]
  change Tendsto _ _ (𝓝 (inner ℂ
    ((SourceFamilyHilbert.constant sourceFilter x) : HistorySpace)
    (lift sourceFilter (fullResponseFamily z mu nu a b cut age frequency damping positive)
      ((SourceFamilyHilbert.constant sourceFilter (sourceProjection y)) : HistorySpace))))
  rw [lift_coe, SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter x)
    (act sourceFilter (fullResponseFamily z mu nu a b cut age frequency damping positive)
      (SourceFamilyHilbert.constant sourceFilter (sourceProjection y)))

#print axioms derivative_kernel_integral
#print axioms finiteResponse_bound
#print axioms fullKernel_return
#print axioms fullResponse_source_readback
#print axioms fullResponse_cutoff_independent
#print axioms lifted_tail_bound

end LowEnergy.CanonicalGradedKernel
