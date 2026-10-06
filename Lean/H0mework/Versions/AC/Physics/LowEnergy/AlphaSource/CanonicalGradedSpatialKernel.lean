import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalGradedSpatial

/-! Physical momentum runs on every configuration-time leg. A Fourier pair
(-k,+k) gives the two intermediate momenta p+k and p-k. Integration is made
on each original finite family before its source-filter lift. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedSpatialKernel
open SourceFiniteUnitary CanonicalGradedSpatial CanonicalGradedSpatialSource
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace Interval

section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem continuous_time (C : E →L[ℂ] E) : Continuous (time C) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

private theorem time_bound (C : E →L[ℂ] E) (hc : IsSelfAdjoint C) (t : ℝ) :
    ‖time C t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [time_norm C hc, one_mul]

def ordered (C D A B : E →L[ℂ] E) (t s : ℝ) : E →L[ℂ] E :=
  time C (-t)*A*time D (t-s)*B*time C s

def kernel (C Cplus Cminus A B : E →L[ℂ] E) (t s : ℝ) : E →L[ℂ] E :=
  Complex.I • (ordered C Cminus B A s t-ordered C Cplus A B t s)

theorem kernel_zero_transfer (C A B : E →L[ℂ] E) (t s : ℝ) :
    kernel C C C A B t s=CanonicalGradedKernel.kernel C A B t s := rfl

theorem ordered_bound (C D A B : E →L[ℂ] E) (hc : IsSelfAdjoint C) (hd : IsSelfAdjoint D)
    (t s : ℝ) : ‖ordered C D A B t s‖ ≤ ‖A‖*‖B‖ := by
  have ha : ‖time C (-t)*A‖ ≤ ‖A‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (time_bound C hc (-t)) (norm_nonneg _)).trans_eq (one_mul _))
  have hb : ‖time C (-t)*A*time D (t-s)‖ ≤ ‖A‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul ha (time_bound D hd (t-s)) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))
  have hthird : ‖time C (-t)*A*time D (t-s)*B‖ ≤ ‖A‖*‖B‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  exact (norm_mul_le _ _).trans ((mul_le_mul hthird (time_bound C hc s)
    (norm_nonneg _) (by positivity)).trans_eq (mul_one _))

theorem kernel_bound (C Cplus Cminus A B : E →L[ℂ] E)
    (hc : IsSelfAdjoint C) (hp : IsSelfAdjoint Cplus) (hm : IsSelfAdjoint Cminus) (t s : ℝ) :
    ‖kernel C Cplus Cminus A B t s‖ ≤ 2*‖A‖*‖B‖ := by
  rw [kernel, norm_smul, Complex.norm_I, one_mul]
  exact (norm_sub_le _ _).trans
    ((add_le_add (ordered_bound C Cminus B A hc hm s t)
      (ordered_bound C Cplus A B hc hp t s)).trans_eq (by ring))

theorem ordered_continuous (C D A B : E →L[ℂ] E) :
    Continuous (fun p : ℝ × ℝ => ordered C D A B p.1 p.2) := by
  unfold ordered
  exact (((((continuous_time C).comp continuous_fst.neg).mul continuous_const).mul
    ((continuous_time D).comp (continuous_fst.sub continuous_snd))).mul continuous_const).mul
      ((continuous_time C).comp continuous_snd)

def integrand (C Cplus Cminus A B : E →L[ℂ] E) (age frequency damping lag : ℝ) : E →L[ℂ] E :=
  CanonicalGradedFrequency.weight frequency damping lag • kernel C Cplus Cminus A B (age+lag) age

theorem integrand_continuous (C Cplus Cminus A B : E →L[ℂ] E) (age frequency damping : ℝ) :
    Continuous (integrand C Cplus Cminus A B age frequency damping) := by
  have hfuture : Continuous (fun lag : ℝ => time C (age+lag)) :=
    (continuous_time C).comp (continuous_const.add continuous_id)
  have hback : Continuous (fun lag : ℝ => time C (-(age+lag))) :=
    (continuous_time C).comp (continuous_const.add continuous_id).neg
  have reverse : Continuous (fun lag : ℝ =>
      time C (-age)*B*time Cminus (age-(age+lag))*A*time C (age+lag)) :=
    (((continuous_const.mul continuous_const).mul
      ((continuous_time Cminus).comp (continuous_const.sub (continuous_const.add continuous_id)))).mul
        continuous_const).mul hfuture
  have forward : Continuous (fun lag : ℝ =>
      time C (-(age+lag))*A*time Cplus (age+lag-age)*B*time C age) :=
    (((hback.mul continuous_const).mul
      ((continuous_time Cplus).comp ((continuous_const.add continuous_id).sub continuous_const))).mul
        continuous_const).mul continuous_const
  exact (CanonicalGradedFrequency.weight_continuous frequency damping).smul
    ((reverse.sub forward).const_smul Complex.I)

theorem integrand_bound (C Cplus Cminus A B : E →L[ℂ] E)
    (hc : IsSelfAdjoint C) (hp : IsSelfAdjoint Cplus) (hm : IsSelfAdjoint Cminus)
    (age frequency damping lag : ℝ) :
    ‖integrand C Cplus Cminus A B age frequency damping lag‖ ≤
      Real.exp (-damping*lag)*(2*‖A‖*‖B‖) := by
  rw [integrand, norm_smul, CanonicalGradedFrequency.weight_norm]
  exact mul_le_mul_of_nonneg_left (kernel_bound C Cplus Cminus A B hc hp hm (age+lag) age) (Real.exp_pos _).le

theorem integrand_integrable (C Cplus Cminus A B : E →L[ℂ] E)
    (hc : IsSelfAdjoint C) (hp : IsSelfAdjoint Cplus) (hm : IsSelfAdjoint Cminus)
    (age frequency damping : ℝ) (positive : 0<damping) :
    IntegrableOn (integrand C Cplus Cminus A B age frequency damping) (Ioi 0) :=
  ((integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) 0).mul_const (2*‖A‖*‖B‖)).mono'
    (integrand_continuous C Cplus Cminus A B age frequency damping).aestronglyMeasurable
    (Filter.Eventually.of_forall (integrand_bound C Cplus Cminus A B hc hp hm age frequency damping))

def finiteResponse (C Cplus Cminus A B : E →L[ℂ] E) (age frequency damping : ℝ) : E →L[ℂ] E :=
  ∫ lag : ℝ in Ioi 0, integrand C Cplus Cminus A B age frequency damping lag

theorem finiteResponse_bound (C Cplus Cminus A B : E →L[ℂ] E)
    (hc : IsSelfAdjoint C) (hp : IsSelfAdjoint Cplus) (hm : IsSelfAdjoint Cminus)
    (age frequency damping : ℝ) (positive : 0<damping) :
    ‖finiteResponse C Cplus Cminus A B age frequency damping‖ ≤ 2*‖A‖*‖B‖/damping := by
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) 0).mul_const (2*‖A‖*‖B‖))
    (Filter.Eventually.of_forall (integrand_bound C Cplus Cminus A B hc hp hm age frequency damping))
  rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos positive) 0] at h
  simpa [finiteResponse, div_eq_mul_inv, mul_comm] using h

def finiteTruncation (C Cplus Cminus A B : E →L[ℂ] E) (age frequency damping cutoff : ℝ) : E →L[ℂ] E :=
  ∫ lag in (0 : ℝ)..cutoff, integrand C Cplus Cminus A B age frequency damping lag

theorem finite_truncation_tail (C Cplus Cminus A B : E →L[ℂ] E)
    (hc : IsSelfAdjoint C) (hp : IsSelfAdjoint Cplus) (hm : IsSelfAdjoint Cminus)
    (age frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) :
    ‖finiteResponse C Cplus Cminus A B age frequency damping-
      finiteTruncation C Cplus Cminus A B age frequency damping cutoff‖ ≤
      Real.exp (-damping*cutoff)/damping*(2*‖A‖*‖B‖) := by
  have hi := integrand_integrable C Cplus Cminus A B hc hp hm age frequency damping positive
  have ht := hi.mono_set (Ioi_subset_Ioi future)
  have split := intervalIntegral.integral_interval_add_Ioi hi ht
  change ‖(∫ lag in Ioi 0, integrand C Cplus Cminus A B age frequency damping lag)-
    (∫ lag in (0 : ℝ)..cutoff, integrand C Cplus Cminus A B age frequency damping lag)‖ ≤ _
  rw [← split, add_sub_cancel_left]
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) cutoff).mul_const (2*‖A‖*‖B‖))
    (Filter.Eventually.of_forall (integrand_bound C Cplus Cminus A B hc hp hm age frequency damping))
  rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos positive) cutoff] at h
  simpa only [neg_mul, neg_div_neg_eq] using h

end Finite

open GaussCoreHilbert CanonicalGradedCurrent SourceFamilyOperator
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

structure NativeCurrent where
  localizer : Localizer
  component : Component
  generator : NativeLie

def current (A : NativeCurrent) : H →L[ℂ] H :=
  CanonicalGradedLocalCurrent.localReader A.localizer A.component A.generator

theorem current_preserves (A : NativeCurrent) : Commute sourceProjection (current A) :=
  CanonicalGradedLocalCurrent.localReader_blocks A.localizer A.component A.generator sourceLabel

def finiteKernel (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (t s : ℝ) (F : Index) : H →L[ℂ] H :=
  kernel (finiteHamiltonian phi p F) (finiteHamiltonian phi (p+k) F)
    (finiteHamiltonian phi (p-k) F) (current A) (current B) t s

theorem finiteKernel_bound (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (t s : ℝ) (F : Index) : ‖finiteKernel phi p k A B t s F‖ ≤ 2*‖current A‖*‖current B‖ :=
  kernel_bound _ _ _ _ _ (finiteHamiltonian_selfAdjoint phi p F)
    (finiteHamiltonian_selfAdjoint phi (p+k) F) (finiteHamiltonian_selfAdjoint phi (p-k) F) t s

theorem finiteKernel_zero_transfer (phi : Localizer) (p : PhysicalMomentum) (A B : NativeCurrent)
    (t s : ℝ) (F : Index) :
    finiteKernel phi p 0 A B t s F=CanonicalGradedKernel.kernel (finiteHamiltonian phi p F)
      (current A) (current B) t s := by
  simp only [finiteKernel, add_zero, sub_zero, kernel_zero_transfer]

def kernelFamily (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent) (t s : ℝ) : Operator Index H where
  component F := finiteKernel phi p k A B t s F
  bounded := ⟨2*‖current A‖*‖current B‖, by positivity, fun F x =>
    ((finiteKernel phi p k A B t s F).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (finiteKernel_bound phi p k A B t s F) (norm_nonneg x))⟩

def currentKernel (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent) (t s : ℝ) :
    HistorySpace →L[ℂ] HistorySpace := lift sourceFilter (kernelFamily phi p k A B t s)

def responseFamily (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := finiteResponse (finiteHamiltonian phi p F) (finiteHamiltonian phi (p+k) F)
    (finiteHamiltonian phi (p-k) F) (current A) (current B) age frequency damping
  bounded := ⟨2*‖current A‖*‖current B‖/damping, by positivity, fun F x =>
    ((finiteResponse _ _ _ _ _ age frequency damping).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (finiteResponse_bound _ _ _ _ _
        (finiteHamiltonian_selfAdjoint phi p F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
        (finiteHamiltonian_selfAdjoint phi (p-k) F) age frequency damping positive) (norm_nonneg x))⟩

def response (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (responseFamily phi p k A B age frequency damping positive)

theorem response_bound (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping : ℝ) (positive : 0<damping) :
    ‖response phi p k A B age frequency damping positive‖ ≤ 2*‖current A‖*‖current B‖/damping :=
  CanonicalGradedVariation.lift_bound sourceFilter _ _ (by positivity) (fun F => finiteResponse_bound _ _ _ _ _
    (finiteHamiltonian_selfAdjoint phi p F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
    (finiteHamiltonian_selfAdjoint phi (p-k) F) age frequency damping positive)

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


theorem finite_ordered_cutoff_return (phi : Localizer) (p middle : PhysicalMomentum)
    (A B : NativeCurrent) (cut : ℕ) (t s : ℝ) (F : Index) :
    sourceProjection*ordered (finiteHamiltonian phi p F+FullYSourceCutoffVolterra.cutoff cut)
      (finiteHamiltonian phi middle F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s =
    sourceProjection*ordered (finiteHamiltonian phi p F) (finiteHamiltonian phi middle F)
      (current A) (current B) t s := by
  unfold ordered
  simp only [← mul_assoc]
  apply three_leg_return
  · exact full_finite_return phi p cut (-t) F
  · exact full_finite_return phi middle cut (t-s) F
  · exact full_finite_return phi p cut s F
  · exact time_commutes _ _ (finiteHamiltonian_blocks phi p F sourceLabel) (-t)
  · exact time_commutes _ _ (finiteHamiltonian_blocks phi middle F sourceLabel) (t-s)
  · exact current_preserves A
  · exact current_preserves B

def fullFiniteKernel (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) : H →L[ℂ] H :=
  sourceProjection*kernel (finiteHamiltonian phi p F+FullYSourceCutoffVolterra.cutoff cut)
    (finiteHamiltonian phi (p+k) F+FullYSourceCutoffVolterra.cutoff cut)
    (finiteHamiltonian phi (p-k) F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s

theorem fullFiniteKernel_return (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) :
    fullFiniteKernel phi p k A B cut t s F=sourceProjection*finiteKernel phi p k A B t s F := by
  simp only [fullFiniteKernel, finiteKernel, kernel, mul_smul_comm, mul_sub, finite_ordered_cutoff_return]

def fullFiniteResponse (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (F : Index) : H →L[ℂ] H :=
  ∫ lag : ℝ in Ioi 0, CanonicalGradedFrequency.weight frequency damping lag •
    fullFiniteKernel phi p k A B cut (age+lag) age F

theorem fullFiniteResponse_return (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (F : Index) :
    fullFiniteResponse phi p k A B cut age frequency damping F = sourceProjection*
      finiteResponse (finiteHamiltonian phi p F) (finiteHamiltonian phi (p+k) F)
        (finiteHamiltonian phi (p-k) F) (current A) (current B) age frequency damping := by
  let L := ContinuousLinearMap.mul ℂ (H →L[ℂ] H) sourceProjection
  have h := L.integral_comp_comm (integrand_integrable _ _ _ (current A) (current B)
    (finiteHamiltonian_selfAdjoint phi p F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
    (finiteHamiltonian_selfAdjoint phi (p-k) F) age frequency damping positive)
  change (∫ lag : ℝ in Ioi 0, sourceProjection*integrand (finiteHamiltonian phi p F)
    (finiteHamiltonian phi (p+k) F) (finiteHamiltonian phi (p-k) F) (current A) (current B)
    age frequency damping lag) = sourceProjection*finiteResponse (finiteHamiltonian phi p F)
      (finiteHamiltonian phi (p+k) F) (finiteHamiltonian phi (p-k) F) (current A) (current B)
      age frequency damping at h
  rw [fullFiniteResponse]
  simp_rw [fullFiniteKernel_return]
  simp only [integrand, finiteKernel, mul_smul_comm] at h ⊢
  exact h

def fullResponseFamily (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := fullFiniteResponse phi p k A B cut age frequency damping F
  bounded := ⟨2*‖current A‖*‖current B‖/damping, by positivity, fun F x => by
    rw [fullFiniteResponse_return phi p k A B cut age frequency damping positive F]
    change ‖sourceProjection (finiteResponse _ _ _ _ _ age frequency damping x)‖ ≤ _
    exact (NativeHistoryGrade.piece_bound sourceLabel _).trans
      (((finiteResponse _ _ _ _ _ age frequency damping).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (finiteResponse_bound _ _ _ _ _
          (finiteHamiltonian_selfAdjoint phi p F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
          (finiteHamiltonian_selfAdjoint phi (p-k) F) age frequency damping positive) (norm_nonneg x)))⟩

def fullResponse (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullResponseFamily phi p k A B cut age frequency damping positive)

theorem fullResponse_return (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    fullResponse phi p k A B cut age frequency damping positive =
      historyProjection*response phi p k A B age frequency damping positive :=
  (lift_congr sourceFilter _ (comp (constant sourceProjection) (responseFamily phi p k A B age frequency damping positive))
    (fun F => fullFiniteResponse_return phi p k A B cut age frequency damping positive F)).trans (lift_comp sourceFilter _ _)

theorem fullResponse_cutoff_independent (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (cut other : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    fullResponse phi p k A B cut age frequency damping positive =
      fullResponse phi p k A B other age frequency damping positive := by
  rw [fullResponse_return, fullResponse_return]

theorem fullResponse_source_readback (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (x y : H) :
    Tendsto (fun F : Index => inner ℂ x
      (fullFiniteResponse phi p k A B cut age frequency damping F (sourceProjection y))) sourceFilter
      (𝓝 (inner ℂ (inclusion x)
        (fullResponse phi p k A B cut age frequency damping positive (historyProjection (inclusion y))))) := by
  rw [historyProjection, GaussUnitaryHistory.reader_inclusion]
  change Tendsto _ _ (𝓝 (inner ℂ
    ((SourceFamilyHilbert.constant sourceFilter x) : HistorySpace)
    (lift sourceFilter (fullResponseFamily phi p k A B cut age frequency damping positive)
      ((SourceFamilyHilbert.constant sourceFilter (sourceProjection y)) : HistorySpace))))
  rw [lift_coe, SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter x)
    (act sourceFilter (fullResponseFamily phi p k A B cut age frequency damping positive)
      (SourceFamilyHilbert.constant sourceFilter (sourceProjection y)))

#print axioms finite_truncation_tail
#print axioms fullFiniteKernel_return
#print axioms fullResponse_return
#print axioms fullResponse_source_readback
end LowEnergy.CanonicalGradedSpatialKernel
