import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalGradedSpatialKernel

/-! Independent physical Fourier transfers keep the two exterior momenta.
The pointwise Fourier readback fixes every intermediate momentum before the
same source-family completion or any preparation is consumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedBilocal
open SourceFiniteUnitary CanonicalGradedVariation
open CanonicalGradedSpatialSource CanonicalGradedSpatial
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

def ordered (Cout Cin Cmiddle A B : E →L[ℂ] E) (t s : ℝ) : E →L[ℂ] E :=
  time Cout (-t)*A*time Cmiddle (t-s)*B*time Cin s

def kernel (Cout Cin Cforward Creverse A B : E →L[ℂ] E) (t s : ℝ) : E →L[ℂ] E :=
  Complex.I • (ordered Cout Cin Creverse B A s t-ordered Cout Cin Cforward A B t s)

theorem same_exterior (C Cforward Creverse A B : E →L[ℂ] E) (t s : ℝ) :
    kernel C C Cforward Creverse A B t s =
      CanonicalGradedSpatialKernel.kernel C Cforward Creverse A B t s := rfl

theorem ordered_bound (Cout Cin Cmiddle A B : E →L[ℂ] E)
    (ho : IsSelfAdjoint Cout) (hi : IsSelfAdjoint Cin) (hm : IsSelfAdjoint Cmiddle)
    (t s : ℝ) : ‖ordered Cout Cin Cmiddle A B t s‖ ≤ ‖A‖*‖B‖ := by
  have first : ‖time Cout (-t)*A‖ ≤ ‖A‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (time_bound Cout ho (-t))
      (norm_nonneg _)).trans_eq (one_mul _))
  have middle : ‖time Cout (-t)*A*time Cmiddle (t-s)‖ ≤ ‖A‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul first (time_bound Cmiddle hm (t-s))
      (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))
  have second : ‖time Cout (-t)*A*time Cmiddle (t-s)*B‖ ≤ ‖A‖*‖B‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right middle (norm_nonneg _))
  exact (norm_mul_le _ _).trans ((mul_le_mul second (time_bound Cin hi s)
    (norm_nonneg _) (by positivity)).trans_eq (mul_one _))

theorem kernel_bound (Cout Cin Cforward Creverse A B : E →L[ℂ] E)
    (ho : IsSelfAdjoint Cout) (hi : IsSelfAdjoint Cin)
    (hf : IsSelfAdjoint Cforward) (hr : IsSelfAdjoint Creverse) (t s : ℝ) :
    ‖kernel Cout Cin Cforward Creverse A B t s‖ ≤ 2*‖A‖*‖B‖ := by
  rw [kernel, norm_smul, Complex.norm_I, one_mul]
  exact (norm_sub_le _ _).trans ((add_le_add
    (ordered_bound Cout Cin Creverse B A ho hi hr s t)
    (ordered_bound Cout Cin Cforward A B ho hi hf t s)).trans_eq (by ring))

def integrand (Cout Cin Cforward Creverse A B : E →L[ℂ] E)
    (age frequency damping lag : ℝ) : E →L[ℂ] E :=
  CanonicalGradedFrequency.weight frequency damping lag •
    kernel Cout Cin Cforward Creverse A B (age+lag) age

theorem integrand_continuous (Cout Cin Cforward Creverse A B : E →L[ℂ] E)
    (age frequency damping : ℝ) :
    Continuous (integrand Cout Cin Cforward Creverse A B age frequency damping) := by
  have hfuture : Continuous (fun lag : ℝ => time Cin (age+lag)) :=
    (continuous_time Cin).comp (continuous_const.add continuous_id)
  have hback : Continuous (fun lag : ℝ => time Cout (-(age+lag))) :=
    (continuous_time Cout).comp (continuous_const.add continuous_id).neg
  have reverse : Continuous (fun lag : ℝ =>
      time Cout (-age)*B*time Creverse (age-(age+lag))*A*time Cin (age+lag)) :=
    (((continuous_const.mul continuous_const).mul
      ((continuous_time Creverse).comp (continuous_const.sub (continuous_const.add continuous_id)))).mul
        continuous_const).mul hfuture
  have forward : Continuous (fun lag : ℝ =>
      time Cout (-(age+lag))*A*time Cforward (age+lag-age)*B*time Cin age) :=
    (((hback.mul continuous_const).mul
      ((continuous_time Cforward).comp ((continuous_const.add continuous_id).sub continuous_const))).mul
        continuous_const).mul continuous_const
  exact (CanonicalGradedFrequency.weight_continuous frequency damping).smul
    ((reverse.sub forward).const_smul Complex.I)

theorem integrand_bound (Cout Cin Cforward Creverse A B : E →L[ℂ] E)
    (ho : IsSelfAdjoint Cout) (hi : IsSelfAdjoint Cin)
    (hf : IsSelfAdjoint Cforward) (hr : IsSelfAdjoint Creverse)
    (age frequency damping lag : ℝ) :
    ‖integrand Cout Cin Cforward Creverse A B age frequency damping lag‖ ≤
      Real.exp (-damping*lag)*(2*‖A‖*‖B‖) := by
  rw [integrand, norm_smul, CanonicalGradedFrequency.weight_norm]
  exact mul_le_mul_of_nonneg_left
    (kernel_bound Cout Cin Cforward Creverse A B ho hi hf hr (age+lag) age) (Real.exp_pos _).le

theorem integrand_integrable (Cout Cin Cforward Creverse A B : E →L[ℂ] E)
    (ho : IsSelfAdjoint Cout) (hi : IsSelfAdjoint Cin)
    (hf : IsSelfAdjoint Cforward) (hr : IsSelfAdjoint Creverse)
    (age frequency damping : ℝ) (positive : 0<damping) :
    IntegrableOn (integrand Cout Cin Cforward Creverse A B age frequency damping) (Ioi 0) :=
  ((integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) 0).mul_const (2*‖A‖*‖B‖)).mono'
    (integrand_continuous Cout Cin Cforward Creverse A B age frequency damping).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (integrand_bound Cout Cin Cforward Creverse A B ho hi hf hr age frequency damping))

def finiteResponse (Cout Cin Cforward Creverse A B : E →L[ℂ] E)
    (age frequency damping : ℝ) : E →L[ℂ] E :=
  ∫ lag : ℝ in Ioi 0, integrand Cout Cin Cforward Creverse A B age frequency damping lag

theorem finiteResponse_bound (Cout Cin Cforward Creverse A B : E →L[ℂ] E)
    (ho : IsSelfAdjoint Cout) (hi : IsSelfAdjoint Cin)
    (hf : IsSelfAdjoint Cforward) (hr : IsSelfAdjoint Creverse)
    (age frequency damping : ℝ) (positive : 0<damping) :
    ‖finiteResponse Cout Cin Cforward Creverse A B age frequency damping‖ ≤
      2*‖A‖*‖B‖/damping := by
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) 0).mul_const (2*‖A‖*‖B‖))
    (Filter.Eventually.of_forall
      (integrand_bound Cout Cin Cforward Creverse A B ho hi hf hr age frequency damping))
  rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos positive) 0] at h
  simpa [finiteResponse, div_eq_mul_inv, mul_comm] using h

def finiteTruncation (Cout Cin Cforward Creverse A B : E →L[ℂ] E)
    (age frequency damping cutoff : ℝ) : E →L[ℂ] E :=
  ∫ lag in (0 : ℝ)..cutoff, integrand Cout Cin Cforward Creverse A B age frequency damping lag

theorem finite_truncation_tail (Cout Cin Cforward Creverse A B : E →L[ℂ] E)
    (ho : IsSelfAdjoint Cout) (hi : IsSelfAdjoint Cin)
    (hf : IsSelfAdjoint Cforward) (hr : IsSelfAdjoint Creverse)
    (age frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) :
    ‖finiteResponse Cout Cin Cforward Creverse A B age frequency damping-
      finiteTruncation Cout Cin Cforward Creverse A B age frequency damping cutoff‖ ≤
      Real.exp (-damping*cutoff)/damping*(2*‖A‖*‖B‖) := by
  have hi := integrand_integrable Cout Cin Cforward Creverse A B ho hi hf hr
    age frequency damping positive
  have ht := hi.mono_set (Ioi_subset_Ioi future)
  have split := intervalIntegral.integral_interval_add_Ioi hi ht
  change ‖(∫ lag in Ioi 0, integrand Cout Cin Cforward Creverse A B age frequency damping lag)-
    (∫ lag in (0 : ℝ)..cutoff, integrand Cout Cin Cforward Creverse A B age frequency damping lag)‖ ≤ _
  rw [← split, add_sub_cancel_left]
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) cutoff).mul_const (2*‖A‖*‖B‖))
    (Filter.Eventually.of_forall
      (integrand_bound Cout Cin Cforward Creverse A B ho
        (by assumption) hf hr age frequency damping))
  rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos positive) cutoff] at h
  simpa only [neg_mul, neg_div_neg_eq] using h

end Finite

open GaussCoreHilbert CanonicalGradedCurrent SourceFamilyOperator
open CanonicalGradedSpatialKernel (NativeCurrent current current_preserves)
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

/-- This raw Fourier section is a calculation carrier, not a chosen state. -/
abbrev FourierSection := PhysicalMomentum → H

def fourierTime (phi : Localizer) (F : Index) (t : ℝ) (f : FourierSection) : FourierSection :=
  fun q => time (finiteHamiltonian phi q F) t (f q)

def fourierCurrent (A : NativeCurrent) (k : PhysicalMomentum) (f : FourierSection) : FourierSection :=
  fun q => current A (f (q-k))

theorem fourierTime_add (phi : Localizer) (F : Index) (t s : ℝ) (f : FourierSection) :
    fourierTime phi F t (fourierTime phi F s f)=fourierTime phi F (t+s) f := by
  funext q
  change time (finiteHamiltonian phi q F) t (time (finiteHamiltonian phi q F) s (f q)) = _
  rw [fourierTime, time_add, mul_apply_eq_comp]

def fourierHeisenberg (phi : Localizer) (F : Index) (A : NativeCurrent)
    (k : PhysicalMomentum) (t : ℝ) (f : FourierSection) : FourierSection :=
  fourierTime phi F (-t) (fourierCurrent A k (fourierTime phi F t f))

def fourierWord (phi : Localizer) (F : Index) (A B : NativeCurrent)
    (k ell : PhysicalMomentum) (t s : ℝ) (f : FourierSection) : FourierSection :=
  fourierTime phi F (-t) (fourierCurrent A k
    (fourierTime phi F (t-s) (fourierCurrent B ell (fourierTime phi F s f))))

theorem fourierWord_read (phi : Localizer) (F : Index) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (t s : ℝ) (f : FourierSection) :
    fourierWord phi F A B k ell t s f (p+k+ell) =
      ordered (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
        (finiteHamiltonian phi (p+ell) F) (current A) (current B) t s (f p) := by
  have first : p+k+ell-k=p+ell := by abel
  simp only [fourierWord, fourierTime, fourierCurrent, first, add_sub_cancel_right,
    ordered, mul_apply_eq_comp]

theorem fourierWord_heisenberg (phi : Localizer) (F : Index) (A B : NativeCurrent)
    (k ell : PhysicalMomentum) (t s : ℝ) (f : FourierSection) :
    fourierWord phi F A B k ell t s f =
      fourierHeisenberg phi F A k t (fourierHeisenberg phi F B ell s f) := by
  simp only [fourierHeisenberg, fourierTime_add, ← sub_eq_add_neg, fourierWord]

def finiteKernel (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (t s : ℝ) (F : Index) : H →L[ℂ] H :=
  kernel (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
    (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F) (current A) (current B) t s

theorem finiteKernel_fourier_read (phi : Localizer) (F : Index) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (t s : ℝ) (f : FourierSection) :
    finiteKernel phi p k ell A B t s F (f p) = Complex.I •
      (fourierWord phi F B A ell k s t f (p+k+ell)-fourierWord phi F A B k ell t s f (p+k+ell)) := by
  have exchange : p+ell+k=p+k+ell := by abel
  have reverse := fourierWord_read phi F B A p ell k s t f
  rw [exchange] at reverse
  rw [reverse, fourierWord_read]
  rfl

theorem finiteKernel_opposite (phi : Localizer) (p k : PhysicalMomentum) (A B : NativeCurrent)
    (t s : ℝ) (F : Index) :
    finiteKernel phi p (-k) k A B t s F =
      CanonicalGradedSpatialKernel.finiteKernel phi p k A B t s F := by
  have exterior : p+-k+k=p := by abel
  rw [finiteKernel, exterior]
  simp only [← sub_eq_add_neg, same_exterior,
    CanonicalGradedSpatialKernel.finiteKernel]

theorem finiteKernel_bound (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (t s : ℝ) (F : Index) : ‖finiteKernel phi p k ell A B t s F‖ ≤ 2*‖current A‖*‖current B‖ :=
  kernel_bound _ _ _ _ _ _ (finiteHamiltonian_selfAdjoint phi (p+k+ell) F)
    (finiteHamiltonian_selfAdjoint phi p F) (finiteHamiltonian_selfAdjoint phi (p+ell) F)
    (finiteHamiltonian_selfAdjoint phi (p+k) F) t s

def responseFamily (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := finiteResponse (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
    (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F)
    (current A) (current B) age frequency damping
  bounded := ⟨2*‖current A‖*‖current B‖/damping, by positivity, fun F x =>
    ((finiteResponse _ _ _ _ _ _ age frequency damping).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (finiteResponse_bound _ _ _ _ _ _
        (finiteHamiltonian_selfAdjoint phi (p+k+ell) F) (finiteHamiltonian_selfAdjoint phi p F)
        (finiteHamiltonian_selfAdjoint phi (p+ell) F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
        age frequency damping positive) (norm_nonneg x))⟩

def response (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (responseFamily phi p k ell A B age frequency damping positive)

theorem response_bound (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping : ℝ) (positive : 0<damping) :
    ‖response phi p k ell A B age frequency damping positive‖ ≤ 2*‖current A‖*‖current B‖/damping :=
  lift_bound sourceFilter _ _ (by positivity) (fun F => finiteResponse_bound _ _ _ _ _ _
    (finiteHamiltonian_selfAdjoint phi (p+k+ell) F) (finiteHamiltonian_selfAdjoint phi p F)
    (finiteHamiltonian_selfAdjoint phi (p+ell) F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
    age frequency damping positive)

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

theorem finite_ordered_cutoff_return (phi : Localizer) (out input middle : PhysicalMomentum)
    (A B : NativeCurrent) (cut : ℕ) (t s : ℝ) (F : Index) :
    sourceProjection*ordered (finiteHamiltonian phi out F+FullYSourceCutoffVolterra.cutoff cut)
      (finiteHamiltonian phi input F+FullYSourceCutoffVolterra.cutoff cut)
      (finiteHamiltonian phi middle F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s =
    sourceProjection*ordered (finiteHamiltonian phi out F) (finiteHamiltonian phi input F)
      (finiteHamiltonian phi middle F) (current A) (current B) t s := by
  unfold ordered
  simp only [← mul_assoc]
  apply three_leg_return
  · exact full_finite_return phi out cut (-t) F
  · exact full_finite_return phi middle cut (t-s) F
  · exact full_finite_return phi input cut s F
  · exact time_commutes _ _ (finiteHamiltonian_blocks phi out F sourceLabel) (-t)
  · exact time_commutes _ _ (finiteHamiltonian_blocks phi middle F sourceLabel) (t-s)
  · exact current_preserves A
  · exact current_preserves B

def fullFiniteKernel (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) : H →L[ℂ] H :=
  sourceProjection*kernel (finiteHamiltonian phi (p+k+ell) F+FullYSourceCutoffVolterra.cutoff cut)
    (finiteHamiltonian phi p F+FullYSourceCutoffVolterra.cutoff cut)
    (finiteHamiltonian phi (p+ell) F+FullYSourceCutoffVolterra.cutoff cut)
    (finiteHamiltonian phi (p+k) F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s

theorem fullFiniteKernel_return (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) :
    fullFiniteKernel phi p k ell A B cut t s F=sourceProjection*finiteKernel phi p k ell A B t s F := by
  simp only [fullFiniteKernel, finiteKernel, kernel, mul_smul_comm, mul_sub, finite_ordered_cutoff_return]

def fullFiniteResponse (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (F : Index) : H →L[ℂ] H :=
  ∫ lag : ℝ in Ioi 0, CanonicalGradedFrequency.weight frequency damping lag •
    fullFiniteKernel phi p k ell A B cut (age+lag) age F

theorem fullFiniteResponse_return (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (F : Index) :
    fullFiniteResponse phi p k ell A B cut age frequency damping F = sourceProjection*
      finiteResponse (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
        (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F)
        (current A) (current B) age frequency damping := by
  let L := ContinuousLinearMap.mul ℂ (H →L[ℂ] H) sourceProjection
  have h := L.integral_comp_comm (integrand_integrable _ _ _ _ (current A) (current B)
    (finiteHamiltonian_selfAdjoint phi (p+k+ell) F) (finiteHamiltonian_selfAdjoint phi p F)
    (finiteHamiltonian_selfAdjoint phi (p+ell) F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
    age frequency damping positive)
  change (∫ lag : ℝ in Ioi 0, sourceProjection*integrand (finiteHamiltonian phi (p+k+ell) F)
    (finiteHamiltonian phi p F) (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F)
    (current A) (current B) age frequency damping lag) = sourceProjection*
      finiteResponse (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
        (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F)
        (current A) (current B) age frequency damping at h
  rw [fullFiniteResponse]
  simp_rw [fullFiniteKernel_return]
  simp only [integrand, finiteKernel, mul_smul_comm] at h ⊢
  exact h

def fullResponseFamily (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := fullFiniteResponse phi p k ell A B cut age frequency damping F
  bounded := ⟨2*‖current A‖*‖current B‖/damping, by positivity, fun F x => by
    rw [fullFiniteResponse_return phi p k ell A B cut age frequency damping positive F]
    change ‖sourceProjection (finiteResponse _ _ _ _ _ _ age frequency damping x)‖ ≤ _
    exact (NativeHistoryGrade.piece_bound sourceLabel _).trans
      (((finiteResponse _ _ _ _ _ _ age frequency damping).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (finiteResponse_bound _ _ _ _ _ _
          (finiteHamiltonian_selfAdjoint phi (p+k+ell) F) (finiteHamiltonian_selfAdjoint phi p F)
          (finiteHamiltonian_selfAdjoint phi (p+ell) F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
          age frequency damping positive) (norm_nonneg x)))⟩

def fullResponse (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullResponseFamily phi p k ell A B cut age frequency damping positive)

theorem fullResponse_return (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    fullResponse phi p k ell A B cut age frequency damping positive =
      historyProjection*response phi p k ell A B age frequency damping positive :=
  (lift_congr sourceFilter _ (comp (constant sourceProjection)
    (responseFamily phi p k ell A B age frequency damping positive))
    (fun F => fullFiniteResponse_return phi p k ell A B cut age frequency damping positive F)).trans
      (lift_comp sourceFilter _ _)

theorem fullResponse_cutoff_independent (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut other : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    fullResponse phi p k ell A B cut age frequency damping positive =
      fullResponse phi p k ell A B other age frequency damping positive := by
  rw [fullResponse_return, fullResponse_return]

theorem fullResponse_source_readback (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (x y : FourierSection) :
    Tendsto (fun F : Index => inner ℂ (x (p+k+ell))
      (fullFiniteResponse phi p k ell A B cut age frequency damping F (sourceProjection (y p)))) sourceFilter
      (𝓝 (inner ℂ (inclusion (x (p+k+ell)))
        (fullResponse phi p k ell A B cut age frequency damping positive
          (historyProjection (inclusion (y p)))))) := by
  rw [historyProjection, GaussUnitaryHistory.reader_inclusion]
  change Tendsto _ _ (𝓝 (inner ℂ
    ((SourceFamilyHilbert.constant sourceFilter (x (p+k+ell))) : HistorySpace)
    (lift sourceFilter (fullResponseFamily phi p k ell A B cut age frequency damping positive)
      ((SourceFamilyHilbert.constant sourceFilter (sourceProjection (y p))) : HistorySpace))))
  rw [lift_coe, SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto sourceFilter
    (SourceFamilyHilbert.constant sourceFilter (x (p+k+ell)))
    (act sourceFilter (fullResponseFamily phi p k ell A B cut age frequency damping positive)
      (SourceFamilyHilbert.constant sourceFilter (sourceProjection (y p))))

end LowEnergy.CanonicalGradedBilocal
