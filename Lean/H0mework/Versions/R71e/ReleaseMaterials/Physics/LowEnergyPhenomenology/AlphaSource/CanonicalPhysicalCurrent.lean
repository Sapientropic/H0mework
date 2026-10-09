import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPhysicalSpatial
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGradedBilocal

/-! The actual unlocalized physical propagation consumes the original bounded
native currents. Independent physical transfers and the whole Yukawa time
word are retained before the same completion and source pairing. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPhysicalCurrent
open GaussCoreHilbert GaussDiagonalHistory SourceFamilyOperator
open CanonicalPhysicalSpatial CanonicalGradedSpatialSource
open CanonicalGradedSpatialKernel (NativeCurrent current current_preserves)
open CanonicalGradedBilocal (ordered kernel finiteResponse finiteResponse_bound integrand_integrable)
open CanonicalGradedCurrent (sourceProjection sourceLabel historyProjection)
open GaussUnitaryHistory (HistorySpace Index sourceFilter inclusion reader)
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace Interval
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

abbrev FourierSection := PhysicalMomentum → H

def fourierTime (F : Index) (t : ℝ) (f : FourierSection) : FourierSection :=
  fun p => SourceFiniteUnitary.time (compression p F) t (f p)

def fourierCurrent (A : NativeCurrent) (k : PhysicalMomentum) (f : FourierSection) : FourierSection :=
  fun p => current A (f (p-k))

def fourierWord (F : Index) (A B : NativeCurrent) (k ell : PhysicalMomentum)
    (t s : ℝ) (f : FourierSection) : FourierSection :=
  fourierTime F (-t) (fourierCurrent A k (fourierTime F (t-s) (fourierCurrent B ell (fourierTime F s f))))

theorem fourierWord_read (F : Index) (A B : NativeCurrent) (p k ell : PhysicalMomentum)
    (t s : ℝ) (f : FourierSection) :
    fourierWord F A B k ell t s f (p+k+ell) =
      ordered (compression (p+k+ell) F) (compression p F) (compression (p+ell) F)
        (current A) (current B) t s (f p) := by
  have route : p+k+ell-k=p+ell := by abel
  simp only [fourierWord, fourierTime, fourierCurrent, route, add_sub_cancel_right, ordered, mul_apply_eq_comp]

def finiteKernel (p k ell : PhysicalMomentum) (A B : NativeCurrent) (t s : ℝ) (F : Index) : H →L[ℂ] H :=
  kernel (compression (p+k+ell) F) (compression p F) (compression (p+ell) F) (compression (p+k) F)
    (current A) (current B) t s

theorem finiteKernel_fourier (F : Index) (A B : NativeCurrent) (p k ell : PhysicalMomentum)
    (t s : ℝ) (f : FourierSection) :
    finiteKernel p k ell A B t s F (f p)=Complex.I •
      (fourierWord F B A ell k s t f (p+k+ell)-fourierWord F A B k ell t s f (p+k+ell)) := by
  have exchange : p+ell+k=p+k+ell := by abel
  have reverse := fourierWord_read F B A p ell k s t f
  rw [exchange] at reverse
  rw [reverse, fourierWord_read]
  rfl

theorem finiteKernel_original (A B : NativeCurrent) (t s : ℝ) (F : Index) :
    finiteKernel 0 0 0 A B t s F=CanonicalGradedKernel.kernel (GaussGradedCompression.compression F)
      (current A) (current B) t s := by
  simp only [finiteKernel, add_zero, compression_zero, CanonicalGradedBilocal.same_exterior,
    CanonicalGradedSpatialKernel.kernel_zero_transfer]

def responseFamily (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := finiteResponse (compression (p+k+ell) F) (compression p F)
    (compression (p+ell) F) (compression (p+k) F) (current A) (current B) age frequency damping
  bounded := ⟨2*‖current A‖*‖current B‖/damping, by positivity, fun F x =>
    ((finiteResponse _ _ _ _ _ _ age frequency damping).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (finiteResponse_bound _ _ _ _ _ _
        (compression_selfAdjoint (p+k+ell) F) (compression_selfAdjoint p F)
        (compression_selfAdjoint (p+ell) F) (compression_selfAdjoint (p+k) F)
        age frequency damping positive) (norm_nonneg x))⟩

def response (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (responseFamily p k ell A B age frequency damping positive)

theorem response_bound (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping : ℝ) (positive : 0<damping) :
    ‖response p k ell A B age frequency damping positive‖ ≤ 2*‖current A‖*‖current B‖/damping :=
  CanonicalGradedVariation.lift_bound sourceFilter _ _ (by positivity) (fun F =>
    finiteResponse_bound _ _ _ _ _ _ (compression_selfAdjoint (p+k+ell) F) (compression_selfAdjoint p F)
      (compression_selfAdjoint (p+ell) F) (compression_selfAdjoint (p+k) F)
      age frequency damping positive)

theorem finite_response_tail (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) (F : Index) :
    ‖finiteResponse (compression (p+k+ell) F) (compression p F) (compression (p+ell) F)
        (compression (p+k) F) (current A) (current B) age frequency damping-
      CanonicalGradedBilocal.finiteTruncation (compression (p+k+ell) F) (compression p F)
        (compression (p+ell) F) (compression (p+k) F) (current A) (current B) age frequency damping cutoff‖ ≤
      Real.exp (-damping*cutoff)/damping*(2*‖current A‖*‖current B‖) :=
  CanonicalGradedBilocal.finite_truncation_tail _ _ _ _ _ _
    (compression_selfAdjoint (p+k+ell) F) (compression_selfAdjoint p F)
    (compression_selfAdjoint (p+ell) F) (compression_selfAdjoint (p+k) F)
    age frequency damping cutoff positive future

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

theorem finite_ordered_cutoff_return (out input middle : PhysicalMomentum)
    (A B : NativeCurrent) (cut : ℕ) (t s : ℝ) (F : Index) :
    sourceProjection*ordered (compression out F+FullYSourceCutoffVolterra.cutoff cut)
      (compression input F+FullYSourceCutoffVolterra.cutoff cut)
      (compression middle F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s =
    sourceProjection*ordered (compression out F) (compression input F) (compression middle F)
      (current A) (current B) t s := by
  unfold ordered
  simp only [← mul_assoc]
  apply three_leg_return
  · exact full_finite_return out cut (-t) F
  · exact full_finite_return middle cut (t-s) F
  · exact full_finite_return input cut s F
  · exact SourceFiniteUnitary.time_commutes _ _ (compression_blocks out F sourceLabel) (-t)
  · exact SourceFiniteUnitary.time_commutes _ _ (compression_blocks middle F sourceLabel) (t-s)
  · exact current_preserves A
  · exact current_preserves B

def fullFiniteKernel (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) : H →L[ℂ] H :=
  sourceProjection*kernel (compression (p+k+ell) F+FullYSourceCutoffVolterra.cutoff cut)
    (compression p F+FullYSourceCutoffVolterra.cutoff cut)
    (compression (p+ell) F+FullYSourceCutoffVolterra.cutoff cut)
    (compression (p+k) F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s

theorem fullFiniteKernel_return (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) :
    fullFiniteKernel p k ell A B cut t s F=sourceProjection*finiteKernel p k ell A B t s F := by
  simp only [fullFiniteKernel, finiteKernel, kernel, mul_smul_comm, mul_sub, finite_ordered_cutoff_return]

def fullFiniteResponse (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (F : Index) : H →L[ℂ] H :=
  ∫ lag : ℝ in Ioi 0, CanonicalGradedFrequency.weight frequency damping lag •
    fullFiniteKernel p k ell A B cut (age+lag) age F

theorem fullFiniteResponse_return (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (F : Index) :
    fullFiniteResponse p k ell A B cut age frequency damping F = sourceProjection*
      finiteResponse (compression (p+k+ell) F) (compression p F) (compression (p+ell) F)
        (compression (p+k) F) (current A) (current B) age frequency damping := by
  let L := ContinuousLinearMap.mul ℂ (H →L[ℂ] H) sourceProjection
  have generated := L.integral_comp_comm (integrand_integrable _ _ _ _ (current A) (current B)
    (compression_selfAdjoint (p+k+ell) F) (compression_selfAdjoint p F)
    (compression_selfAdjoint (p+ell) F) (compression_selfAdjoint (p+k) F)
    age frequency damping positive)
  change (∫ lag : ℝ in Ioi 0, sourceProjection*CanonicalGradedBilocal.integrand
    (compression (p+k+ell) F) (compression p F) (compression (p+ell) F) (compression (p+k) F)
    (current A) (current B) age frequency damping lag) = sourceProjection*
      finiteResponse (compression (p+k+ell) F) (compression p F) (compression (p+ell) F)
        (compression (p+k) F) (current A) (current B) age frequency damping at generated
  rw [fullFiniteResponse]
  simp_rw [fullFiniteKernel_return]
  simp only [CanonicalGradedBilocal.integrand, finiteKernel, mul_smul_comm] at generated ⊢
  exact generated

def fullResponseFamily (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := fullFiniteResponse p k ell A B cut age frequency damping F
  bounded := ⟨2*‖current A‖*‖current B‖/damping, by positivity, fun F x => by
    rw [fullFiniteResponse_return p k ell A B cut age frequency damping positive F]
    change ‖sourceProjection (finiteResponse _ _ _ _ _ _ age frequency damping x)‖ ≤ _
    exact (NativeHistoryGrade.piece_bound sourceLabel _).trans
      (((finiteResponse _ _ _ _ _ _ age frequency damping).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (finiteResponse_bound _ _ _ _ _ _
          (compression_selfAdjoint (p+k+ell) F) (compression_selfAdjoint p F)
          (compression_selfAdjoint (p+ell) F) (compression_selfAdjoint (p+k) F)
          age frequency damping positive) (norm_nonneg x)))⟩

def fullResponse (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullResponseFamily p k ell A B cut age frequency damping positive)

theorem fullResponse_return (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    fullResponse p k ell A B cut age frequency damping positive =
      historyProjection*response p k ell A B age frequency damping positive :=
  (lift_congr sourceFilter _ (comp (constant sourceProjection)
    (responseFamily p k ell A B age frequency damping positive))
    (fun F => fullFiniteResponse_return p k ell A B cut age frequency damping positive F)).trans
      (lift_comp sourceFilter _ _)

theorem fullResponse_cutoff_independent (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut other : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    fullResponse p k ell A B cut age frequency damping positive =
      fullResponse p k ell A B other age frequency damping positive := by
  rw [fullResponse_return, fullResponse_return]

theorem fullResponse_source_readback (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (x y : FourierSection) :
    Tendsto (fun F : Index => inner ℂ (x (p+k+ell))
      (fullFiniteResponse p k ell A B cut age frequency damping F (sourceProjection (y p)))) sourceFilter
      (𝓝 (inner ℂ (inclusion (x (p+k+ell)))
        (fullResponse p k ell A B cut age frequency damping positive
          (historyProjection (inclusion (y p)))))) := by
  rw [historyProjection, GaussUnitaryHistory.reader_inclusion]
  change Tendsto _ _ (𝓝 (inner ℂ
    ((SourceFamilyHilbert.constant sourceFilter (x (p+k+ell))) : HistorySpace)
    (lift sourceFilter (fullResponseFamily p k ell A B cut age frequency damping positive)
      ((SourceFamilyHilbert.constant sourceFilter (sourceProjection (y p))) : HistorySpace))))
  rw [lift_coe, SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto sourceFilter
    (SourceFamilyHilbert.constant sourceFilter (x (p+k+ell)))
    (act sourceFilter (fullResponseFamily p k ell A B cut age frequency damping positive)
      (SourceFamilyHilbert.constant sourceFilter (sourceProjection (y p))))

def sourceCurrent (out input : PhysicalMomentum) (A : NativeCurrent) (t s : ℝ) (x y : H) : ℂ :=
  inner ℂ (time out t (inclusion x)) (reader (current A) (time input s (inclusion y)))

theorem sourceCurrent_left (out input : PhysicalMomentum) (A : NativeCurrent)
    (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => sourceCurrent out input A u s x y)
      (Complex.I*sourceCurrent out input A t s (physical out x) y) t := by
  have generated := (core_derivative out x t).inner ℂ
    (hasDerivAt_const t (reader (current A) (time input s (inclusion (y : H)))))
  simpa [sourceCurrent, inner_smul_left] using generated

theorem sourceCurrent_right (out input : PhysicalMomentum) (A : NativeCurrent)
    (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => sourceCurrent out input A t u x y)
      (-Complex.I*sourceCurrent out input A t s x (physical input y)) s := by
  have mapped := (reader (current A)).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt s
    (core_derivative input y s)
  have generated := (hasDerivAt_const s (time out t (inclusion (x : H)))).inner ℂ mapped
  simpa [sourceCurrent, inner_smul_right] using generated

end LowEnergy.CanonicalPhysicalCurrent
