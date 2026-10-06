import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCurrentResponse
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalGradedBilocal

/-! The original independent-momentum kernel acts on the source composite
legs. Only the left G0 projection is used; Number-zero and Number-two
occupations survive. All four original momentum Hamiltonians are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.Bilocal
open GaussCoreHilbert GaussCoreDifferential SourceFamilyOperator
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open CanonicalGradedSpatialSource CanonicalGradedSpatial
open CanonicalGradedSpatialKernel (NativeCurrent current)
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open SourceFiniteUnitary
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem momentum_grade_zero (phi : Localizer) (p : PhysicalMomentum) (F : Index) :
    Commute gradeZeroProjection (finiteHamiltonian phi p F) :=
  grade_zero_commutes _ (finiteHamiltonian_blocks phi p F)

theorem current_grade_zero (A : NativeCurrent) : Commute gradeZeroProjection (current A) :=
  grade_zero_current A.localizer A.component A.generator

theorem finite_time_return (phi : Localizer) (p : PhysicalMomentum) (cut : ℕ) (t : ℝ) (F : Index) :
    gradeZeroProjection*time (finiteHamiltonian phi p F+FullYSourceCutoffVolterra.cutoff cut) t =
      gradeZeroProjection*time (finiteHamiltonian phi p F) t :=
  CanonicalGradedGaugeReturn.left_time_return _ _ gradeZeroProjection
    (momentum_grade_zero phi p F) (grade_zero_cutoff cut) t

private theorem three_leg {R : Type*} [Monoid R]
    (P U₁ U₂ U₃ V₁ V₂ V₃ A B : R)
    (h₁ : P*U₁=P*V₁) (h₂ : P*U₂=P*V₂) (h₃ : P*U₃=P*V₃)
    (v₁ : Commute P V₁) (v₂ : Commute P V₂) (a : Commute P A) (b : Commute P B) :
    P*U₁*A*U₂*B*U₃=P*V₁*A*V₂*B*V₃ := by
  have first := (v₁.mul_right a).eq
  have second := (((v₁.mul_right a).mul_right v₂).mul_right b).eq
  calc
    _ = (P*V₁*A)*U₂*B*U₃ := by rw [h₁]
    _ = (V₁*A)*(P*U₂)*B*U₃ := by
      rw [←mul_assoc] at first
      rw [first]
      simp only [mul_assoc]
    _ = (V₁*A)*(P*V₂)*B*U₃ := by rw [h₂]
    _ = (P*V₁*A*V₂*B)*U₃ := by
      rw [←mul_assoc] at first
      rw [first]
      simp only [mul_assoc]
    _ = (V₁*A*V₂*B)*(P*U₃) := by
      simp only [←mul_assoc] at second
      rw [second]
      simp only [mul_assoc]
    _ = (V₁*A*V₂*B)*(P*V₃) := by rw [h₃]
    _ = _ := by
      simp only [←mul_assoc] at second
      rw [second]
      simp only [mul_assoc]

theorem ordered_return (phi : Localizer) (out input middle : PhysicalMomentum)
    (A B : NativeCurrent) (cut : ℕ) (t s : ℝ) (F : Index) :
    gradeZeroProjection*CanonicalGradedBilocal.ordered
      (finiteHamiltonian phi out F+FullYSourceCutoffVolterra.cutoff cut)
      (finiteHamiltonian phi input F+FullYSourceCutoffVolterra.cutoff cut)
      (finiteHamiltonian phi middle F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s =
    gradeZeroProjection*CanonicalGradedBilocal.ordered
      (finiteHamiltonian phi out F) (finiteHamiltonian phi input F)
      (finiteHamiltonian phi middle F) (current A) (current B) t s := by
  unfold CanonicalGradedBilocal.ordered
  simp only [←mul_assoc]
  apply three_leg
  · exact finite_time_return phi out cut (-t) F
  · exact finite_time_return phi middle cut (t-s) F
  · exact finite_time_return phi input cut s F
  · exact time_commutes _ _ (momentum_grade_zero phi out F) (-t)
  · exact time_commutes _ _ (momentum_grade_zero phi middle F) (t-s)
  · exact current_grade_zero A
  · exact current_grade_zero B

def fullFiniteKernel (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) : H →L[ℂ] H :=
  gradeZeroProjection*CanonicalGradedBilocal.kernel
    (finiteHamiltonian phi (p+k+ell) F+FullYSourceCutoffVolterra.cutoff cut)
    (finiteHamiltonian phi p F+FullYSourceCutoffVolterra.cutoff cut)
    (finiteHamiltonian phi (p+ell) F+FullYSourceCutoffVolterra.cutoff cut)
    (finiteHamiltonian phi (p+k) F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s

theorem full_kernel_return (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) :
    fullFiniteKernel phi p k ell A B cut t s F=
      gradeZeroProjection*CanonicalGradedBilocal.finiteKernel phi p k ell A B t s F := by
  simp only [fullFiniteKernel,CanonicalGradedBilocal.finiteKernel,CanonicalGradedBilocal.kernel,
    mul_smul_comm,mul_sub,ordered_return]

def fullFiniteResponse (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (F : Index) : H →L[ℂ] H :=
  ∫ lag : ℝ in Ioi 0, CanonicalGradedFrequency.weight frequency damping lag •
    fullFiniteKernel phi p k ell A B cut (age+lag) age F

theorem full_finite_response_return (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (F : Index) :
    fullFiniteResponse phi p k ell A B cut age frequency damping F=gradeZeroProjection*
      (CanonicalGradedBilocal.responseFamily phi p k ell A B age frequency damping positive).component F := by
  let L := ContinuousLinearMap.mul ℂ (H →L[ℂ] H) gradeZeroProjection
  have h := L.integral_comp_comm (CanonicalGradedBilocal.integrand_integrable _ _ _ _ (current A) (current B)
    (finiteHamiltonian_selfAdjoint phi (p+k+ell) F) (finiteHamiltonian_selfAdjoint phi p F)
    (finiteHamiltonian_selfAdjoint phi (p+ell) F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
    age frequency damping positive)
  change (∫ lag : ℝ in Ioi 0, gradeZeroProjection*CanonicalGradedBilocal.integrand
    (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
    (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F)
    (current A) (current B) age frequency damping lag) = gradeZeroProjection*
      CanonicalGradedBilocal.finiteResponse (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
        (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F)
        (current A) (current B) age frequency damping at h
  rw [fullFiniteResponse]
  simp_rw [full_kernel_return]
  simp only [CanonicalGradedBilocal.integrand,CanonicalGradedBilocal.finiteKernel,
    CanonicalGradedBilocal.responseFamily,mul_smul_comm] at h ⊢
  exact h

def fullResponseFamily (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := fullFiniteResponse phi p k ell A B cut age frequency damping F
  bounded := ⟨2*‖current A‖*‖current B‖/damping,by positivity,fun F x => by
    rw [full_finite_response_return phi p k ell A B cut age frequency damping positive F]
    exact (grade_zero_projection_bound _).trans
      (((CanonicalGradedBilocal.finiteResponse _ _ _ _ _ _ age frequency damping).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (CanonicalGradedBilocal.finiteResponse_bound _ _ _ _ _ _
          (finiteHamiltonian_selfAdjoint phi (p+k+ell) F) (finiteHamiltonian_selfAdjoint phi p F)
          (finiteHamiltonian_selfAdjoint phi (p+ell) F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
          age frequency damping positive) (norm_nonneg x)))⟩

def fullResponse (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullResponseFamily phi p k ell A B cut age frequency damping positive)

theorem full_response_return (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    fullResponse phi p k ell A B cut age frequency damping positive =
      reader gradeZeroProjection*CanonicalGradedBilocal.response phi p k ell A B age frequency damping positive :=
  (lift_congr sourceFilter _ (comp (constant gradeZeroProjection)
    (CanonicalGradedBilocal.responseFamily phi p k ell A B age frequency damping positive))
    (fun F => full_finite_response_return phi p k ell A B cut age frequency damping positive F)).trans
      (lift_comp sourceFilter _ _)

theorem composite_response_return (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping)
    (left right : Bool) (a s b t : Fin 2) (f g : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    inner ℂ (inclusion (leg left a s f))
      (fullResponse phi p k ell A B cut age frequency damping positive (inclusion (leg right b t g))) =
    inner ℂ (inclusion (leg left a s f))
      (CanonicalGradedBilocal.response phi p k ell A B age frequency damping positive (inclusion (leg right b t g))) := by
  rw [full_response_return]
  change inner ℂ (inclusion (leg left a s f)) (reader gradeZeroProjection
    (CanonicalGradedBilocal.response phi p k ell A B age frequency damping positive (inclusion (leg right b t g)))) = _
  rw [←grade_zero_history_pair,source_leg_grade_zero_fixed left a s f profile sameSource]

end LowEnergy.GaussComposite.Bilocal
