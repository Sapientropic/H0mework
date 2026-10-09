import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeBilocal
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPhysicalCurrent

/-! The composite-grade-zero readout of the unlocalized physical bilocal
response. The four propagating legs use the actual physical compressions
compression q F = C_F + finite dΓ(J_q) at all four physical momenta
p+k+ell, p, p+ell, p+k; only the left projection fixes the observable
grade-zero sector, retaining every Number component including the
source-created N=2 states. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalBilocal
open GaussCoreHilbert GaussCoreDifferential SourceFamilyOperator
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open CanonicalPhysicalSpatial CanonicalPhysicalCurrent CanonicalGradedSpatialSource
open CanonicalGradedSpatialKernel (NativeCurrent current)
open CanonicalGradedBilocal (ordered kernel finiteResponse finiteResponse_bound integrand integrand_integrable)
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem physical_grade_zero (p : PhysicalMomentum) (F : Index) :
    Commute gradeZeroProjection (compression p F) :=
  grade_zero_commutes _ (compression_blocks p F)

theorem physical_time_return (p : PhysicalMomentum) (cut : ℕ) (t : ℝ) (F : Index) :
    gradeZeroProjection*SourceFiniteUnitary.time (compression p F+FullYSourceCutoffVolterra.cutoff cut) t=
      gradeZeroProjection*SourceFiniteUnitary.time (compression p F) t :=
  CanonicalGradedGaugeReturn.left_time_return _ _ gradeZeroProjection
    (physical_grade_zero p F) (grade_zero_cutoff cut) t

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

/-- The ordered physical bilocal returns its literal graded compression:
the grade-zero projection sees through the literal Yukawa cutoff on every
unlocalized physical leg. -/
theorem physical_ordered_return (out input middle : PhysicalMomentum)
    (A B : NativeCurrent) (cut : ℕ) (t s : ℝ) (F : Index) :
    gradeZeroProjection*ordered
      (compression out F+FullYSourceCutoffVolterra.cutoff cut)
      (compression input F+FullYSourceCutoffVolterra.cutoff cut)
      (compression middle F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s=
    gradeZeroProjection*ordered
      (compression out F) (compression input F) (compression middle F) (current A) (current B) t s := by
  unfold ordered
  simp only [←mul_assoc]
  apply three_leg_return
  · exact physical_time_return out cut (-t) F
  · exact physical_time_return middle cut (t-s) F
  · exact physical_time_return input cut s F
  · exact SourceFiniteUnitary.time_commutes _ _ (physical_grade_zero out F) (-t)
  · exact SourceFiniteUnitary.time_commutes _ _ (physical_grade_zero middle F) (t-s)
  · exact Bilocal.current_grade_zero A
  · exact Bilocal.current_grade_zero B

/-- The grade-zero bilocal kernel of the physical compressions equals the
grade-zero projected physical finite kernel of the source response. -/
def physicalFullFiniteKernel (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) : H →L[ℂ] H :=
  gradeZeroProjection*kernel
    (compression (p+k+ell) F+FullYSourceCutoffVolterra.cutoff cut)
    (compression p F+FullYSourceCutoffVolterra.cutoff cut)
    (compression (p+ell) F+FullYSourceCutoffVolterra.cutoff cut)
    (compression (p+k) F+FullYSourceCutoffVolterra.cutoff cut) (current A) (current B) t s

theorem physical_full_kernel_return (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (t s : ℝ) (F : Index) :
    physicalFullFiniteKernel p k ell A B cut t s F=
      gradeZeroProjection*CanonicalPhysicalCurrent.finiteKernel p k ell A B t s F := by
  simp only [physicalFullFiniteKernel,CanonicalPhysicalCurrent.finiteKernel,kernel,
    mul_smul_comm,mul_sub,physical_ordered_return]

def physicalFullFiniteResponse (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (F : Index) : H →L[ℂ] H :=
  ∫ lag : ℝ in Ioi 0, CanonicalGradedFrequency.weight frequency damping lag •
    physicalFullFiniteKernel p k ell A B cut (age+lag) age F

/-- Componentwise the grade-zero response of the physical compressions is
the projected physical response family: the whole unlocalized bilocal
chain is retained, no localizer is chosen. -/
theorem physical_full_finite_response_return (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) (F : Index) :
    physicalFullFiniteResponse p k ell A B cut age frequency damping F=
      gradeZeroProjection*(CanonicalPhysicalCurrent.responseFamily p k ell A B age frequency damping
        positive).component F := by
  let L := ContinuousLinearMap.mul ℂ (H →L[ℂ] H) gradeZeroProjection
  have h := L.integral_comp_comm (CanonicalGradedBilocal.integrand_integrable _ _ _ _
    (current A) (current B)
    (compression_selfAdjoint (p+k+ell) F) (compression_selfAdjoint p F)
    (compression_selfAdjoint (p+ell) F) (compression_selfAdjoint (p+k) F)
    age frequency damping positive)
  change (∫ lag : ℝ in Ioi 0, gradeZeroProjection*CanonicalGradedBilocal.integrand
    (compression (p+k+ell) F) (compression p F)
    (compression (p+ell) F) (compression (p+k) F)
    (current A) (current B) age frequency damping lag)=gradeZeroProjection*
      CanonicalGradedBilocal.finiteResponse (compression (p+k+ell) F) (compression p F)
        (compression (p+ell) F) (compression (p+k) F)
        (current A) (current B) age frequency damping at h
  rw [physicalFullFiniteResponse]
  simp_rw [physical_full_kernel_return]
  simp only [CanonicalGradedBilocal.integrand,CanonicalPhysicalCurrent.finiteKernel,
    CanonicalPhysicalCurrent.responseFamily,mul_smul_comm] at h ⊢
  exact h

def physicalFullResponseFamily (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component := physicalFullFiniteResponse p k ell A B cut age frequency damping
  bounded := ⟨2*‖current A‖*‖current B‖/damping,by positivity,fun F x => by
    rw [physical_full_finite_response_return p k ell A B cut age frequency damping positive F]
    exact (grade_zero_projection_bound _).trans
      (((CanonicalGradedBilocal.finiteResponse _ _ _ _ _ _ age frequency damping).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (CanonicalGradedBilocal.finiteResponse_bound _ _ _ _ _ _
          (compression_selfAdjoint (p+k+ell) F) (compression_selfAdjoint p F)
          (compression_selfAdjoint (p+ell) F) (compression_selfAdjoint (p+k) F)
          age frequency damping positive) (norm_nonneg x)))⟩

def physicalFullResponse (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (physicalFullResponseFamily p k ell A B cut age frequency damping positive)

/-- The lifted grade-zero physical response is exactly the grade-zero
reader composed with the completed physical response of the main window. -/
theorem physical_full_response_return (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    physicalFullResponse p k ell A B cut age frequency damping positive=
      reader gradeZeroProjection*CanonicalPhysicalCurrent.response p k ell A B age frequency damping
        positive :=
  (lift_congr sourceFilter _ (comp (constant gradeZeroProjection)
    (CanonicalPhysicalCurrent.responseFamily p k ell A B age frequency damping positive))
    (fun F => physical_full_finite_response_return p k ell A B cut age frequency damping positive F)).trans
    (lift_comp sourceFilter _ _)

/-- The grade-zero projection is transparent on actual source legs: every
Number component survives, so the composite readout returns the physical
response of the right leg directly. -/
theorem physical_composite_response_return (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping)
    (left right : Bool) (a s b t : Fin 2) (f g : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    inner ℂ (inclusion (leg left a s f))
      (physicalFullResponse p k ell A B cut age frequency damping positive
        (inclusion (leg right b t g)))=
    inner ℂ (inclusion (leg left a s f))
      (CanonicalPhysicalCurrent.response p k ell A B age frequency damping positive
        (inclusion (leg right b t g))) := by
  rw [physical_full_response_return]
  change inner ℂ (inclusion (leg left a s f)) (reader gradeZeroProjection
    (CanonicalPhysicalCurrent.response p k ell A B age frequency damping positive
      (inclusion (leg right b t g)))) =_
  rw [←grade_zero_history_pair,source_leg_grade_zero_fixed left a s f profile sameSource]

/-- The completed physical response does not depend on the literal cutoff:
the grade-zero projection returns the same lifted operator for every cut. -/
theorem physical_full_cutoff_independent (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut other : ℕ) (age frequency damping : ℝ) (positive : 0<damping) :
    physicalFullResponse p k ell A B cut age frequency damping positive=
      physicalFullResponse p k ell A B other age frequency damping positive := by
  rw [physical_full_response_return,physical_full_response_return]

end LowEnergy.GaussComposite.PhysicalBilocal
