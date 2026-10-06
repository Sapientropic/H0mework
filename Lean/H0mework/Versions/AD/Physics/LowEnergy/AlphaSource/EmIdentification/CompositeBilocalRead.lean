import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeBilocal
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeVelocity

/-! Original finite-family matrix elements and the inherited controlled time
tail for the composite external legs, with no right Number projection. -/
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
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem composite_source_readback (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping)
    (left right : Bool) (a s b t : Fin 2) (f g : QuantumTest) :
    Tendsto (fun F : Index => inner ℂ (leg left a s f)
      (fullFiniteResponse phi p k ell A B cut age frequency damping F (leg right b t g))) sourceFilter
      (𝓝 (inner ℂ (inclusion (leg left a s f))
        (fullResponse phi p k ell A B cut age frequency damping positive (inclusion (leg right b t g))))) := by
  change Tendsto _ _ (𝓝 (inner ℂ
    ((SourceFamilyHilbert.constant sourceFilter (leg left a s f)) : HistorySpace)
    (lift sourceFilter (fullResponseFamily phi p k ell A B cut age frequency damping positive)
      ((SourceFamilyHilbert.constant sourceFilter (leg right b t g)) : HistorySpace))))
  rw [lift_coe,SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto sourceFilter
    (SourceFamilyHilbert.constant sourceFilter (leg left a s f))
    (act sourceFilter (fullResponseFamily phi p k ell A B cut age frequency damping positive)
      (SourceFamilyHilbert.constant sourceFilter (leg right b t g)))

def finiteTruncation (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (age frequency damping endTime : ℝ) (F : Index) : H →L[ℂ] H :=
  gradeZeroProjection*CanonicalGradedBilocal.finiteTruncation
    (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
    (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F)
    (current A) (current B) age frequency damping endTime

theorem finite_composite_tail (phi : Localizer) (p k ell : PhysicalMomentum) (A B : NativeCurrent)
    (cut : ℕ) (age frequency damping endTime : ℝ) (positive : 0<damping) (future : 0≤endTime)
    (F : Index) (left right : Bool) (a s b t : Fin 2) (f g : QuantumTest) :
    ‖inner ℂ (leg left a s f)
      ((fullFiniteResponse phi p k ell A B cut age frequency damping F-
        finiteTruncation phi p k ell A B age frequency damping endTime F) (leg right b t g))‖ ≤
      ‖leg left a s f‖*(Real.exp (-damping*endTime)/damping*(2*‖current A‖*‖current B‖))*‖leg right b t g‖ := by
  rw [full_finite_response_return phi p k ell A B cut age frequency damping positive F]
  let R := CanonicalGradedBilocal.finiteResponse
    (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
    (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F)
    (current A) (current B) age frequency damping
  let T := CanonicalGradedBilocal.finiteTruncation
    (finiteHamiltonian phi (p+k+ell) F) (finiteHamiltonian phi p F)
    (finiteHamiltonian phi (p+ell) F) (finiteHamiltonian phi (p+k) F)
    (current A) (current B) age frequency damping endTime
  change ‖inner ℂ (leg left a s f) ((gradeZeroProjection*R-gradeZeroProjection*T) (leg right b t g))‖≤_
  rw [←mul_sub]
  have ht : ‖R-T‖≤Real.exp (-damping*endTime)/damping*(2*‖current A‖*‖current B‖) :=
    CanonicalGradedBilocal.finite_truncation_tail _ _ _ _ _ _
      (finiteHamiltonian_selfAdjoint phi (p+k+ell) F) (finiteHamiltonian_selfAdjoint phi p F)
      (finiteHamiltonian_selfAdjoint phi (p+ell) F) (finiteHamiltonian_selfAdjoint phi (p+k) F)
      age frequency damping endTime positive future
  calc
    _ ≤ ‖leg left a s f‖*‖gradeZeroProjection ((R-T) (leg right b t g))‖ := norm_inner_le_norm _ _
    _ ≤ ‖leg left a s f‖*‖(R-T) (leg right b t g)‖ :=
      mul_le_mul_of_nonneg_left (grade_zero_projection_bound _) (norm_nonneg _)
    _ ≤ ‖leg left a s f‖*(‖R-T‖*‖leg right b t g‖) :=
      mul_le_mul_of_nonneg_left ((R-T).le_opNorm _) (norm_nonneg _)
    _ ≤ _ := by rw [←mul_assoc]; gcongr

end LowEnergy.GaussComposite.Bilocal
