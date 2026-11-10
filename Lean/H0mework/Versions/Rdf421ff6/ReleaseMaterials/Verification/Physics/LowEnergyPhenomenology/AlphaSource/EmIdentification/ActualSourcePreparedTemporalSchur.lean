import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalQuantumWard
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHalfSchur

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedTemporalSchur
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalStaticSpatialCouplingReturn
open PreparationVacuumStaticPoleResponse
open ActualEMCarrierOwn ActualEMResponseSplit ActualEMDressedSchur ActualEMDressedConstraint
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedFrequencyHalf
open ActualDressedHalfGreenSchur ActualDressedEMTensorClock ActualDressedZeroDamping
open ActualSourcePreparedStaticNativeConstraint ActualSourcePreparedStaticCorrectedReturn
open ActualSourcePreparedEMEnclosure ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualDressedNoetherCoulombUnit ActualSourcePreparedN3EMChargeRead
open scoped Matrix BigOperators
attribute [local irreducible] sourceNullCoordinates sourceNullLift sourceNull
  halfSchur halfResponseNine sourcePreparedFullGreenRead

def sourceTemporalStaticPoint (e : scaleDomain) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) : regularSource :=
  sourceSpatialStaticRegularPoint n unit ⟨e.val^2, by exact ⟨pow_pos e.property.1 2, small⟩⟩

private theorem static_point_ray (e : scaleDomain) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) :
    (sourceTemporalStaticPoint e n unit small).val = frequencyRay e.val 0 n :=
  source_static_spatial_ray e.val n

private theorem static_clock (epsilon sigma : ℝ) :
    dampedFourierClock (sourceFrequency epsilon 0) sigma = (sigma : ℂ) := by
  simp [dampedFourierClock, sourceFrequency]

def sourceTemporalSchurMatrix (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) :
    Matrix (Fin 9) (Fin 9) ℂ :=
  halfSchur event ((e.val^2 : ℝ) • n) (sourceTemporalStaticPoint e n unit small) (sigma : ℂ)

def sourceTemporalSchurCoordinates (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) : Fin 9 → ℂ :=
  (sourceTemporalSchurMatrix event e sigma n unit small)⁻¹ *ᵥ
    halfSchurSource event ((e.val^2 : ℝ) • n) (sourceTemporalStaticPoint e n unit small)
      (sigma : ℂ) sourceTemporalEMForce

def sourceTemporalSchurField (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) : Fin 289 → ℂ :=
  halfResponseNine event ((e.val^2 : ℝ) • n) (sourceTemporalStaticPoint e n unit small)
    (sigma : ℂ) sourceTemporalEMForce (sourceTemporalSchurCoordinates event e sigma n unit small)

private theorem schur_source_zero (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) : halfSchurSource event transfer p lambda 0 = 0 := by
  unfold halfSchurSource
  rw [Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero, map_zero, neg_zero]

private theorem schur_regular_from_full_inverse (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (G : Matrix (Fin 289) (Fin 289) ℂ)
    (feedback : halfFeedbackDet event transfer p lambda ≠ 0)
    (inverse : G * frequencyResponsePencil event transfer p.val lambda = 1) :
    (halfSchur event transfer p lambda).det ≠ 0 := by
  have kernel : ∀ x : Fin 9 → ℂ, halfSchur event transfer p lambda *ᵥ x = 0 → x = 0 := by
    intro x zero
    let a := halfResponseNine event transfer p lambda 0 x
    have source : halfSchur event transfer p lambda *ᵥ x = halfSchurSource event transfer p lambda 0 := by
      rw [zero, schur_source_zero]
    have equation : frequencyResponsePencil event transfer p.val lambda *ᵥ a = 0 :=
      (half_full_solution_schur event transfer p lambda feedback 0 a).2 ⟨x, rfl, source⟩
    have a_zero := congrArg (fun v => G*ᵥv) equation
    rw [Matrix.mulVec_mulVec, inverse, Matrix.one_mulVec, Matrix.mulVec_zero] at a_zero
    have data := half_response_null_data event transfer p lambda feedback 0 x
    change sourceNull p.val*ᵥa = sourceNullLift p.val x at data
    rw [a_zero, Matrix.mulVec_zero] at data
    have returned := congrArg (sourceNullCoordinates p.val) data
    rw [map_zero, source_null_lift_coordinates] at returned
    exact returned.symm
  have injective : Function.Injective (halfSchur event transfer p lambda).mulVec := by
    intro x y equality
    exact sub_eq_zero.mp (kernel (x-y) (by rw [Matrix.mulVec_sub, equality, sub_self]))
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp injective))

/-- The nine-dimensional determinant is generated by the complete actual
inverse and the original feedback chart; it is not an independent input. -/
theorem source_temporal_schur_regular (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0)
    (feedback : halfFeedbackDet event ((e.val^2 : ℝ) • n)
      (sourceTemporalStaticPoint e n unit small) (sigma : ℂ) ≠ 0) :
    (sourceTemporalSchurMatrix event e sigma n unit small).det ≠ 0 := by
  have inverse := (source_prepared_static_green_inverse event e.val sigma n positive regular).2
  rw [source_prepared_static_pencil_actual event e.val sigma n positive, static_clock] at inverse
  unfold sourceTemporalSchurMatrix
  apply schur_regular_from_full_inverse event _ _ _ (correctedGreen event e.val 0 sigma n) feedback
  rw [static_point_ray]
  exact inverse

/-- Original 9-by-9 inversion returns the very same complete actual time field. -/
theorem source_temporal_schur_field_actual (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0)
    (feedback : halfFeedbackDet event ((e.val^2 : ℝ) • n)
      (sourceTemporalStaticPoint e n unit small) (sigma : ℂ) ≠ 0) :
    sourceTemporalSchurField event e sigma n unit small =
      sourceTemporalCorrectedField event e.val sigma n := by
  have schur := source_temporal_schur_regular event e sigma n unit small positive regular feedback
  have equation : sourceTemporalSchurMatrix event e sigma n unit small *ᵥ
      sourceTemporalSchurCoordinates event e sigma n unit small =
    halfSchurSource event ((e.val^2 : ℝ) • n) (sourceTemporalStaticPoint e n unit small)
      (sigma : ℂ) sourceTemporalEMForce := by
    unfold sourceTemporalSchurCoordinates
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr schur), Matrix.one_mulVec]
  have full := (half_full_solution_schur event ((e.val^2 : ℝ) • n)
    (sourceTemporalStaticPoint e n unit small) (sigma : ℂ) feedback
    sourceTemporalEMForce (sourceTemporalSchurField event e sigma n unit small)).2
      ⟨sourceTemporalSchurCoordinates event e sigma n unit small, rfl, equation⟩
  rw [static_point_ray] at full
  have same := (actual_corrected_full_solution event e.val 0 sigma n positive regular
    sourceTemporalEMForce (sourceTemporalSchurField event e sigma n unit small)).1
      (by rw [static_clock]; exact full)
  rw [same]
  unfold sourceTemporalCorrectedField correctedResponse
  rw [source_prepared_full_green_original event e.val sigma n positive regular]

/-- These are the original null coordinates of G E0, not arbitrary initial data. -/
theorem source_temporal_schur_coordinates_actual (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0)
    (feedback : halfFeedbackDet event ((e.val^2 : ℝ) • n)
      (sourceTemporalStaticPoint e n unit small) (sigma : ℂ) ≠ 0) :
    sourceTemporalSchurCoordinates event e sigma n unit small =
      sourceNullCoordinates (frequencyRay e.val 0 n)
        (sourceTemporalCorrectedField event e.val sigma n) := by
  have data := half_response_null_data event ((e.val^2 : ℝ) • n)
    (sourceTemporalStaticPoint e n unit small) (sigma : ℂ) feedback sourceTemporalEMForce
    (sourceTemporalSchurCoordinates event e sigma n unit small)
  change sourceNull (sourceTemporalStaticPoint e n unit small).val*ᵥ
    sourceTemporalSchurField event e sigma n unit small = _ at data
  rw [source_temporal_schur_field_actual event e sigma n unit small positive regular feedback,
    static_point_ray] at data
  have returned := congrArg (sourceNullCoordinates (frequencyRay e.val 0 n)) data
  rw [←source_null_coordinates_generated, source_null_lift_coordinates, source_null_lift_coordinates] at returned
  exact returned.symm

theorem source_temporal_schur_tensor_read (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0)
    (feedback : halfFeedbackDet event ((e.val^2 : ℝ) • n)
      (sourceTemporalStaticPoint e n unit small) (sigma : ℂ) ≠ 0) :
    dotProduct sourceTemporalEMForce (sourceTemporalSchurField event e sigma n unit small) =
      correctedEMTensor event e.val 0 sigma n 0 0 := by
  rw [source_temporal_schur_field_actual event e sigma n unit small positive regular feedback]
  unfold sourceTemporalCorrectedField
  rw [source_prepared_full_green_original event e.val sigma n positive regular]
  unfold sourceTemporalEMForce correctedEMTensor emResponseTensor
  rw [Matrix.mul_assoc]
  rfl

/-- The Schur field directly consumes the original temporal clock cofactor. -/
theorem source_temporal_schur_clock_cofactor (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0)
    (feedback : halfFeedbackDet event ((e.val^2 : ℝ) • n)
      (sourceTemporalStaticPoint e n unit small) (sigma : ℂ) ≠ 0) :
    (dampingDeterminant event e.val n).eval (sigma : ℂ) *
      dotProduct sourceTemporalEMForce (sourceTemporalSchurField event e sigma n unit small) =
      (dampingEMNumerator event e.val n 0 0).eval (sigma : ℂ) := by
  rw [source_temporal_schur_tensor_read event e sigma n unit small positive regular feedback]
  have tensor := congrFun (congrFun
    (actual_corrected_em_tensor_clear event e.val sigma 0 n positive regular) 0) 0
  simpa only [dampingDeterminant, dampingEMNumerator, Matrix.map_apply, damping_slice_eval,
    Matrix.smul_apply, smul_eq_mul] using tensor

theorem source_temporal_schur_noether_coefficient (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0)
    (feedback : halfFeedbackDet event ((e.val^2 : ℝ) • n)
      (sourceTemporalStaticPoint e n unit small) (sigma : ℂ) ≠ 0) :
    sourceN3TemporalEMCoefficient event e.val sigma n = noetherPairScale^2 *
      dotProduct sourceTemporalEMForce (sourceTemporalSchurField event e sigma n unit small) := by
  rw [source_temporal_schur_tensor_read event e sigma n unit small positive regular feedback]
  unfold sourceN3TemporalEMCoefficient
  rw [source_prepared_em_tensor_original event e.val sigma n positive regular]

end LowEnergy.GaussComposite.ActualSourcePreparedTemporalSchur
