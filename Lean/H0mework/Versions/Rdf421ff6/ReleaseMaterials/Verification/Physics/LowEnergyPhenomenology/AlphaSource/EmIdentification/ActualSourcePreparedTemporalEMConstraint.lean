import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3EMCoefficient
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeConstraint

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedTemporalEMConstraint
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalStaticSpatialCouplingReturn
open PreparationVacuumStaticPoleResponse
open ActualEMCarrierOwn ActualDressedNullNative ActualEMDressedSchur
open ActualDressedFullCoulomb ActualSourcePreparedEMEnclosure ActualSourcePreparedN3MovingResponse
open ActualSourcePreparedStaticNativeConstraint
open ActualDressedCorrectedGreen ActualEMResponseSplit ActualDressedNoetherCoulombUnit
open ActualSourcePreparedN3EMChargeRead
open scoped Matrix BigOperators
attribute [local irreducible] emInsertion sourcePhotonNullSource originalChange originalReadback

def sourceTemporalEMForce : Fin 289 → ℂ := fun i => emInsertion i 0

theorem source_em_temporal_cokernel_frequency (p : Fin 4 → ℂ) :
    sourceCokernel p sourceTemporalEMForce 2 = -(1/2:ℂ)*p 0 := by
  rw [original_null_cokernel]
  change dotProduct (originalNullColumn (-p) 2) (fun i => emInsertion i 0) = _
  rw [dotProduct_comm]
  change (emInsertion.transpose*ᵥoriginalNullColumn (-p) 2) 0 = _
  rw [em_projection_coordinates]
  simp_rw [original_null_column_literal]
  dsimp only [nullColumnTerms, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons,
    Fin.cases, Fin.induction, Fin.induction.go]
  norm_num [nullColumnTerms, sourceMatrix, SourceTerm.matrix, Powers.value,
    nullColumnIndex, PreparationVacuumMixedFieldReturn.gaugeSlot, Pi.neg_apply,
    Matrix.single, Fin.ext_iff, coefficientValue]
  ring

/-- The actual temporal EM insertion consumes the original nine-row source
columns at static momentum; no dressed current constraint is assumed. -/
theorem source_em_temporal_cokernel (p : Fin 4 → ℂ) (static : p 0 = 0) :
    sourceCokernel p sourceTemporalEMForce = 0 := by
  funext row
  rw [original_null_cokernel]
  change dotProduct (originalNullColumn (-p) row) (fun i => emInsertion i 0) = 0
  rw [dotProduct_comm]
  change (emInsertion.transpose*ᵥoriginalNullColumn (-p) row) 0=0
  rw [em_projection_coordinates]
  simp_rw [original_null_column_literal]
  fin_cases row <;>
    norm_num [nullColumnTerms, sourceMatrix, SourceTerm.matrix, Powers.value,
      nullColumnIndex, PreparationVacuumMixedFieldReturn.gaugeSlot, Pi.neg_apply, static, Matrix.single, Fin.ext_iff]

/-- This is the original transported null-source projector, restricted to the
same temporal column, not a replacement unconstrained Green operator. -/
theorem source_em_temporal_null_source (epsilon : ℝ) (n : PhysicalMomentum) :
    sourcePhotonNullSource epsilon 0 n *ᵥsourceTemporalEMForce = 0 := by
  have static : frequencyRay epsilon 0 n 0 = 0 := by
    change -Complex.I*((0*epsilon^2 : ℝ) : ℂ)=0
    simp only [zero_mul, Complex.ofReal_zero, mul_zero]
  have compatible := (source_compatibility_nine (frequencyRay epsilon 0 n) sourceTemporalEMForce).mpr
    (source_em_temporal_cokernel _ static)
  unfold sourcePhotonNullSource
  rw [←Matrix.mulVec_mulVec, ←Matrix.mulVec_mulVec]
  change originalRowLift (frequencyRay epsilon 0 n)*ᵥ
    sourceCompatibility (frequencyRay epsilon 0 n) sourceTemporalEMForce = 0
  rw [compatible, Matrix.mulVec_zero]

theorem source_prepared_temporal_native_defect_zero (fieldEvent : DressedEvent)
    (e : scaleDomain) (sigma : ℝ) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) :
    dotProduct sourceTemporalEMForce
      ((sourcePreparedFullGreenRead fieldEvent e.val sigma n * sourcePreparedNativeConstraint e.val n)*ᵥ
        sourceTemporalEMForce) = 0 := by
  rw [source_prepared_native_constraint_actual e n unit small, ←Matrix.mulVec_mulVec,
    source_em_temporal_null_source, Matrix.mulVec_zero, dotProduct_zero]

/-- The actual temporal Noether-normalized coefficient consumes full corrected
minus native propagation; its original constraint arm vanishes by the source
column identity, while the complete clock quantum arm remains. -/
theorem source_prepared_temporal_moving_response (fieldEvent : DressedEvent)
    (e : scaleDomain) (sigma : ℝ) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) (positive : 0 < sigma)
    (regular : correctedDet fieldEvent e.val 0 sigma n ≠ 0) :
    sourceN3TemporalEMCoefficient fieldEvent e.val sigma n -
      noetherPairScale^2 * dotProduct sourceTemporalEMForce
        (sourceNativeStaticMatrix e.val n *ᵥsourceTemporalEMForce) =
      noetherPairScale^2 * dotProduct sourceTemporalEMForce
        ((sourcePreparedFullGreenRead fieldEvent e.val sigma n *
          sourcePreparedClockQuantumMatrix fieldEvent e.val sigma n * sourceNativeStaticMatrix e.val n)*ᵥ
            sourceTemporalEMForce) := by
  have read := congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ =>
    dotProduct sourceTemporalEMForce (M*ᵥsourceTemporalEMForce))
    (source_prepared_full_native_response fieldEvent e.val sigma n positive regular)
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.add_mulVec, dotProduct_add,
    source_prepared_temporal_native_defect_zero fieldEvent e sigma n unit small, add_zero] at read
  unfold sourceN3TemporalEMCoefficient sourcePreparedEMTensorRead emResponseTensor
  rw [Matrix.mul_assoc]
  change noetherPairScale^2 * dotProduct sourceTemporalEMForce
      (sourcePreparedFullGreenRead fieldEvent e.val sigma n *ᵥsourceTemporalEMForce) - _ = _
  rw [←mul_sub, read]

end LowEnergy.GaussComposite.ActualSourcePreparedTemporalEMConstraint
