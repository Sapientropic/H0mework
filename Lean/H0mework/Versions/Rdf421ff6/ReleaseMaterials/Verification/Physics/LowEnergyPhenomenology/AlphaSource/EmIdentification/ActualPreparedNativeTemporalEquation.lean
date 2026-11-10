import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMForcedSchurSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalQuantumIR
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMEnclosure
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3EMChargeRead

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedNativeTemporal
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open SourcePropagationNativeActionHessian ActualEMAction ActualEMCarrierOwn PhysicalEMGaugeRealization
open CanonicalGradedSpatialSource PreparationCoordinates PreparationVacuumMixedFieldReturn
  PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockVector ActualDressedZeroClockFrequency
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMNativeSchurClock
open ActualDressedEMNativePrincipal ActualDressedEMNativeMomentum ActualDressedEMNativeCoulomb
open ActualDressedEMPhysicalResidueFlux ActualDressedEMFullPoleFlux
open ActualDressedEMCorrectedCouplingSource
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedTemporalQuantumIR ActualSourcePreparedN3MovingResponse
open ActualSourcePreparedStaticCorrectedReturn ActualSourcePreparedEMEnclosure
open ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open ActualEMResponseSplit ActualDressedCorrectedGreen
open scoped Matrix BigOperators

/-- The source-native correction is the original full289 Schur residual at the
actual prepared field, not a difference of couplings. -/
def actualNativeTemporalCorrection (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  (nativeEMRestInsertion.transpose *ᵥ
    nativeCompleteCorrection (frequencyRay e.val 0 n)
      (sourcePreparedClockQuantumMatrix event e.val sigma n)
      (sourceTemporalCorrectedField event e.val sigma n)) 0

private theorem em_insertion_auxiliary_zero (i : Fin 6 × Fin 12) (mu : Fin 4) :
    emInsertion (gaugeAuxiliaryIndex i) mu = 0 := by
  have ne (a : Fin 12) : gaugeAuxiliaryIndex i ≠ gaugeSlot mu a := by
    intro same
    have val := congrArg Fin.val same
    change 217 + 12 * i.1.val + i.2.val = 9 + 12 * mu.val + a.val at val
    omega
  simp only [emInsertion, emGaugeField, Finset.sum_apply, Pi.smul_apply, gaugeField,
    Pi.single_apply, ne, if_false, smul_zero, Finset.sum_const_zero, Complex.ofReal_zero]

private theorem force_read_em_input (p : Fin 4 → ℂ) (nu : Fin 4) :
    nativeCompleteForceRead p (fun i => emInsertion i nu) =
      fun i => nativeEMRestInsertion i nu := by
  have auxiliary : emAuxiliarySlice (fun i => emInsertion i nu) = 0 := by
    funext i
    exact em_insertion_auxiliary_zero i nu
  rw [nativeCompleteForceRead, auxiliary, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]
  rfl

private theorem force_read_temporal (p : Fin 4 → ℂ) :
    nativeCompleteForceRead p sourceTemporalEMForce = fun i => nativeEMRestInsertion i 0 :=
  force_read_em_input p 0

private theorem gram_rest_column :
    nativeEMRestInsertion.transpose *ᵥ (fun i => nativeEMRestInsertion i 0) =
      (3/4 : ℂ) • Pi.single 0 1 := by
  have paid := actual_native_rest_coordinate_gram
  have column := congrArg (fun T : Matrix (Fin 4) (Fin 4) ℂ => fun mu => T mu 0) paid
  funext mu
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply, Matrix.mulVec, dotProduct] using congrFun column mu

/-- The actual prepared principal is the original rest insertion of the generated
clock forcing plus the complete native correction. No zero-clock gate enters. -/
theorem actual_native_prepared_principal (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    nativePhysicalEMPrincipal 0 ((e.val^2 : ℝ) • n)
      (emInsertion.transpose *ᵥ sourceTemporalCorrectedField event e.val sigma n) =
      (3/4 : ℂ) • Pi.single 0 1 +
        nativeEMRestInsertion.transpose *ᵥ
          nativeCompleteCorrection (frequencyRay e.val 0 n)
            (sourcePreparedClockQuantumMatrix event e.val sigma n)
            (sourceTemporalCorrectedField event e.val sigma n) := by
  have field := source_temporal_corrected_field_equation event e.val sigma n positive regular
  have pencil : emOriginalJacobi (frequencyRay e.val 0 n) -
      sourcePreparedClockQuantumMatrix event e.val sigma n =
        sourcePreparedStaticPencil event e.val sigma n := rfl
  have driven : (emOriginalJacobi (frequencyRay e.val 0 n) -
      sourcePreparedClockQuantumMatrix event e.val sigma n) *ᵥ
        sourceTemporalCorrectedField event e.val sigma n = sourceTemporalEMForce := by
    rw [pencil, field]
  have source := actual_native_forced_principal (frequencyRay e.val 0 n)
    (sourcePreparedClockQuantumMatrix event e.val sigma n)
    (sourceTemporalCorrectedField event e.val sigma n)
  rw [driven, force_read_temporal, gram_rest_column] at source
  have frequency : sourceFrequency e.val 0 = 0 := by
    unfold sourceFrequency
    ring
  have physical : nativeEMMomentumMatrix (frequencyRay e.val 0 n) *ᵥ
      (emInsertion.transpose *ᵥ sourceTemporalCorrectedField event e.val sigma n) =
      nativePhysicalEMPrincipal 0 ((e.val^2 : ℝ) • n)
        (emInsertion.transpose *ᵥ sourceTemporalCorrectedField event e.val sigma n) := by
    rw [← actual_physical_frequency_ray, actual_native_physical_em_principal, frequency]
  rw [physical] at source
  exact source

private theorem principal_time (k : PhysicalMomentum) (v : Fin 4 → ℂ) :
    nativePhysicalEMPrincipal 0 k v 0 =
      2 * (lapse : ℂ) * (spatialSquare k : ℂ) * v 0 := by
  have square : (spatialSquare k : ℂ) =
      (k (0 : Fin 3) : ℂ)^2 + (k (1 : Fin 3) : ℂ)^2 + (k (2 : Fin 3) : ℂ)^2 := by
    unfold spatialSquare
    push_cast
    ring
  unfold nativePhysicalEMPrincipal
  simp only [Matrix.cons_val_zero, Complex.ofReal_zero, zero_mul, add_zero]
  rw [← square]
  ring

private theorem spatial_square_scale (c : ℝ) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) : spatialSquare (c • n) = c^2 := by
  have body : spatialSquare (c • n) = c^2 * spatialSquare n := by
    unfold spatialSquare
    have point (i : Fin 3) : (c • n) i = c * n i := rfl
    simp only [point, mul_pow]
    ring
  rw [body, unit, mul_one]

private theorem coefficient_observation (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) :
    sourceN3TemporalEMCoefficient event e.val sigma n =
      noetherPairScale^2 * (emInsertion.transpose *ᵥ
        sourceTemporalCorrectedField event e.val sigma n) 0 := by
  unfold sourceN3TemporalEMCoefficient sourcePreparedEMTensorRead emResponseTensor
    sourceTemporalCorrectedField sourceTemporalEMForce
  rw [Matrix.mul_assoc]
  congr 1

/-- The real scaled Noether T00 equation at the actual prepared field: the only
scale is the original noetherPairScale over twice the source lapse. -/
theorem actual_native_temporal_scaled (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    (e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n =
      noetherPairScale^2 / (2 * (lapse : ℂ)) *
        ((3/4 : ℂ) + actualNativeTemporalCorrection event e sigma n) := by
  have principal := congrFun (actual_native_prepared_principal event e sigma n positive regular) 0
  rw [principal_time] at principal
  have square : (spatialSquare ((e.val^2 : ℝ) • n) : ℂ) = (e.val : ℂ)^4 := by
    rw [spatial_square_scale (e.val^2) n unit]
    push_cast
    ring
  rw [square] at principal
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at principal
  have correction : actualNativeTemporalCorrection event e sigma n =
      (nativeEMRestInsertion.transpose *ᵥ
        nativeCompleteCorrection (frequencyRay e.val 0 n)
          (sourcePreparedClockQuantumMatrix event e.val sigma n)
          (sourceTemporalCorrectedField event e.val sigma n)) 0 := rfl
  rw [coefficient_observation, correction, ← principal]
  field_simp [Complex.ofReal_ne_zero.mpr lapse_pos.ne']


end LowEnergy.GaussComposite.ActualPreparedNativeTemporal
