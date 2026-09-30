import H0mework.Versions.X.NavierStokes.TimeGramAction.RecoveryTimeGramMeasured

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeMomentumWrite

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeRecoveryTimeGramReadout NativeRecoveryTimeGramMeasured NativeRecoveryRowAction
open NativeTimeJetCarrier NativeStressCurlAlgebra

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def path (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) (actual : ℝ) : ComplexCoordinateVector :=
  velocityRead stress pointLe (.fixed (projIcc (0 : ℝ) 1 zero_le_one actual)) wave

def action (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) (actual : ℝ) : ComplexCoordinateVector :=
  forcing stress pointLe wave (projIcc (0 : ℝ) 1 zero_le_one actual) -
    (nu.coeff * integerWaveViscousMultiplier wave) • path stress pointLe wave actual

theorem path_original (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) (actual : ℝ) :
    path stress pointLe wave actual = NativeRecoveryRowAction.velocity receipt actual wave :=
  funext fun coordinate => source_velocity stress pointLe _ wave coordinate

theorem forcing_ambient (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    ∀ᵐ actual : ℝ, actual ∈ Icc (0 : ℝ) 1 →
      forcing stress pointLe wave (projIcc (0 : ℝ) 1 zero_le_one actual) = inheritedForcing receipt wave actual := by
  have common : commonTimeMeasure 1 = Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  apply (ae_restrict_iff' measurableSet_Icc).mp
  rw [ae_restrict_iff_subtype measurableSet_Icc, ← common]
  filter_upwards [source_forcing_ae stress pointLe wave] with time same
  rw [projIcc_of_mem zero_le_one time.2, inheritedForcing, commonTimeZeroExtension_of_mem 1 _ time.1 time.2]
  exact same

theorem action_original_ae (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    ∀ᵐ actual : ℝ, actual ∈ Icc (0 : ℝ) 1 →
      action stress pointLe wave actual = rateRow receipt wave actual := by
  filter_upwards [forcing_ambient stress pointLe wave, inheritedForcing_eq_source_ae receipt wave] with actual forcingSame original
  intro inside
  rw [action, forcingSame inside, original inside, path_original]
  rfl

theorem action_integrable (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    IntervalIntegrable (action stress pointLe wave) volume 0 1 := by
  have pathContinuous : Continuous (path stress pointLe wave) := by
    have same : path stress pointLe wave = fun actual => NativeRecoveryRowAction.velocity receipt actual wave :=
      funext (path_original stress pointLe wave)
    rw [same]
    exact (receipt.coordinate_continuous wave).comp continuous_projIcc
  have paid := (inheritedForcing_integrable receipt wave).sub
    ((pathContinuous.const_smul (nu.coeff * integerWaveViscousMultiplier wave)).intervalIntegrable (μ := volume) (a := 0) (b := 1))
  apply paid.congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [forcing_ambient stress pointLe wave] with actual same inside
  rw [uIoc_of_le zero_le_one] at inside
  rw [action, same ⟨inside.1.le, inside.2⟩]
  rfl

theorem source_hasDerivAt_nonzero (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    ∀ᵐ actual : ℝ, actual ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (path stress pointLe wave) (action stress pointLe wave actual) actual := by
  filter_upwards [rowExtension_derivative_ae receipt wave nonzero, action_original_ae stress pointLe wave]
    with actual derivative same
  intro inside
  have near : path stress pointLe wave =ᶠ[𝓝 actual] rowExtension receipt wave := by
    filter_upwards [Icc_mem_nhds inside.1 inside.2] with sample member
    rw [path_original]
    exact (rowExtension_on_interval receipt wave nonzero ⟨sample, member⟩).symm
  rw [same ⟨inside.1.le, inside.2.le⟩]
  exact (derivative ⟨inside.1.le, inside.2.le⟩).congr_of_eventuallyEq near

theorem source_integral_nonzero (stress : StressAt escape) (pointLe : point ≤ 1)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) (time : Icc (0 : ℝ) 1) :
    (∫ actual in 0..time.1, action stress pointLe wave actual) =
      velocityRead stress pointLe (.fixed time) wave -
        velocityRead stress pointLe (.fixed ⟨0, le_rfl, zero_le_one⟩) wave := by
  have derivative : ∀ᵐ actual : ℝ, actual ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (rowExtension receipt wave) (action stress pointLe wave actual) actual := by
    filter_upwards [rowExtension_derivative_ae receipt wave nonzero, action_original_ae stress pointLe wave]
      with actual evolves same
    intro inside
    rw [uIcc_of_le zero_le_one] at inside
    rw [same inside]
    exact evolves inside
  have write := path_sub_eq_intervalIntegral (rowExtension_absolutelyContinuous receipt wave)
    (action_integrable stress pointLe wave) derivative time.1 (by simpa only [uIcc_of_le zero_le_one] using time.2)
  rw [rowExtension_on_interval receipt wave nonzero time,
    rowExtension_on_interval receipt wave nonzero ⟨0, le_rfl, zero_le_one⟩,
    ← path_original stress pointLe wave time.1, ← path_original stress pointLe wave 0,
    path, path, projIcc_of_mem zero_le_one time.2,
    projIcc_of_mem zero_le_one (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)] at write
  exact write.symm

theorem path_zero (stress : StressAt escape) (pointLe : point ≤ 1) (actual : ℝ) :
    path stress pointLe 0 actual = 0 := by
  rw [path_original]
  exact NativeRecoveryPhysical.wholeMild_zero ledger receipt _

theorem action_zero (stress : StressAt escape) (pointLe : point ≤ 1) (actual : ℝ) :
    action stress pointLe 0 actual = 0 := by
  simp [action, forcing, projectedDivergenceCLM_apply,
    transverseProjection, integerWaveViscousMultiplier, integerWaveNormSq]

theorem source_hasDerivAt (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    ∀ᵐ actual : ℝ, actual ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (path stress pointLe wave) (action stress pointLe wave actual) actual := by
  by_cases nonzero : wave ≠ 0
  · exact source_hasDerivAt_nonzero stress pointLe wave nonzero
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    exact Eventually.of_forall fun actual _ => by
      rw [action_zero]
      have same : path stress pointLe 0 = fun _ => (0 : ComplexCoordinateVector) := funext (path_zero stress pointLe)
      rw [same]
      exact hasDerivAt_const actual 0

theorem source_integral (stress : StressAt escape) (pointLe : point ≤ 1)
    (wave : IntegerWavevector) (time : Icc (0 : ℝ) 1) :
    (∫ actual in 0..time.1, action stress pointLe wave actual) =
      velocityRead stress pointLe (.fixed time) wave -
        velocityRead stress pointLe (.fixed ⟨0, le_rfl, zero_le_one⟩) wave := by
  by_cases nonzero : wave ≠ 0
  · exact source_integral_nonzero stress pointLe wave nonzero time
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    have first : velocityRead stress pointLe (.fixed time) 0 = 0 :=
      (funext fun coordinate => source_velocity stress pointLe (.fixed time) 0 coordinate).trans
        (NativeRecoveryPhysical.wholeMild_zero ledger receipt time)
    have last : velocityRead stress pointLe (.fixed ⟨0, le_rfl, zero_le_one⟩) 0 = 0 :=
      (funext fun coordinate => source_velocity stress pointLe (.fixed ⟨0, le_rfl, zero_le_one⟩) 0 coordinate).trans
        (NativeRecoveryPhysical.wholeMild_zero ledger receipt _)
    simp only [action_zero, intervalIntegral.integral_zero, first, last, sub_self]

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeMomentumWrite
