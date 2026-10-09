import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePolarizationFlux

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCauchyDynamic
open SaturationMonoid.PhysicsCore
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumCausalPoleResponse PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumStaticVoltageSource PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumFieldConstraintResponse PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationPhysicalNativePhotonFluxReturn
open CanonicalGradedSpatialSource ActualEMAction Filter
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceWholePhotonGreen sourceWholePhotonResidue sourceWholePhotonFrequencyResidue
  originalJacobi originalChange originalInverse originalReadback originalRowLift sourceTemporalFirst sourceTemporalSecond

def voltageElectricVector (spatial : Fin 3 → ℂ) : Fin 36 → ℂ :=
  Pi.single 24 (-spatial 0)+Pi.single 25 (-spatial 1)+Pi.single 26 (-spatial 2)

private theorem voltage_reader_value (p : Fin 4 → ℂ) (r : Fin 36) :
    originalReader36 p r 20 = voltageElectricVector (fun i => p i.succ) r := by
  fin_cases r
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change -p 1 = -p 1+0+0
    ring
  · change -p 2 = 0+-p 2+0
    ring
  · change -p 3 = 0+0+-p 3
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring
  · change (0:ℂ) = 0+0+0
    ring

private theorem voltage_reader_zero_8 (p : Fin 4 → ℂ) (r : Fin 36) :
    originalReader36 p r 8 = 0 := by
  fin_cases r <;> rfl

private theorem voltage_reader_zero_264 (p : Fin 4 → ℂ) (r : Fin 36) :
    originalReader36 p r 264 = 0 := by
  fin_cases r <;> rfl

private theorem voltage_reader_zero_276 (p : Fin 4 → ℂ) (r : Fin 36) :
    originalReader36 p r 276 = 0 := by
  fin_cases r <;> rfl

private theorem voltage_reader_zero_288 (p : Fin 4 → ℂ) (r : Fin 36) :
    originalReader36 p r 288 = 0 := by
  fin_cases r <;> rfl

/-- Every ordinary curvature row of the original initial field is evaluated, including the constitutive B slots. -/
theorem voltage_initial_curvature (spatial : Fin 3 → ℂ) (p : Fin 4 → ℂ) :
    originalReader36 p *ᵥ sourceVoltageSpatialVector spatial =
      voltageElectricVector (fun i => p i.succ) := by
  simp only [sourceVoltageSpatialVector, Matrix.mulVec_add, Matrix.mulVec_single,
    Matrix.col, voltageElectricVector]
  ext r
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.transpose_apply, op_smul_eq_mul,
    voltage_reader_value, voltage_reader_zero_264, voltage_reader_zero_276,
    voltage_reader_zero_288, mul_one, zero_mul, add_zero]
  rfl

theorem voltage_scalar_jet_curvature (p : Fin 4 → ℂ) :
    originalReader36 p *ᵥ sourceVoltageTemporalVector = 0 := by
  rw [sourceVoltageTemporalVector, Matrix.mulVec_single]
  ext r
  simp only [Matrix.col, Pi.smul_apply, Matrix.transpose_apply, op_smul_eq_mul,
    voltage_reader_zero_8, zero_mul, Pi.zero_apply]

/-- The scalar time jet has been retained through the full action before this genuine curvature restriction. -/
theorem voltage_window_curvature (spatial : Fin 3 → ℂ) (z : ℂ) (T : ℝ) :
    originalReader36 (fullMomentum spatial z) *ᵥ voltageWindowField spatial z T =
      voltageWindowMass z T • voltageElectricVector spatial := by
  rw [voltageWindowField, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    voltage_initial_curvature, voltage_scalar_jet_curvature, smul_zero, add_zero]
  rfl

def voltageAuxiliaryFlux (field : Fin 289 → ℂ) : Fin 3 → ℂ :=
  ![field 264, field 276, field 288]

/-- The raw auxiliary coordinate is the actual Y electric flux in the source's fixed native frame. -/
theorem voltage_window_electric_flux (spatial : Fin 3 → ℂ) (z : ℂ) (T : ℝ) (i : Fin 3) :
    voltageAuxiliaryFlux (voltageWindowField spatial z T) i =
      (2*(Stage9C.Material.SpinPair.lapse:ℂ))*(-spatial i*voltageWindowMass z T) := by
  fin_cases i <;>
    norm_num [voltageAuxiliaryFlux, voltageWindowField, sourceVoltageSpatialVector,
      sourceVoltageTemporalVector, Pi.single_apply, Fin.ext_iff] <;> try ring
  congr 2

theorem voltage_full_curvature_observation (spatial : Fin 3 → ℂ) (z : ℂ) (hz : z ≠ 0)
    (regular : fullMomentum spatial z ∈ regularSource) :
    originalReader36 (fullMomentum spatial z) *ᵥ voltageInitialResponse spatial z regular +
      originalReader36 (fullMomentum spatial z) *ᵥ voltageContinuationResponse spatial z regular +
      originalReader36 (fullMomentum spatial z) *ᵥ voltageNullData spatial z =
      z⁻¹ • voltageElectricVector spatial := by
  rw [voltage_curvature_response spatial z hz regular, sourceVoltageLaplaceRamp,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, voltage_initial_curvature,
    voltage_scalar_jet_curvature, smul_zero, add_zero]
  rfl

/-- The actual quantum update is observed after full-field propagation, with its null and both causal parts. -/
theorem voltage_updated_curvature (q : PhysicalResponsePoint) (z : physicalSpectralDomain q.k) (T : ℝ) :
    originalReader36 (fullMomentum (physicalSpatial q.k) z.val) *ᵥ voltageCurrentUpdate q z T =
      voltageWindowMass z.val T • voltageElectricVector (physicalSpatial q.k)-
      originalReader36 (fullMomentum (physicalSpatial q.k) z.val) *ᵥ
        (originalChange (fullMomentum (physicalSpatial q.k) z.val) *ᵥ (nullProjection *ᵥ
          (originalInverse (fullMomentum (physicalSpatial q.k) z.val) *ᵥ voltageWindowField (physicalSpatial q.k) z.val T)))+
      originalReader36 (fullMomentum (physicalSpatial q.k) z.val) *ᵥ voltageCausalResponse q false z T+
      Complex.I • (originalReader36 (fullMomentum (physicalSpatial q.k) z.val) *ᵥ voltageCausalResponse q true z T) := by
  rw [voltage_current_update_split, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul, voltage_window_curvature]

def voltageInitialFrequencyForcing (e omega : ℝ) (n : PhysicalMomentum) : Fin 289 → ℂ :=
  voltageInitialBoundary (fun i => Complex.I*((e^2*n i:ℝ):ℂ)) (-Complex.I*(omega:ℂ))

def voltageInitialPole (e s : ℝ) (n : PhysicalMomentum) : Fin 289 → ℂ :=
  sourceWholePhotonFrequencyResidue e s n *ᵥ
    voltageInitialFrequencyForcing e (sourceFrequency e s) n

/-- This is the original physical clock and wave vector of the common Cauchy event. -/
theorem voltage_frequency_ray (e s : ℝ) (n : PhysicalMomentum) :
    fullMomentum (fun i => Complex.I*((e^2*n i:ℝ):ℂ)) (-Complex.I*(sourceFrequency e s:ℂ)) =
      frequencyRay e s n := by
  funext mu
  refine Fin.cases ?_ (fun i => ?_) mu
  · simp [fullMomentum, frequencyRay, physicalFrequencyMomentum, sourceFrequency, mul_comm]
  · simp [fullMomentum, frequencyRay, physicalFrequencyMomentum, sourceFrequency]

private theorem voltage_frequency_forcing_continuous (e : ℝ) (n : PhysicalMomentum) :
    Continuous (fun w : ℝ => voltageInitialFrequencyForcing e w n) := by
  unfold voltageInitialFrequencyForcing voltageInitialBoundary
  exact continuous_const.add ((continuous_const.mul Complex.continuous_ofReal).smul continuous_const)

/-- Both source-generated simple sheets are tested; no physical photon branch is selected by a caller. -/
theorem voltage_initial_frequency_pole (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach, Tendsto
      (fun w : ℝ => ((w-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) •
        (sourceWholePhotonGreen e.val (w/e.val^2) n *ᵥ voltageInitialFrequencyForcing e.val w n))
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (voltageInitialPole e.val (sourceSheet branch n unit e.val) n)) := by
  filter_upwards [sourceWholePhotonGreen_frequencyResidue branch n unit] with e pole
  have forcing : Tendsto (fun w : ℝ => voltageInitialFrequencyForcing e.val w n)
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (voltageInitialFrequencyForcing e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n)) :=
    ((voltage_frequency_forcing_continuous e.val n).tendsto _).mono_left nhdsWithin_le_nhds
  have continuous : Continuous (fun pair : Matrix (Fin 289) (Fin 289) ℂ × (Fin 289 → ℂ) =>
      pair.1 *ᵥ pair.2) := continuous_fst.matrix_mulVec continuous_snd
  have result := (continuous.tendsto _).comp (pole.prodMk_nhds forcing)
  change Tendsto (fun w =>
    (((w-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) •
      sourceWholePhotonGreen e.val (w/e.val^2) n) *ᵥ voltageInitialFrequencyForcing e.val w n) _
    (𝓝 (voltageInitialPole e.val (sourceSheet branch n unit e.val) n)) at result
  simpa only [Matrix.smul_mulVec] using result

/-- Initial-data emission uses the original full action frequency-flux normalization without rescaling a residue. -/
theorem voltage_initial_frequency_flux (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
        (emActionFrequencyJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n *ᵥ
          voltageInitialPole e.val (sourceSheet branch n unit e.val) n) =
        voltageInitialPole e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_frequencyFlux branch n unit] with e flux
  rw [voltageInitialPole, em_action_frequency_jet]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  rw [flux]

end LowEnergy.GaussComposite.ActualEMCauchyDynamic
