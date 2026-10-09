import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPhysicalCarrierRead
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMAction
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageGreenRecovery

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCauchyDynamic
open SaturationMonoid.PhysicsCore
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumCausalPoleResponse PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumStaticVoltageSource PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumFieldConstraintResponse SourcePropagationNativeActionHessian
open ActualEMAction
open scoped Matrix BigOperators
attribute [local irreducible] originalJacobi sourceTemporalFirst sourceTemporalSecond
  sourceGreen sourceField originalChange originalInverse originalReadback originalRowLift
  originalReader36

/-- The original second-order action pencil supplies the initial-data co-source. -/
def voltageInitialBoundary (spatial : Fin 3 → ℂ) (z : ℂ) : Fin 289 → ℂ :=
  sourceTemporalFirst spatial *ᵥ sourceVoltageSpatialVector spatial +
    sourceTemporalSecond *ᵥ sourceVoltageTemporalVector +
    z • (sourceTemporalSecond *ᵥ sourceVoltageSpatialVector spatial)

/-- Maintaining the actual scalar ramp has a complete original Euler source, including matter. -/
def voltageContinuationSource (spatial : Fin 3 → ℂ) (z : ℂ) : Fin 289 → ℂ :=
  z⁻¹ • sourceVoltageWholeForcing spatial + (z⁻¹)^2 •
    (originalJacobi (fullMomentum spatial 0) *ᵥ sourceVoltageTemporalVector)

/-- The original action distinguishes initial data from the forcing which maintains the Cauchy ramp. -/
theorem voltage_action_boundary_split (spatial : Fin 3 → ℂ) (z : ℂ) (hz : z ≠ 0) :
    emOriginalJacobi (fullMomentum spatial z) *ᵥ sourceVoltageLaplaceRamp spatial z =
      voltageInitialBoundary spatial z + voltageContinuationSource spatial z := by
  rw [em_jacobi_source, sourceTemporalPencil_original]
  simp only [sourceVoltageLaplaceRamp, voltageInitialBoundary, voltageContinuationSource,
    sourceVoltageWholeForcing, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_smul, smul_add, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hz]
  ring

theorem voltage_original_forcing_split (spatial : Fin 3 → ℂ) (z : ℂ) (hz : z ≠ 0) :
    sourceVoltageLaplaceForcing spatial z =
      voltageInitialBoundary spatial z + voltageContinuationSource spatial z := by
  rw [← sourceVoltageLaplaceRamp_equation spatial z hz]
  rw [← em_jacobi_source]
  exact voltage_action_boundary_split spatial z hz

theorem voltage_continuation_all_rows (spatial : Fin 3 → ℂ) (z : ℂ) :
    voltageContinuationSource spatial z =
      z⁻¹ • (Pi.single 20 (-(2*(Stage9C.Material.SpinPair.lapse:ℂ))*
        ∑ j : Fin 3, (spatial j)^2) + sourceVoltageMatterForcing) +
      (z⁻¹)^2 • (originalJacobi (fullMomentum spatial 0) *ᵥ sourceVoltageTemporalVector) := by
  rw [voltageContinuationSource, sourceVoltageWholeForcing_generated]

/-- Compatibility is shared by the initial and continuing sources, rather than discarded separately. -/
theorem voltage_boundary_compatibility (spatial : Fin 3 → ℂ) (z : ℂ) (hz : z ≠ 0) :
    sourceCompatibility (fullMomentum spatial z) (voltageInitialBoundary spatial z) +
      sourceCompatibility (fullMomentum spatial z) (voltageContinuationSource spatial z) = 0 := by
  have paid := sourceVoltageLaplaceForcing_compatible spatial z hz
  rw [voltage_original_forcing_split spatial z hz] at paid
  simpa only [sourceCompatibility, Matrix.mulVec_add] using paid

def voltageInitialResponse (spatial : Fin 3 → ℂ) (z : ℂ)
    (regular : fullMomentum spatial z ∈ regularSource) : Fin 289 → ℂ :=
  sourceField ⟨fullMomentum spatial z, regular⟩ (voltageInitialBoundary spatial z)

def voltageContinuationResponse (spatial : Fin 3 → ℂ) (z : ℂ)
    (regular : fullMomentum spatial z ∈ regularSource) : Fin 289 → ℂ :=
  sourceField ⟨fullMomentum spatial z, regular⟩ (voltageContinuationSource spatial z)

def voltageNullData (spatial : Fin 3 → ℂ) (z : ℂ) : Fin 289 → ℂ :=
  originalChange (fullMomentum spatial z) *ᵥ (nullProjection *ᵥ
    (originalInverse (fullMomentum spatial z) *ᵥ sourceVoltageLaplaceRamp spatial z))

/-- The same full289 Green restores the whole Cauchy event, with its original nine null data. -/
theorem voltage_same_green_response (spatial : Fin 3 → ℂ) (z : ℂ) (hz : z ≠ 0)
    (regular : fullMomentum spatial z ∈ regularSource) :
    voltageInitialResponse spatial z regular + voltageContinuationResponse spatial z regular +
      voltageNullData spatial z = sourceVoltageLaplaceRamp spatial z := by
  have paid := sourceVoltageLaplaceRamp_recovered spatial z hz regular
  rw [voltage_original_forcing_split spatial z hz] at paid
  simp only [sourceField, Matrix.mulVec_add] at paid
  unfold voltageInitialResponse voltageContinuationResponse voltageNullData
  simp only [sourceField]
  exact eq_sub_iff_add_eq.mp paid

theorem voltage_initial_action (spatial : Fin 3 → ℂ) (z : ℂ)
    (regular : fullMomentum spatial z ∈ regularSource) :
    emOriginalJacobi (fullMomentum spatial z) *ᵥ voltageInitialResponse spatial z regular =
      voltageInitialBoundary spatial z - originalRowLift (fullMomentum spatial z) *ᵥ
        sourceCompatibility (fullMomentum spatial z) (voltageInitialBoundary spatial z) := by
  rw [em_jacobi_source]
  exact original_forced_field ⟨fullMomentum spatial z, regular⟩ _

/-- The complete source curvature symbol reads the same field; no null or initial term is suppressed. -/
theorem voltage_curvature_response (spatial : Fin 3 → ℂ) (z : ℂ) (hz : z ≠ 0)
    (regular : fullMomentum spatial z ∈ regularSource) :
    originalReader36 (fullMomentum spatial z) *ᵥ voltageInitialResponse spatial z regular +
      originalReader36 (fullMomentum spatial z) *ᵥ voltageContinuationResponse spatial z regular +
      originalReader36 (fullMomentum spatial z) *ᵥ voltageNullData spatial z =
    originalReader36 (fullMomentum spatial z) *ᵥ sourceVoltageLaplaceRamp spatial z := by
  rw [← Matrix.mulVec_add, ← Matrix.mulVec_add, voltage_same_green_response spatial z hz regular]

end LowEnergy.GaussComposite.ActualEMCauchyDynamic
