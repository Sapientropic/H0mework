import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyWindow

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCauchyDynamic
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumCausalPoleResponse PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumStaticVoltageSource PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumCurrentSignalRealization
open PreparationVacuumFieldConstraintResponse
open PreparationVacuumMixedFieldReturn (Field289)
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory
open SourcePropagationNoetherTime SourcePropagationMotherEulerKernel
open ActualEMAction Filter MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] originalJacobi sourceTemporalFirst sourceTemporalSecond
  sourceGreen sourceField originalChange originalInverse originalReadback originalRowLift
  originalReader36 sourceVoltageSpatialVector sourceVoltageTemporalVector
  noetherForcing noetherField noetherHistorySourceJet noetherTimeSource noetherBoundary

def voltageQuadrature (imaginary : Bool) (c : ℂ) : ℝ := if imaginary then c.im else c.re

/-- Both real native histories come from the original voltage, scalar ramp and constitutive B fields. -/
def voltageNativeTimeJet (spatial : Fin 3 → ℂ) (imaginary : Bool) (t : ℝ) : SourceJet Field289 :=
  let u : Field289 := fun i => voltageQuadrature imaginary (sourceVoltageSpatialVector spatial i)
  let v : Field289 := fun i => voltageQuadrature imaginary (sourceVoltageTemporalVector i)
  ⟨u+t • v, v, 0⟩

theorem voltage_timejet_generated (spatial : Fin 3 → ℂ) (imaginary : Bool) (t : ℝ) :
    HasSourceJets (voltageNativeTimeJet spatial imaginary) t := by
  constructor
  · apply hasDerivAt_pi.mpr
    intro i
    change HasDerivAt (fun s : ℝ => voltageQuadrature imaginary (sourceVoltageSpatialVector spatial i)+
      s*voltageQuadrature imaginary (sourceVoltageTemporalVector i))
      (voltageQuadrature imaginary (sourceVoltageTemporalVector i)) t
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id t).mul_const (voltageQuadrature imaginary (sourceVoltageTemporalVector i))).const_add
        (voltageQuadrature imaginary (sourceVoltageSpatialVector spatial i))
  · exact hasDerivAt_const t _

theorem voltage_timejet_continuous (spatial : Fin 3 → ℂ) (imaginary : Bool) :
    ContinuousJets (voltageNativeTimeJet spatial imaginary) := by
  refine ⟨?_, continuous_const, continuous_const⟩
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- The temporal signal is the same original real Cauchy configuration in both Fourier quadratures. -/
theorem voltage_timejet_realization (spatial : Fin 3 → ℂ) (imaginary : Bool) (t : ℝ) :
    (voltageNativeTimeJet spatial imaginary t).value =
      sourceVoltageSignal (sourceVoltageFourierProfile spatial (if imaginary then -Complex.I else 1)) 1
        (nativeTimePoint t) := by
  rw [sourceVoltage_signal_fourier]
  have time : nativeTimePoint t 0 = t := by
    simp [nativeTimePoint, coordinateDirection]
  funext i
  simp only [sourceVoltageRamp, sourcePhase_time, fullMomentum, Fin.cases_zero,
    mul_zero, Complex.exp_zero, one_mul, time]
  cases imaginary <;>
    simp [voltageNativeTimeJet, voltageQuadrature, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]

def voltageCausalCurrent (q : PhysicalResponsePoint) (imaginary : Bool) (z : ℂ) (T : ℝ) :
    Fin 289 → ℂ :=
  noetherForcing q (voltageNativeTimeJet (physicalSpatial q.k) imaginary) z T

def voltageCausalResponse (q : PhysicalResponsePoint) (imaginary : Bool)
    (z : physicalSpectralDomain q.k) (T : ℝ) : Fin 289 → ℂ :=
  noetherField q (voltageNativeTimeJet (physicalSpatial q.k) imaginary) z T

/-- The original quantum retarded current is generated from that very Cauchy history, including its first jet. -/
theorem voltage_causal_current_integral (q : PhysicalResponsePoint) (imaginary : Bool)
    (z : ℂ) (T : ℝ) (i : Fin 289) :
    voltageCausalCurrent q imaginary z T i =
      ∫ t in (0:ℝ)..T, laplaceWeight z t*
        (noetherHistorySourceJet q (voltageNativeTimeJet (physicalSpatial q.k) imaginary) t i).value := by
  unfold voltageCausalCurrent noetherForcing
  rfl

/-- The same finite observation retains the complete quantum initial and terminal co-sources. -/
theorem voltage_causal_current_cosources (q : PhysicalResponsePoint) (imaginary : Bool)
    (z : ℂ) (T : ℝ) (i : Fin 289) :
    (originalReadback (fullMomentum (physicalSpatial q.k) z) *ᵥ voltageCausalCurrent q imaginary z T) i =
      (∫ t in (0:ℝ)..T, laplaceWeight z t*
        noetherTimeSource q (voltageNativeTimeJet (physicalSpatial q.k) imaginary) (physicalSpatial q.k) t i)-
      (noetherBoundary q (voltageNativeTimeJet (physicalSpatial q.k) imaginary) (physicalSpatial q.k) z T i-
        noetherBoundary q (voltageNativeTimeJet (physicalSpatial q.k) imaginary) (physicalSpatial q.k) z 0 i) := by
  exact noetherForcing_readback q _ (voltage_timejet_continuous _ imaginary)
    (voltage_timejet_generated _ imaginary) _ z T i

theorem voltage_causal_action (q : PhysicalResponsePoint) (imaginary : Bool)
    (z : physicalSpectralDomain q.k) (T : ℝ) :
    emOriginalJacobi (fullMomentum (physicalSpatial q.k) z.val) *ᵥ voltageCausalResponse q imaginary z T =
      voltageCausalCurrent q imaginary z.val T-originalRowLift (fullMomentum (physicalSpatial q.k) z.val) *ᵥ
        sourceCompatibility (fullMomentum (physicalSpatial q.k) z.val) (voltageCausalCurrent q imaginary z.val T) := by
  rw [em_jacobi_source]
  exact noetherField_equation q _ z T

/-- One generated quantum update of the full native field; neither the source history nor its current is an input witness. -/
def voltageCurrentUpdate (q : PhysicalResponsePoint) (z : physicalSpectralDomain q.k) (T : ℝ) :
    Fin 289 → ℂ :=
  sourceField ⟨fullMomentum (physicalSpatial q.k) z.val, z.property⟩
    (voltageWindowForcing (physicalSpatial q.k) z.val T+
      voltageCausalCurrent q false z.val T+Complex.I • voltageCausalCurrent q true z.val T)

theorem voltage_current_update_original (q : PhysicalResponsePoint)
    (z : physicalSpectralDomain q.k) (T : ℝ) :
    emOriginalJacobi (fullMomentum (physicalSpatial q.k) z.val) *ᵥ voltageCurrentUpdate q z T =
      voltageWindowForcing (physicalSpatial q.k) z.val T+
        voltageCausalCurrent q false z.val T+Complex.I • voltageCausalCurrent q true z.val T-
        originalRowLift (fullMomentum (physicalSpatial q.k) z.val) *ᵥ
          sourceCompatibility (fullMomentum (physicalSpatial q.k) z.val)
            (voltageWindowForcing (physicalSpatial q.k) z.val T+
              voltageCausalCurrent q false z.val T+Complex.I • voltageCausalCurrent q true z.val T) := by
  rw [em_jacobi_source]
  exact original_forced_field ⟨_, z.property⟩ _

/-- The original Cauchy field, its null data, and both causal quantum quadratures occupy one complete carrier. -/
theorem voltage_current_update_split (q : PhysicalResponsePoint)
    (z : physicalSpectralDomain q.k) (T : ℝ) :
    voltageCurrentUpdate q z T =
      voltageWindowField (physicalSpatial q.k) z.val T-
        originalChange (fullMomentum (physicalSpatial q.k) z.val) *ᵥ (nullProjection *ᵥ
          (originalInverse (fullMomentum (physicalSpatial q.k) z.val) *ᵥ voltageWindowField (physicalSpatial q.k) z.val T))+
      voltageCausalResponse q false z T+Complex.I • voltageCausalResponse q true z T := by
  have paid := voltage_window_green (physicalSpatial q.k) z.val T z.property
  unfold voltageCurrentUpdate voltageCausalResponse noetherField
  simp only [sourceField, Matrix.mulVec_add, Matrix.mulVec_smul]
  simpa only [sourceField, voltageCausalCurrent] using
    congrArg (fun field => field+
      sourceGreen ⟨fullMomentum (physicalSpatial q.k) z.val, z.property⟩ *ᵥ voltageCausalCurrent q false z.val T+
      Complex.I • (sourceGreen ⟨fullMomentum (physicalSpatial q.k) z.val, z.property⟩ *ᵥ voltageCausalCurrent q true z.val T)) paid

end LowEnergy.GaussComposite.ActualEMCauchyDynamic
