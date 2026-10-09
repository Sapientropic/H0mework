import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyBoundary

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCauchyDynamic
open SaturationMonoid.PhysicsCore
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumCausalPoleResponse PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumStaticVoltageSource PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumCurrentSignalRealization
open PreparationVacuumFieldConstraintResponse SourcePropagationNativeActionHessian
open ActualEMAction Filter MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] originalJacobi sourceTemporalFirst sourceTemporalSecond
  sourceGreen sourceField originalChange originalInverse originalReadback originalRowLift
  originalReader36

def voltageTimeValue (spatial : Fin 3 → ℂ) (t : ℝ) : Fin 289 → ℂ :=
  sourceVoltageSpatialVector spatial + (t:ℂ) • sourceVoltageTemporalVector

def voltageWindowMass (z : ℂ) (T : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..T, laplaceWeight z t

def voltageWindowMoment (z : ℂ) (T : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..T, laplaceWeight z t*(t:ℂ)

def voltageWindowField (spatial : Fin 3 → ℂ) (z : ℂ) (T : ℝ) : Fin 289 → ℂ :=
  voltageWindowMass z T • sourceVoltageSpatialVector spatial +
    voltageWindowMoment z T • sourceVoltageTemporalVector

def voltageWindowBulk (spatial : Fin 3 → ℂ) (z : ℂ) (T : ℝ) : Fin 289 → ℂ :=
  voltageWindowMass z T • sourceVoltageWholeForcing spatial +
    voltageWindowMoment z T • (originalJacobi (fullMomentum spatial 0) *ᵥ sourceVoltageTemporalVector)

def voltageBoundaryTrace (spatial : Fin 3 → ℂ) (z : ℂ) (t : ℝ) : Fin 289 → ℂ :=
  laplaceWeight z t • (sourceTemporalFirst spatial *ᵥ voltageTimeValue spatial t +
    sourceTemporalSecond *ᵥ (z • voltageTimeValue spatial t+sourceVoltageTemporalVector))

private theorem real_time_derivative (t : ℝ) : HasDerivAt (fun r : ℝ => (r:ℂ)) (1:ℂ) t := by
  simpa only [id_eq, Complex.real_smul, mul_one, one_smul] using
    (hasDerivAt_id t).smul_const (1:ℂ)

private theorem weight_derivative (z : ℂ) (t : ℝ) :
    HasDerivAt (laplaceWeight z) (-z*laplaceWeight z t) t := by
  have paid := ((real_time_derivative t).const_mul (-z)).cexp
  change HasDerivAt (laplaceWeight z) _ t at paid
  convert paid using 1
  unfold laplaceWeight
  ring

private theorem weight_continuous (z : ℂ) : Continuous (laplaceWeight z) :=
  continuous_iff_continuousAt.mpr fun t => (weight_derivative z t).continuousAt

private theorem moment_zero (z : ℂ) (T : ℝ) :
    z*voltageWindowMass z T = 1-laplaceWeight z T := by
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => weight_derivative z t)
    (((weight_continuous z).const_mul (-z)).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_const_mul] at paid
  change -z*voltageWindowMass z T=laplaceWeight z T-laplaceWeight z 0 at paid
  have zero : laplaceWeight z 0=1 := by simp [laplaceWeight]
  rw [zero] at paid
  linear_combination -paid

theorem voltage_window_moment (z : ℂ) (T : ℝ) :
    z*voltageWindowMoment z T = voltageWindowMass z T-(T:ℂ)*laplaceWeight z T := by
  have derivative (t : ℝ) : HasDerivAt (fun s => laplaceWeight z s*(s:ℂ))
      (laplaceWeight z t-z*(laplaceWeight z t*(t:ℂ))) t := by
    exact ((weight_derivative z t).mul (real_time_derivative t)).congr_deriv (by ring)
  have h0 : IntervalIntegrable (laplaceWeight z) volume 0 T := (weight_continuous z).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun t : ℝ => laplaceWeight z t*(t:ℂ)) volume 0 T :=
    ((weight_continuous z).mul Complex.continuous_ofReal).intervalIntegrable _ _
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => derivative t)
    (h0.sub (h1.const_mul z))
  rw [intervalIntegral.integral_sub h0 (h1.const_mul z), intervalIntegral.integral_const_mul] at paid
  unfold voltageWindowMass voltageWindowMoment
  simp only [Complex.ofReal_zero, mul_zero, sub_zero] at paid
  linear_combination -paid

/-- The field is a genuine finite Laplace integral of the original value and scalar normal-time jet. -/
theorem voltage_window_field_integral (spatial : Fin 3 → ℂ) (z : ℂ) (T : ℝ) (i : Fin 289) :
    voltageWindowField spatial z T i =
      ∫ t in (0:ℝ)..T, laplaceWeight z t*voltageTimeValue spatial t i := by
  have h0 : IntervalIntegrable (laplaceWeight z) volume 0 T := (weight_continuous z).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun t : ℝ => laplaceWeight z t*(t:ℂ)) volume 0 T :=
    ((weight_continuous z).mul Complex.continuous_ofReal).intervalIntegrable _ _
  simp only [voltageWindowField, voltageTimeValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, ← mul_assoc]
  rw [intervalIntegral.integral_add (h0.mul_const _) (h1.mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    voltageWindowMass]
  rfl

theorem voltage_boundary_initial (spatial : Fin 3 → ℂ) (z : ℂ) :
    voltageBoundaryTrace spatial z 0 = voltageInitialBoundary spatial z := by
  simp only [voltageBoundaryTrace, voltageTimeValue, Complex.ofReal_zero, zero_smul, add_zero,
    laplaceWeight, mul_zero, Complex.exp_zero, one_smul, voltageInitialBoundary,
    Matrix.mulVec_add, Matrix.mulVec_smul]
  abel

/-- The actual finite observation retains both initial and terminal boundary co-sources. -/
theorem voltage_window_action (spatial : Fin 3 → ℂ) (z : ℂ) (T : ℝ) :
    emOriginalJacobi (fullMomentum spatial z) *ᵥ voltageWindowField spatial z T =
      voltageWindowBulk spatial z T -
        (voltageBoundaryTrace spatial z T-voltageBoundaryTrace spatial z 0) := by
  rw [em_jacobi_source, sourceTemporalPencil_original, voltage_boundary_initial]
  simp only [voltageWindowField, voltageWindowBulk, voltageBoundaryTrace, voltageTimeValue,
    voltageInitialBoundary, sourceVoltageWholeForcing, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination
    ((sourceTemporalFirst spatial *ᵥ sourceVoltageSpatialVector spatial) i+
      z*(sourceTemporalSecond *ᵥ sourceVoltageSpatialVector spatial) i+
      (sourceTemporalSecond *ᵥ sourceVoltageTemporalVector) i)*moment_zero z T +
    ((sourceTemporalFirst spatial *ᵥ sourceVoltageTemporalVector) i+
      z*(sourceTemporalSecond *ᵥ sourceVoltageTemporalVector) i)*voltage_window_moment z T

def voltageWindowForcing (spatial : Fin 3 → ℂ) (z : ℂ) (T : ℝ) : Fin 289 → ℂ :=
  voltageWindowBulk spatial z T-(voltageBoundaryTrace spatial z T-voltageBoundaryTrace spatial z 0)

/-- The full original Green now consumes this very finite Cauchy event, with its null data retained. -/
theorem voltage_window_green (spatial : Fin 3 → ℂ) (z : ℂ) (T : ℝ)
    (regular : fullMomentum spatial z ∈ regularSource) :
    sourceField ⟨fullMomentum spatial z, regular⟩ (voltageWindowForcing spatial z T) =
      voltageWindowField spatial z T-originalChange (fullMomentum spatial z) *ᵥ
        (nullProjection *ᵥ (originalInverse (fullMomentum spatial z) *ᵥ voltageWindowField spatial z T)) := by
  have paid := voltage_window_action spatial z T
  rw [em_jacobi_source] at paid
  change originalJacobi (fullMomentum spatial z) *ᵥ voltageWindowField spatial z T =
    voltageWindowForcing spatial z T at paid
  rw [sourceField, ← paid, Matrix.mulVec_mulVec, sourceGreen_original_left,
    Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec]

end LowEnergy.GaussComposite.ActualEMCauchyDynamic
