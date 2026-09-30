import H0mework.Versions.X.NavierStokes.StressWeakInput.FiniteAdjoint

set_option autoImplicit false
open scoped BigOperators
namespace SaturationMonoid.NavierStokes.NativeWindowOperatorGreen
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint
noncomputable section

theorem zero_reality : FiniteStateFourierReality (0 : ComplexVorticityHilbertState) := by
  intro wave
  funext coordinate
  simp [vectorConj]

theorem trilinear_zero (frequencies : Finset IntegerWavevector)
    (first last : ComplexVorticityHilbertState) :
    finiteStateVelocityBilinearEnergyPairing frequencies first 0 last = 0 := by
  have actual := trilinear_negative frequencies first 0 last
  simp only [neg_zero] at actual
  linarith

variable (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
  (closed : FiniteModeNegClosed frequencies) (nu : Viscosity)
  (advector : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality advector)

def dissipative : Module.End ℝ (physicalSpace frequencies) :=
  physicalOperator frequencies zeroNotMem closed nu 0 zero_reality

def laplacian : Module.End ℝ (physicalSpace frequencies) :=
  (-nu.coeff⁻¹) • dissipative frequencies zeroNotMem closed nu

def convection : Module.End ℝ (physicalSpace frequencies) :=
  physicalOperator frequencies zeroNotMem closed nu advector reality-
    dissipative frequencies zeroNotMem closed nu

theorem dissipative_pairing (x y : physicalSpace frequencies) :
    pairing frequencies x (dissipative frequencies zeroNotMem closed nu y) =
      -nu.coeff*curlPair frequencies x.1 y.1 := by
  rw [dissipative,operator_mixed_pairing,trilinear_zero]
  ring

theorem laplacian_pairing (x y : physicalSpace frequencies) :
    pairing frequencies x (laplacian frequencies zeroNotMem closed nu y) = curlPair frequencies x.1 y.1 := by
  rw [laplacian,LinearMap.smul_apply,map_smul,dissipative_pairing]
  simp only [smul_eq_mul]
  field_simp [nu.coeff_pos.ne']

theorem dissipative_adjoint (x y : physicalSpace frequencies) :
    pairing frequencies (dissipative frequencies zeroNotMem closed nu x) y =
      pairing frequencies x (dissipative frequencies zeroNotMem closed nu y) := by
  simpa only [dissipative,neg_zero] using
    operator_adjoint frequencies zeroNotMem closed nu 0 zero_reality x y

theorem operator_midpoint :
    physicalOperator frequencies zeroNotMem closed nu advector reality+
      physicalOperator frequencies zeroNotMem closed nu (-advector) (negative_reality reality) =
        (2 : ℝ) • dissipative frequencies zeroNotMem closed nu := by
  apply LinearMap.ext
  intro y
  apply sub_eq_zero.mp
  apply pairing_faithful frequencies
  have zero (x : physicalSpace frequencies) :
      pairing frequencies x (((physicalOperator frequencies zeroNotMem closed nu advector reality+
        physicalOperator frequencies zeroNotMem closed nu (-advector) (negative_reality reality)) y)-
          ((2 : ℝ) • dissipative frequencies zeroNotMem closed nu) y) = 0 := by
    simp only [LinearMap.add_apply,LinearMap.smul_apply,map_sub,map_add,map_smul,smul_eq_mul,
      operator_mixed_pairing,trilinear_negative,dissipative_pairing]
    ring
  exact (zero _).le

theorem dissipative_laplacian : dissipative frequencies zeroNotMem closed nu =
    (-nu.coeff) • laplacian frequencies zeroNotMem closed nu := by
  rw [laplacian,smul_smul]
  simp [nu.coeff_pos.ne']

theorem zero_convection (wave : IntegerWavevector) (field : ComplexVorticityHilbertState) :
    convectionCLM frequencies 0 wave field = 0 := by
  simp [convectionCLM,pairCLM,finiteStateVelocityCoefficient,biotSavartVelocityCoefficient]
  apply Finset.sum_eq_zero
  intro first _
  apply Finset.sum_eq_zero
  intro last _
  split_ifs <;> simp

theorem laplacian_row (field : physicalSpace frequencies) (wave : IntegerWavevector) :
    (laplacian frequencies zeroNotMem closed nu field).1 wave =
      integerWaveViscousMultiplier wave • field.1 wave := by
  change -nu.coeff⁻¹ • frozenOperator frequencies nu 0 field.1 wave = _
  rw [operator_apply,zero_convection]
  by_cases member : wave ∈ frequencies
  · rw [if_pos member,zero_sub,← neg_smul]
    change -nu.coeff⁻¹ • (transverseProjectionCLM wave) (-(nu.coeff*integerWaveViscousMultiplier wave) • field.1 wave) = _
    rw [map_smul]
    simp only [transverseProjectionCLM_apply]
    rw [transverseProjection_eq_self_of_transverse (fun zero => zeroNotMem (zero ▸ member))
      (physical_transverse field wave member),smul_smul]
    congr 1
    field_simp [nu.coeff_pos.ne']
  · rw [if_neg member,physical_supported field wave member]
    simp

theorem operator_split : physicalOperator frequencies zeroNotMem closed nu advector reality =
    (-nu.coeff) • laplacian frequencies zeroNotMem closed nu+
      convection frequencies zeroNotMem closed nu advector reality := by
  rw [← dissipative_laplacian,convection]
  abel

theorem adjoint_split : physicalOperator frequencies zeroNotMem closed nu (-advector) (negative_reality reality) =
    (-nu.coeff) • laplacian frequencies zeroNotMem closed nu-
      convection frequencies zeroNotMem closed nu advector reality := by
  have actual := operator_midpoint frequencies zeroNotMem closed nu advector reality
  rw [← dissipative_laplacian,convection]
  rw [two_smul] at actual
  calc
    _ = (physicalOperator frequencies zeroNotMem closed nu advector reality+
      physicalOperator frequencies zeroNotMem closed nu (-advector) (negative_reality reality))-
        physicalOperator frequencies zeroNotMem closed nu advector reality := by abel
    _ = _ := by rw [actual]; abel

theorem convection_pairing (x y : physicalSpace frequencies) :
    pairing frequencies x (convection frequencies zeroNotMem closed nu advector reality y) =
      finiteStateVelocityBilinearEnergyPairing frequencies (curlLift frequencies x.1) advector (curlLift frequencies y.1) := by
  simp only [convection,LinearMap.sub_apply,map_sub,operator_mixed_pairing,dissipative_pairing]
  ring

theorem convection_skew (x y : physicalSpace frequencies) :
    pairing frequencies (convection frequencies zeroNotMem closed nu advector reality x) y =
      -pairing frequencies x (convection frequencies zeroNotMem closed nu advector reality y) := by
  rw [convection,LinearMap.sub_apply,map_sub,LinearMap.sub_apply,
    operator_adjoint,dissipative_adjoint,adjoint_split frequencies zeroNotMem closed nu advector reality,
    ← dissipative_laplacian]
  simp only [convection,LinearMap.sub_apply,map_sub]
  ring

def lyapunov (test : Module.End ℝ (physicalSpace frequencies)) : Module.End ℝ (physicalSpace frequencies) :=
  (-nu.coeff) • ((laplacian frequencies zeroNotMem closed nu).comp test+
    test.comp (laplacian frequencies zeroNotMem closed nu))+
      (test.comp (convection frequencies zeroNotMem closed nu advector reality)-
        (convection frequencies zeroNotMem closed nu advector reality).comp test)

theorem lyapunov_original (test : Module.End ℝ (physicalSpace frequencies)) :
    lyapunov frequencies zeroNotMem closed nu advector reality test =
      (physicalOperator frequencies zeroNotMem closed nu (-advector) (negative_reality reality)).comp test+
        test.comp (physicalOperator frequencies zeroNotMem closed nu advector reality) := by
  rw [adjoint_split frequencies zeroNotMem closed nu advector reality,
    operator_split frequencies zeroNotMem closed nu advector reality]
  apply LinearMap.ext
  intro value
  simp only [lyapunov,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,map_add,map_smul]
  module

theorem whole_green (test : Module.End ℝ (physicalSpace frequencies)) (value : physicalSpace frequencies) :
    pairing frequencies (physicalOperator frequencies zeroNotMem closed nu advector reality value) (test value)+
      pairing frequencies value (test (physicalOperator frequencies zeroNotMem closed nu advector reality value)) =
        pairing frequencies value (lyapunov frequencies zeroNotMem closed nu advector reality test value) := by
  rw [lyapunov_original,operator_adjoint]
  simp only [LinearMap.add_apply,LinearMap.comp_apply,map_add]

end
end SaturationMonoid.NavierStokes.NativeWindowOperatorGreen
