import H0mework.Physics.CompositeSpectrum.Action

/-! The magnetic helicity/current composite is generated from the actual
connection, curvature, and covariant derivative. Its trace is over all seven
mother coordinates. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineFormNativeP286GaugeGeometricKinematics
open StageNineP286GaugeAuxiliaryVariation
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage9C.Material.SpinPair Stage9DEF

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def magnetic (point : BasePoint) (axis : Fin 3) : P286LieBlockData :=
  holonomicGaugeCurvature Runtime.configuration point (magneticPair axis)

def curvatureCoordinates (point : BasePoint) : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv (holonomicGaugeCurvature Runtime.configuration point pair)

def curvatureDerivative (point : BasePoint) (direction : LorentzianIndex) : P286GaugeTwoForm :=
  fieldDirectionalDerivative curvatureCoordinates point direction

def covariantDerivative (point : BasePoint) (direction axis : Fin 3) : P286LieBlockData :=
  p286CoordinateEquiv.symm
    (pointwiseP286GaugeTwoFormCovariantDerivative
      (holonomicP286GaugeConnectionCoordinate Runtime.configuration point)
      (curvatureCoordinates point) (curvatureDerivative point) direction.succ (magneticPair axis))

def covariantCurl (point : BasePoint) : Fin 3 → P286LieBlockData :=
  ![covariantDerivative point 1 2 - covariantDerivative point 2 1,
    covariantDerivative point 2 0 - covariantDerivative point 0 2,
    covariantDerivative point 0 1 - covariantDerivative point 1 0]

def motherMagnetic (point : BasePoint) (axis : Fin 3) : Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  p286LieBlockEmbed (magnetic point axis)

def motherCurl (point : BasePoint) (axis : Fin 3) : Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  p286LieBlockEmbed (covariantCurl point axis)

def value (point : BasePoint) : ℂ :=
  ∑ axis : Fin 3, (motherMagnetic point axis * motherCurl point axis).trace

theorem magnetic_eq (point : BasePoint) (axis : Fin 3) :
    magnetic point axis = -(gaugeScale ^ 2) • sourceColorP286Generator axis := by
  rw [magnetic, Runtime.configuration_eq]
  exact actual_magnetic_component point axis

theorem curvatureDerivative_zero (point : BasePoint) (direction : LorentzianIndex) :
    curvatureDerivative point direction = 0 := by
  have constant : curvatureCoordinates = fun _ pair => p286CoordinateEquiv (magneticCurvature gaugeScale pair) := by
    funext candidate pair
    rw [curvatureCoordinates, Runtime.configuration_eq, actual_gaugeCurvature]
  rw [curvatureDerivative, fieldDirectionalDerivative, constant]
  rw [(hasFDerivAt_const (𝕜 := ℝ)
    (fun pair => p286CoordinateEquiv (magneticCurvature gaugeScale pair)) point).fderiv]
  rfl

theorem covariantDerivative_eq (point : BasePoint) (direction axis : Fin 3) :
    covariantDerivative point direction axis = -(gaugeScale ^ 3) •
      p286LieBracket (sourceColorP286Generator direction) (sourceColorP286Generator axis) := by
  unfold covariantDerivative pointwiseP286GaugeTwoFormCovariantDerivative
  rw [curvatureDerivative_zero, zero_add]
  simp only [p286GaugeTwoFormAdjoint, holonomicP286GaugeConnectionCoordinate,
    curvatureCoordinates, p286CoordinateLieBracket,
    p286CoordinateEquiv.symm_apply_apply, Runtime.configuration_eq]
  rw [Compatibility.actual_connection_source, actual_magnetic_component,
    p286LieBracket_smul_left, p286LieBracket_smul_right, smul_smul]
  congr 1
  ring

theorem covariantCurl_eq (point : BasePoint) (axis : Fin 3) :
    covariantCurl point axis = (2 * gaugeScale ^ 3) • sourceColorP286Generator axis := by
  unfold covariantCurl
  simp_rw [covariantDerivative_eq, sourceColorP286Generator_bracket]
  fin_cases axis <;> simp <;> module

theorem motherGenerator_trace_square (axis : Fin 3) :
    ((p286LieBlockEmbed (sourceColorP286Generator axis) : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
      (p286LieBlockEmbed (sourceColorP286Generator axis) : Matrix SU7MotherIndex SU7MotherIndex ℂ)).trace = -1 / 2 := by
  change (rawP286LieBlock (sourceColorP286Generator axis) *
    rawP286LieBlock (sourceColorP286Generator axis)).trace = _
  fin_cases axis <;>
    norm_num [rawP286LieBlock, weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
      sourceColorP286Generator_color, sourceColorP286Generator_weak_zero,
      sourceColorP286Generator_hypercharge_zero, Matrix.fromBlocks_multiply,
      Matrix.trace, Matrix.mul_apply, sourceColorRaw, Fin.sum_univ_three]
  all_goals ring_nf; simp [Complex.I_sq, div_eq_mul_inv]

theorem value_eq (point : BasePoint) : value point = (3 * gaugeScale ^ 5 : ℝ) := by
  unfold value motherMagnetic motherCurl
  simp_rw [magnetic_eq, covariantCurl_eq, p286LieBlockEmbed_real_smul]
  simp only [SetLike.val_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, motherGenerator_trace_square, Fin.sum_univ_three, Complex.real_smul]
  push_cast
  ring

theorem value_nonzero (point : BasePoint) : value point ≠ 0 := by
  rw [value_eq]
  exact_mod_cast ne_of_gt (mul_pos (by norm_num) (pow_pos gaugeScale_pos 5))

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
