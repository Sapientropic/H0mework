import H0mework.Physics.MatrixResponse.Value

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse

open Matrix Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineP286GaugeConnectionVariation Helicity

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def potential (M : Coefficients) : LorentzianIndex → P286LieBlockData :=
  ![0, color (M 0), color (M 1), color (M 2)]

def configuration (M : Coefficients) : StageNineHolonomicConfiguration :=
  { Runtime.configuration with gaugeConnection := fun _ => potential M }

theorem color_scalar (r : ℝ) (axis : Fin 3) :
    color ((r • (1 : Coefficients)) axis) = r • sourceColorP286Generator axis := by
  fin_cases axis <;> simp [color]

theorem potential_scalar (r : ℝ) : potential (r • (1 : Coefficients)) = gaugePotential r := by
  funext axis
  fin_cases axis <;> simp [potential, color_scalar, gaugePotential]

theorem configuration_source : configuration (gaugeScale • (1 : Coefficients)) = Runtime.configuration := by
  unfold configuration
  have h : (fun _ : BasePoint => potential (gaugeScale • (1 : Coefficients))) =
      Runtime.configuration.gaugeConnection := by
    rw [potential_scalar, Runtime.configuration_eq, actual_gaugeConnection]
  rw [h]

theorem constant_derivative (M : Coefficients) (point : BasePoint) (i j : LorentzianIndex) :
    p286ConnectionDerivative (configuration M) point i j = 0 := by
  unfold p286ConnectionDerivative fieldDirectionalDerivative configuration
  rw [(hasFDerivAt_const (𝕜 := ℝ) (p286CoordinateEquiv (potential M j)) point).fderiv]
  simp

theorem curvature_magnetic (M : Coefficients) (point : BasePoint) (axis : Fin 3) :
    (p286LieBlockEmbed (holonomicGaugeCurvature (configuration M) point (magneticPair axis)) :
      MotherMatrix) = magnetic M axis := by
  unfold holonomicGaugeCurvature
  simp only [constant_derivative, sub_self, zero_add]
  fin_cases axis <;>
    simp [magneticPair, pairFirst, pairSecond, configuration, potential,
      magnetic, connection, mother, p286LieBlockEmbed_bracket, bracket, suLieBracket]

theorem connection_source (point : BasePoint) :
    connection (gaugeScale • (1 : Coefficients)) = connectionMatrix point := by
  funext axis
  simp only [connection, mother, color_scalar, connectionMatrix, Runtime.configuration_eq,
    Stage9DEF.Compatibility.actual_connection_source]

theorem magnetic_source (point : BasePoint) :
    magnetic (gaugeScale • (1 : Coefficients)) = motherMagnetic point := by
  funext axis
  rw [← curvature_magnetic _ point, configuration_source]
  rfl

theorem actual_source_value (point : BasePoint) :
    value (gaugeScale • (1 : Coefficients)) = Helicity.value point := by
  rw [value, connection_source point, magnetic_source point, ← value_homogeneous]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse
