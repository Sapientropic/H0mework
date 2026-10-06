import H0mework.Versions.AB.Physics.MotherSource.HyperchargeResponse.Mother

/-! All P286 temporal potentials on the same original U configuration. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open Stage9C.Material.SpinPair
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

abbrev Potential := BasePoint → P286LieBlockData

/-- The full Lie-valued temporal connection varies; all other primitive fields remain original. -/
def primitive (potential : Potential) : StageNineHolonomicConfiguration :=
  { Stage10.Runtime.configuration with
    gaugeConnection := fun point direction =>
      Stage10.Runtime.configuration.gaugeConnection point direction +
        if direction = 0 then potential point else 0 }

def configuration (potential : Potential) : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout Stage10.Runtime.source (primitive potential)

def derivative (potential : Potential) (point : BasePoint) (direction : LorentzianIndex) :
    P286LieBlockData :=
  p286CoordinateEquiv.symm
    (fieldDirectionalDerivative (fun p => p286CoordinateEquiv (potential p)) point direction)

theorem connection_derivative (potential : Potential) (point : BasePoint)
    (d f : LorentzianIndex) :
    p286ConnectionDerivative (primitive potential) point d f =
      if f = 0 then derivative potential point d else 0 := by
  have original : Stage10.Runtime.configuration.gaugeConnection = fun _ => gaugePotential gaugeScale := by
    rw [Stage10.Runtime.configuration_eq, actual_gaugeConnection]
  unfold p286ConnectionDerivative
  simp only [primitive, original, map_add]
  by_cases zero : f = 0
  · subst f
    simp only [ite_true, gaugePotential, Matrix.cons_val_zero, map_zero, zero_add]
    rfl
  · simp [zero, fieldDirectionalDerivative]

def electric (potential : Potential) (point : BasePoint) (axis : Fin 3) : P286LieBlockData :=
  -derivative potential point axis.succ +
    p286LieBracket (potential point) (gaugeScale • sourceColorP286Generator axis)

def electricForm (field : Fin 3 → P286LieBlockData) : Fin 6 → P286LieBlockData :=
  ![field 0, field 1, field 2, 0, 0, 0]

theorem bracket_zero_left (data : P286LieBlockData) : p286LieBracket 0 data = 0 := by
  ext <;> simp [p286LieBracket, suLieBracket]

theorem bracket_zero_right (data : P286LieBlockData) : p286LieBracket data 0 = 0 := by
  ext <;> simp [p286LieBracket, suLieBracket]

/-- The actual covariant spatial derivative of the entire P286 temporal potential. -/
theorem curvature (potential : Potential) (point : BasePoint) :
    holonomicGaugeCurvature (primitive potential) point =
      magneticCurvature gaugeScale + electricForm (electric potential point) := by
  have original : holonomicGaugeCurvature Stage10.Runtime.configuration point =
      magneticCurvature gaugeScale := by
    rw [Stage10.Runtime.configuration_eq, actual_gaugeCurvature]
  have originalDerivative (first second : LorentzianIndex) :
      p286ConnectionDerivative Stage10.Runtime.configuration point first second = 0 := by
    rw [Stage10.Runtime.configuration_eq]
    simp [p286ConnectionDerivative, actual_gaugeConnection, fieldDirectionalDerivative]
  rw [← original]
  funext pair
  simp only [holonomicGaugeCurvature, connection_derivative potential point,
    originalDerivative, sub_self, zero_add, Pi.add_apply]
  fin_cases pair <;>
    simp [pairFirst, pairSecond, electricForm, electric, primitive,
      Stage10.Runtime.configuration_eq, actual_gaugeConnection, gaugePotential,
      bracket_zero_left]

end
end SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
