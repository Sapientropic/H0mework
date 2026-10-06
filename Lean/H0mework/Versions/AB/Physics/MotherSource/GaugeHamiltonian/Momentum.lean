import H0mework.Versions.AB.Physics.MotherSource.CanonicalGauss.Poisson

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.GaugeHamiltonian
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeConnectionLocalVariation StageNineTopologicalFourFormPairing
open StageNineTopologicalP286GaugeThreeFormDuality StageNineFormNativeGaugeWedge
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open Stage9C.Material.SpinPair
open TemporalGauge
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def spatialVariation (velocity : Fin 3 → P286LieBlockData) : P286GaugeOneForm :=
  ![0, p286CoordinateEquiv (velocity 0), p286CoordinateEquiv (velocity 1), p286CoordinateEquiv (velocity 2)]

def timeVariation (point : BasePoint) (velocity : Fin 3 → P286LieBlockData) : BasePoint → P286GaugeOneForm :=
  fun candidate => (candidate 0-point 0) • spatialVariation velocity

theorem timeVariation_zero (point : BasePoint) (velocity : Fin 3 → P286LieBlockData) :
    timeVariation point velocity point = 0 := by simp [timeVariation]

theorem timeVariation_derivative (point : BasePoint) (velocity : Fin 3 → P286LieBlockData)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative (timeVariation point velocity) point derivativeDirection formDirection =
      if derivativeDirection = 0 then spatialVariation velocity formDirection else 0 := by
  unfold p286GaugeVariationCoordinateDerivative timeVariation fieldDirectionalDerivative
  simp only [Pi.smul_apply]
  have coordinate : HasFDerivAt (fun candidate : BasePoint => candidate 0-point 0)
      (EuclideanSpace.proj 0 : BasePoint →L[ℝ] ℝ) point :=
    (EuclideanSpace.proj 0 : BasePoint →L[ℝ] ℝ).hasFDerivAt.sub_const _
  rw [(coordinate.smul_const (spatialVariation velocity formDirection)).fderiv]
  simp [coordinateDirection, eq_comm]

theorem timeVariation_curvature (point : BasePoint) (velocity : Fin 3 → P286LieBlockData) :
    p286GaugeConnectionExteriorDerivativeVariation (timeVariation point velocity) point =
      ![p286CoordinateEquiv (velocity 0), p286CoordinateEquiv (velocity 1),
        p286CoordinateEquiv (velocity 2), 0, 0, 0] := by
  funext pair
  unfold p286GaugeConnectionExteriorDerivativeVariation
  simp only [timeVariation_derivative]
  fin_cases pair <;> simp [pairFirst, pairSecond, spatialVariation]

private theorem auxiliary_normal (background : StageNineHolonomicConfiguration) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
      (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator background) point =
      holonomicP286GaugeAuxiliaryCoordinate background point := rfl

/-- The BF coefficient of the actual temporal connection path; `Action` proves its derivative provenance at the complete Dirac-dual root. -/
def momentum (potential : Potential) (point : BasePoint) (velocity : Fin 3 → P286LieBlockData) : ℝ :=
  formNativeP286GaugeConnectionBFFirstVariationDensity
    (toContinuumPointField (CanonicalGauss.configuration potential) point)
    (p286GaugeConnectionExteriorDerivativeVariation (timeVariation point velocity) point)

theorem momentum_readout (potential : Potential) (point : BasePoint) (velocity : Fin 3 → P286LieBlockData) :
    momentum potential point velocity =
      2*lapse*∑ i : Fin 3, formNativeP286LiePairing (electric potential point i) (velocity i) := by
  unfold momentum
  rw [formNativeP286GaugeConnectionBFFirstVariationDensity_eq_coordinate, timeVariation_curvature]
  change StageNineTopologicalFourFormPairing.generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
    (holonomicP286GaugeAuxiliaryCoordinate (CanonicalGauss.configuration potential) point) _ = _
  rw [CanonicalGauss.configuration, auxiliary_normal, auxiliary_coordinates]
  simp [generatedTwoFormWedgeCoefficient, Fin.sum_univ_six, twoFormComplement,
    p286CoordinateLiePairing, formNativeP286LiePairing,
    p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing, Fin.sum_univ_three]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeHamiltonian
