import H0mework.NavierStokes.Heat.Maps
import H0mework.NavierStokes.Fourier.CanonicalExhaustiveGalerkinTarget

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.HeatPrimitive

open scoped BigOperators
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget

noncomputable section

abbrev RawField := IntegerWavevector → ComplexCoordinateVector

def row (nu : Viscosity) (p q : IntegerWavevector) (x : RawField) : Real :=
  HeatWork.work p q (x (p + q)) (x p) (x q) / HeatWork.heatWeight nu p q

def rowDifferential (nu : Viscosity) (p q : IntegerWavevector)
    (x h : RawField) : Real :=
  (HeatWork.work p q (h (p + q)) (x p) (x q) +
    HeatWork.work p q (x (p + q)) (h p) (x q) +
    HeatWork.work p q (x (p + q)) (x p) (h q)) / HeatWork.heatWeight nu p q

def heat (nu : Viscosity) (x : RawField) : RawField :=
  fun k => -(nu.coeff * integerWaveViscousMultiplier k) • x k

theorem rowDifferential_add (nu : Viscosity) (p q : IntegerWavevector)
    (x h g : RawField) :
    rowDifferential nu p q x (h + g) =
      rowDifferential nu p q x h + rowDifferential nu p q x g := by
  simp only [rowDifferential, Pi.add_apply, HeatCalculus.work_add_output,
    HeatCalculus.work_add_left, HeatCalculus.work_add_right]
  ring

theorem rowDifferential_heat (nu : Viscosity) (p q : IntegerWavevector)
    (x : RawField) (pNe : p ≠ 0) :
    rowDifferential nu p q x (heat nu x) =
      -HeatWork.work p q (x (p + q)) (x p) (x q) := by
  exact HeatWork.heat_primitive nu p q pNe (x (p + q)) (x p) (x q)

end
end SaturationMonoid.NavierStokes.HeatPrimitive
