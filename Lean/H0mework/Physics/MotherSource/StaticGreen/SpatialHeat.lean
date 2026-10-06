import H0mework.Physics.MotherSource.StaticGreen.HeatLimit
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! Coordinate derivatives of the same Gaussian and original-carrier Schwartz tests. -/

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open scoped SchwartzMap LineDeriv
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
noncomputable section

def axis (index : Fin 3) : Point := Pi.single index 1

def testLaplacian (test : 𝓢(Point, ℝ)) : 𝓢(Point, ℝ) :=
  ∑ index : Fin 3, ∂_{axis index} (∂_{axis index} test)

theorem distance_sq (point : Point) : distance point ^ 2 = ∑ i : Fin 3, point i ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (point i)))

theorem spatialHeat_hasFDerivAt (parameter : ℝ) (point : Point) :
    HasFDerivAt (spatialHeat parameter)
      (spatialHeat parameter point • (-parameter^2 •
        ∑ i : Fin 3, (2*point i) • (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ))) point := by
  have radius : HasFDerivAt (fun p : Point => ∑ i : Fin 3, p i ^ 2)
      (∑ i : Fin 3, (2*point i) • (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ)) point := by
    simpa using HasFDerivAt.fun_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) =>
      ((ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt (x := point)).pow 2)
  unfold spatialHeat
  simp_rw [distance_sq]
  exact (radius.const_mul (-parameter^2)).exp

def heatFirst (parameter : ℝ) (index : Fin 3) (point : Point) : ℝ :=
  -2*parameter^2*point index*spatialHeat parameter point

def heatSecond (parameter : ℝ) (index : Fin 3) (point : Point) : ℝ :=
  (4*parameter^4*(point index)^2-2*parameter^2)*spatialHeat parameter point

theorem spatialHeat_line (parameter : ℝ) (point : Point) (index : Fin 3) :
    HasLineDerivAt ℝ (spatialHeat parameter) (heatFirst parameter index point) point (axis index) := by
  have generated := (spatialHeat_hasFDerivAt parameter point).hasLineDerivAt (axis index)
  convert generated using 1 <;> try rfl
  simp [axis, heatFirst, Pi.single_apply]
  ring

theorem heatFirst_hasFDerivAt (parameter : ℝ) (point : Point) (index : Fin 3) :
    HasFDerivAt (heatFirst parameter index)
      ((-2*parameter^2*point index) •
        (spatialHeat parameter point • (-parameter^2 •
          ∑ i : Fin 3, (2*point i) • (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ))) +
        spatialHeat parameter point • ((-2*parameter^2) • (ContinuousLinearMap.proj index : Point →L[ℝ] ℝ))) point :=
  (((ContinuousLinearMap.proj index : Point →L[ℝ] ℝ).hasFDerivAt (x := point)).const_mul
    (-2*parameter^2)).fun_mul (spatialHeat_hasFDerivAt parameter point)

theorem heatFirst_line (parameter : ℝ) (point : Point) (index : Fin 3) :
    HasLineDerivAt ℝ (heatFirst parameter index) (heatSecond parameter index point) point (axis index) := by
  have generated := (heatFirst_hasFDerivAt parameter point index).hasLineDerivAt (axis index)
  convert generated using 1 <;> try rfl
  simp [axis, heatSecond, Pi.single_apply]
  ring

theorem heatSecond_sum (parameter : ℝ) (point : Point) :
    (∑ index : Fin 3, heatSecond parameter index point) =
      (4*parameter^4*(distance point)^2-6*parameter^2)*spatialHeat parameter point := by
  simp [heatSecond, distance_sq, Fin.sum_univ_three]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
