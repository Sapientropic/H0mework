import H0mework.Physics.MotherSource.StaticGreen.HeatBounds

/-! Two integrations by parts on the original Cartesian carrier; no integrability receipts are inputs. -/

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open scoped SchwartzMap LineDeriv
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
noncomputable section

theorem heat_pairing_second (parameter : ℝ) (index : Fin 3) (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, spatialHeat parameter point*(∂_{axis index} (∂_{axis index} test)) point) =
      ∫ point : Point, heatSecond parameter index point*test point := by
  have first := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (heatFirst_mul_integrable parameter index (∂_{axis index} test))
    (spatialHeat_mul_integrable parameter (∂_{axis index} (∂_{axis index} test)))
    (spatialHeat_mul_integrable parameter (∂_{axis index} test))
    (fun point _ => spatialHeat_line parameter point index)
    (fun point _ => (SchwartzMap.hasFDerivAt (∂_{axis index} test) point).hasLineDerivAt (axis index))
  have second := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (heatSecond_mul_integrable parameter index test)
    (heatFirst_mul_integrable parameter index (∂_{axis index} test))
    (heatFirst_mul_integrable parameter index test)
    (fun point _ => heatFirst_line parameter point index)
    (fun point _ => (SchwartzMap.hasFDerivAt test point).hasLineDerivAt (axis index))
  change (∫ point : Point, spatialHeat parameter point*(∂_{axis index} (∂_{axis index} test)) point) =
      -(∫ point : Point, heatFirst parameter index point*(∂_{axis index} test) point) at first
  change (∫ point : Point, heatFirst parameter index point*(∂_{axis index} test) point) =
      -(∫ point : Point, heatSecond parameter index point*test point) at second
  rw [first, second, neg_neg]

theorem heat_pairing_laplacian (parameter : ℝ) (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, spatialHeat parameter point*testLaplacian test point) =
      ∫ point : Point, (4*parameter^4*(distance point)^2-6*parameter^2)*
        spatialHeat parameter point*test point := by
  simp only [testLaplacian, sum_apply, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    spatialHeat_mul_integrable parameter (∂_{axis i} (∂_{axis i} test)))]
  simp_rw [heat_pairing_second]
  rw [← integral_finsetSum Finset.univ (fun i _ => heatSecond_mul_integrable parameter i test)]
  simp only [← Finset.sum_mul, heatSecond_sum]

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
