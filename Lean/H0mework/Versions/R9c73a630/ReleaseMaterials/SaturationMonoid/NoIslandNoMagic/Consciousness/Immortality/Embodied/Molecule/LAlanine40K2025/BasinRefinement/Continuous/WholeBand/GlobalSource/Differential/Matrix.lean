import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Variational
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowConservation.SourceVolumeEvolution

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel SourceFiniteData ContinuousGradient Matrix Set
open _root_.LAlanineTrueFlowDifferential
noncomputable section

def responseMatrix (x : Point) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => responseCurve x (Pi.single j 1) t i

theorem responseMatrix_actual (x : Point) (t : Time) :
    responseMatrix x t = LinearMap.toMatrix' (flowDerivative x t).toLinearMap := by
  ext i j
  change responseCurve x (Pi.single j 1) t i = response x (Pi.single j 1) t i
  rw [responseCurve_actual]

theorem responseMatrix_starts (x : Point) : responseMatrix x 0 = 1 := by
  rw [show (0 : ℝ) = (zeroTime : ℝ) from rfl,responseMatrix_actual,flowDerivative_zero]
  simp

theorem responseMatrix_variational (x : Point) (t : Time) (i j : Fin 3) :
    HasDerivAt (fun u => responseMatrix x u i j)
      (((spatialStep • TrueFlowConservation.hessianMatrix (actualPath x t)) * responseMatrix x t) i j) (t : ℝ) := by
  have result := hasDerivAt_pi.mp (original_variational x (Pi.single j 1) t) i
  change HasDerivAt (fun u => responseMatrix x u i j) (derivative (actualPath x t) (response x (Pi.single j 1) t) i) (t : ℝ) at result
  simp only [derivative,_root_.smul_apply,Pi.smul_apply,smul_eq_mul,sourceHessianLinear_apply] at result
  convert! result using 1
  simp only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul,TrueFlowConservation.hessianMatrix,
    responseMatrix,responseCurve_actual,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem response_determinant_evolution (x : Point) (t : Time) :
    HasDerivAt (fun u => (responseMatrix x u).det)
      (spatialStep * laplacian sourceTerms densityMatrix (actualPath x t) * (responseMatrix x t).det) (t : ℝ) := by
  have result := _root_.LAlanineTrueFlowConservation.determinant_evolution (responseMatrix x)
    (spatialStep • TrueFlowConservation.hessianMatrix (actualPath x t)) univ t
    (fun i j => (responseMatrix_variational x t i j).hasDerivWithinAt)
  have derivative := result.hasDerivAt (Filter.univ_mem)
  simpa only [Matrix.trace_smul,smul_eq_mul,TrueFlowConservation.sourceHessian_trace] using derivative

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
