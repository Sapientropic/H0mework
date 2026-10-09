import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ParameterNondegenerate
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowConservation.SourceVolumeEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient WholeBandSource WholeBandGeometry
open TrueFlowDifferential TrueFlowConservation WholeBandContinuation WholeBandContinuationDifferential
open WholeBandContinuationParameter Matrix Set MeasureTheory
noncomputable section

def evolvingJacobian (c : FullBandCell) (p : Point) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => extendPath (sourceResponse c p (seedFlowDerivative c p (Pi.single j 1))) t i

theorem evolvingJacobian_variational (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (s : Time) (i j : Fin 3) :
    HasDerivWithinAt (fun t => evolvingJacobian c p t i j)
      ((hessianMatrix (rawPath (cellSeed c p) s) * evolvingJacobian c p s) i j)
      (Icc (-(1/2 : ℝ)) (1/2)) (s : ℝ) := by
  have derivative := hasDerivWithinAt_pi.mp
    (sourceResponse_actual_variational c fields bounds p inside (seedFlowDerivative c p (Pi.single j 1)) s) i
  simpa only [sourceHessianLinear_apply, Matrix.mul_apply, hessianMatrix, evolvingJacobian,
    extendPath_coe] using derivative

theorem evolvingJacobian_determinant_evolution (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (s : Time) :
    HasDerivWithinAt (fun t => (evolvingJacobian c p t).det)
      (laplacian sourceTerms densityMatrix (rawPath (cellSeed c p) s) * (evolvingJacobian c p s).det)
      (Icc (-(1/2 : ℝ)) (1/2)) (s : ℝ) := by
  rw [← sourceHessian_trace]
  exact _root_.LAlanineTrueFlowConservation.determinant_evolution
    (evolvingJacobian c p) (hessianMatrix (rawPath (cellSeed c p) s)) _ s
    (evolvingJacobian_variational c fields bounds p inside s)

theorem evolvingJacobian_is_actual (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    evolvingJacobian c p (actualParameterTime c p inside) = LinearMap.toMatrix' (trueJacobian c p).toLinearMap := by
  ext i j
  rw [trueJacobian_flow_factorization c fields bounds p inside]
  change extendPath (sourceResponse c p (seedFlowDerivative c p (Pi.single j 1)))
    (actualParameterTime c p inside : ℝ) i = sourceResponse c p (seedFlowDerivative c p (Pi.single j 1))
    (actualParameterTime c p inside) i
  rw [extendPath_coe]

theorem evolvingJacobian_det_is_actual (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    (evolvingJacobian c p (actualParameterTime c p inside)).det = LinearMap.det (trueJacobian c p).toLinearMap := by
  rw [evolvingJacobian_is_actual c fields bounds p inside, LinearMap.det_toMatrix']

end
end LAlanine40K2025.BasinRefinement.WholeBandConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
