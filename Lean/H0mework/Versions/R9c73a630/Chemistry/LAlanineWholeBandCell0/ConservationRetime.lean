import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.ConservationTimeIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient ContinuousSeed TrueFlowDifferential TrueFlowGeometry
open TrueFlowConservation WholeBandActual WholeBandGeometry WholeBandCell0Geometry WholeBandCell0Differential
open WholeBandCell0Continuation WholeCellBoundary
open Matrix Set MeasureTheory
noncomputable section

def cell0_retime (p : Cell0Point) (s : Time) : Cell0Point :=
  ⟨Function.update p.val 2 s, cell0_line_inside p 2 s.property⟩

@[simp] theorem cell0_retime_time (p : Cell0Point) (s : Time) : cell0_actualParameterTime (cell0_retime p s) = s := by
  apply Subtype.ext
  exact Function.update_self 2 s p.val

@[simp] theorem cell0_retime_seed (p : Cell0Point) (s : Time) :
    cellSeed 0 (cell0_retime p s).val =
      cellSeed 0 p.val := by
  simp only [cellSeed, bandSeed, bandU, cell0_retime,
    Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

@[simp] theorem cell0_retime_seedDerivative (p : Cell0Point) (s : Time) :
    cell0_seedFlowDerivative (cell0_retime p s) = cell0_seedFlowDerivative p := by
  unfold cell0_seedFlowDerivative
  rw [cell0_retime_seed]
  simp only [bandSeedDerivative, bandUDerivative, cell0_retime,
    Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

theorem cell0_retime_initialDerivative (p : Cell0Point) (s t : Time) :
    cell0_initialFlowDerivative (cell0_retime p s) t = cell0_initialFlowDerivative p t := by
  have derivative := cell0_initialFlow_hasStrictFDerivAt (cell0_retime p s) t
  rw [cell0_retime_seed] at derivative
  exact derivative.hasFDerivAt.unique (cell0_initialFlow_hasStrictFDerivAt p t).hasFDerivAt

theorem cell0_evolvingJacobian_eq_retimed (p : Cell0Point) (s : Time) :
    cell0_evolvingJacobian p s = LinearMap.toMatrix' (cell0_trueJacobian (cell0_retime p s)).toLinearMap := by
  rw [cell0_trueJacobian_flow_factorization]
  change cell0_evolvingJacobian p s =
    LinearMap.toMatrix' ((cell0_initialFlowDerivative (cell0_retime p s)
      (cell0_actualParameterTime (cell0_retime p s))).comp (cell0_seedFlowDerivative (cell0_retime p s))).toLinearMap
  rw [cell0_retime_time, cell0_retime_initialDerivative, cell0_retime_seedDerivative]
  ext i j
  change extendPath (cell0_sourceResponse p (cell0_seedFlowDerivative p (Pi.single j 1))) (s : ℝ) i =
    cell0_sourceResponse p (cell0_seedFlowDerivative p (Pi.single j 1)) s i
  rw [extendPath_coe]

theorem cell0_evolvingJacobian_det_ne_zero (p : Cell0Point) (s : Time) :
    (cell0_evolvingJacobian p s).det ≠ 0 := by
  rw [cell0_evolvingJacobian_eq_retimed, LinearMap.det_toMatrix']
  exact cell0_trueJacobian_det_ne_zero (cell0_retime p s)

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
