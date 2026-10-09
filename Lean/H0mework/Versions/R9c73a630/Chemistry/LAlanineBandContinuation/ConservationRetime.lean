import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ConservationVolumeEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandSource WholeBandGeometry
open TrueFlowDifferential WholeBandContinuation WholeBandContinuationDifferential
open WholeBandContinuationParameter Matrix Set
noncomputable section

def retime (p : Point) (s : Time) : Point := Function.update p 2 s

theorem retime_inside (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) (s : Time) :
    retime p s ∈ cellDomain c := by
  exact ⟨by simpa only [retime, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)] using inside.1,
    by simpa only [retime, Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)] using inside.2.1,
    by simpa only [retime, Function.update_self] using s.property⟩

@[simp] theorem retime_time (c : FullBandCell) (p : Point) (s : Time) (inside : retime p s ∈ cellDomain c) :
    actualParameterTime c (retime p s) inside = s := by
  apply Subtype.ext
  exact Function.update_self 2 s p

@[simp] theorem retime_seed (c : FullBandCell) (p : Point) (s : Time) :
    cellSeed c (retime p s) = cellSeed c p := by
  simp only [cellSeed, bandSeed, bandU, retime,
    Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

@[simp] theorem retime_seedDerivative (c : FullBandCell) (p : Point) (s : Time) :
    seedFlowDerivative c (retime p s) = seedFlowDerivative c p := by
  unfold seedFlowDerivative
  rw [retime_seed]
  simp only [bandSeedDerivative, bandUDerivative, retime,
    Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

@[simp] theorem retime_sourceResponse (c : FullBandCell) (p : Point) (s : Time) :
    sourceResponse c (retime p s) = sourceResponse c p := by
  simp only [WholeBandContinuationDifferential.sourceResponse,
    WholeBandContinuationDifferential.volterraHessian,
    WholeBandContinuationDifferential.pathHessian, retime_seed]

theorem retime_initialDerivative (c : FullBandCell) (p : Point) (s t : Time) :
    initialFlowDerivative c (retime p s) t = initialFlowDerivative c p t := by
  simp only [WholeBandContinuationDifferential.initialFlowDerivative, retime_sourceResponse]

theorem evolvingJacobian_eq_retimed (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (s : Time) :
    evolvingJacobian c p s = LinearMap.toMatrix' (trueJacobian c (retime p s)).toLinearMap := by
  rw [trueJacobian_flow_factorization c fields bounds (retime p s) (retime_inside c p inside s)]
  rw [retime_time, retime_initialDerivative, retime_seedDerivative]
  ext i j
  change extendPath (sourceResponse c p (seedFlowDerivative c p (Pi.single j 1))) (s : ℝ) i =
    sourceResponse c p (seedFlowDerivative c p (Pi.single j 1)) s i
  rw [extendPath_coe]

theorem evolvingJacobian_det_ne_zero (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) (s : Time) :
    (evolvingJacobian c p s).det ≠ 0 := by
  rw [evolvingJacobian_eq_retimed c fields bounds p inside s, LinearMap.det_toMatrix']
  exact trueJacobian_det_ne_zero c fields bounds positive _ (retime_inside c p inside s)

end
end LAlanine40K2025.BasinRefinement.WholeBandConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
