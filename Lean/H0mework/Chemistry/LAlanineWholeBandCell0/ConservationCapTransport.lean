import H0mework.Chemistry.LAlanineWholeBandCell0.ConservationRetime
import H0mework.Chemistry.LAlanineWholeBandCell0.BoundaryCapFlux
import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceCapTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient ContinuousSeed TrueFlowDifferential TrueFlowGeometry
open TrueFlowConservation WholeBandActual WholeBandGeometry WholeBandCell0Geometry WholeBandCell0Differential
open WholeBandCell0Continuation WholeBandCell0Spatial WholeBandCell0Boundary WholeCellBoundary
open Matrix Set MeasureTheory
noncomputable section

def cell0_capBase (p : Cell0Point) : FacePoint := fun i => p.val ((2 : Fin 3).succAbove i)

theorem cell0_capBase_mem (p : Cell0Point) : cell0_capBase p ∈ cell0_faceDomain 2 :=
  ⟨fun i => (cell0_coordinate_mem p ((2 : Fin 3).succAbove i)).1,
    fun i => (cell0_coordinate_mem p ((2 : Fin 3).succAbove i)).2⟩

theorem cell0_retime_eq_cap (p : Cell0Point) (upper : Bool) :
    cell0_retime p (capTime upper) = cell0_trueFaceParameter (2, upper) (cell0_capBase p) (cell0_capBase_mem p) := by
  apply Subtype.ext
  ext i
  fin_cases i
  · rfl
  · rfl
  · change (if upper then (1 / 2 : ℝ) else -(1 / 2)) = cell0_faceCoordinate (2, upper)
    cases upper <;> rfl

theorem cell0_capFlux_eq_evolvingJacobian (p : Cell0Point) (upper : Bool) :
    cell0_trueFaceFlux (2, upper) (cell0_capBase p) (cell0_capBase_mem p) =
      (if upper then 1 else -1 : ℝ) * (cell0_evolvingJacobian p (capTime upper)).det := by
  rw [cell0_trueCapFlux_eq_oriented_det _ _ _ rfl, cell0_evolvingJacobian_eq_retimed,
    LinearMap.det_toMatrix', cell0_retime_eq_cap]

/-- A single original trajectory joins its two actual boundary caps through the source Laplacian. -/
theorem cell0_actual_time_integral_eq_cap_flux (p : Cell0Point) :
    (∫ t in (-(1 / 2) : ℝ)..(1 / 2), cell0_signedVolumeRate p t) =
      cell0_trueFaceFlux (2, true) (cell0_capBase p) (cell0_capBase_mem p) +
        cell0_trueFaceFlux (2, false) (cell0_capBase p) (cell0_capBase_mem p) := by
  rw [cell0_actual_time_integral_eq_det_difference, cell0_capFlux_eq_evolvingJacobian,
    cell0_capFlux_eq_evolvingJacobian]
  simp only [Bool.false_eq_true, ↓reduceIte, capTime, one_mul, neg_mul, sub_eq_add_neg]

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
