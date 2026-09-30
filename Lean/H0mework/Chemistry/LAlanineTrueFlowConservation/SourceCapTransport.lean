import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceRetime
import H0mework.Chemistry.LAlanineTrueFlowBoundary.SourceCapFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueFlowDifferential TrueFlowBoundary TrueTubeWholeActual
open WholeCellBoundary WholeCellPartition Set MeasureTheory
noncomputable section

def capTime (upper : Bool) : Time := ⟨if upper then 1 / 2 else -(1 / 2), by
  cases upper <;> constructor <;> norm_num⟩

def capBase (p : BandPoint) : FacePoint := fun i => p.val ((2 : Fin 3).succAbove i)

theorem capBase_mem (p : BandPoint) : capBase p ∈ faceDomain 2 := by
  constructor
  · intro i
    exact p.property.1 _
  · intro i
    exact p.property.2 _

theorem retime_eq_cap (p : BandPoint) (upper : Bool) :
    retime p (capTime upper) = trueFaceParameter (2, upper) (capBase p) (capBase_mem p) := by
  apply Subtype.ext
  ext i
  fin_cases i
  · rfl
  · rfl
  · change (if upper then (1 / 2 : ℝ) else -(1 / 2)) = faceCoordinate (2, upper)
    cases upper <;> norm_num [faceCoordinate, fullLower, fullLowerQ, fullUpper, fullUpperQ, halfFlow_exact]

theorem capFlux_eq_evolvingJacobian (p : BandPoint) (upper : Bool) :
    trueFaceFlux (2, upper) (capBase p) (capBase_mem p) =
      (if upper then 1 else -1 : ℝ) * (evolvingJacobian p (capTime upper)).det := by
  rw [trueCapFlux_eq_oriented_det _ _ _ rfl, evolvingJacobian_eq_retimed,
    LinearMap.det_toMatrix', retime_eq_cap]

/-- A single original trajectory joins its two actual boundary caps through the source Laplacian. -/
theorem actual_time_integral_eq_cap_flux (p : BandPoint) :
    (∫ t in (-(1 / 2) : ℝ)..(1 / 2), signedVolumeRate p t) =
      trueFaceFlux (2, true) (capBase p) (capBase_mem p) +
        trueFaceFlux (2, false) (capBase p) (capBase_mem p) := by
  rw [actual_time_integral_eq_det_difference, capFlux_eq_evolvingJacobian,
    capFlux_eq_evolvingJacobian]
  simp only [Bool.false_eq_true, ↓reduceIte, capTime, one_mul, neg_mul, sub_eq_add_neg]

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
