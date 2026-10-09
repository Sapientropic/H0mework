import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.FlowNoFold
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.ResponseNondegenerate
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open SourceGaussianModel TrueFlowDifferential TrueTubeWholeActual WholeCellPartition
open Set MeasureTheory
noncomputable section

theorem fullDomain_interior_nonempty : (interior fullDomain).Nonempty := by
  unfold fullDomain
  rw [← pi_univ_Icc, interior_pi_set (finite_univ : (univ : Set (Fin 3)).Finite)]
  simp only [interior_Icc]
  refine ⟨fun i => (fullLower i + fullUpper i) / 2, ?_⟩
  intro i _
  have ordered : fullLower i < fullUpper i := Rat.cast_lt.mpr (full_ordered i)
  constructor <;> dsimp only <;> linarith

theorem fullDomain_uniqueDiffOn : UniqueDiffOn ℝ fullDomain :=
  uniqueDiffOn_convex (convex_Icc fullLower fullUpper) fullDomain_interior_nonempty

/-- The canonical within-domain derivative reads the generated Jacobian on the full parameter box. -/
def actualDerivative (x : Point) : Point →L[ℝ] Point :=
  fderivWithin ℝ trueParameterMap fullDomain x

theorem actualDerivative_eq_trueJacobian (p : BandPoint) :
    actualDerivative p.val = trueJacobian p :=
  (actualMap_hasFDerivWithinAt p).fderivWithin (fullDomain_uniqueDiffOn p.val p.property)

theorem actualDerivative_hasFDerivWithinAt (x : Point) (inside : x ∈ fullDomain) :
    HasFDerivWithinAt trueParameterMap (actualDerivative x) fullDomain x :=
  (actualMap_hasFDerivWithinAt ⟨x, inside⟩).differentiableWithinAt.hasFDerivWithinAt

theorem trueParameterMap_continuousOn : ContinuousOn trueParameterMap fullDomain :=
  fun x hx => (actualDerivative_hasFDerivWithinAt x hx).continuousWithinAt

def truePatch : Set Point := trueParameterMap '' fullDomain

theorem truePatch_compact : IsCompact truePatch :=
  full_compact.image_of_continuousOn trueParameterMap_continuousOn

theorem truePatch_nonempty : truePatch.Nonempty := full_nonempty.image trueParameterMap

theorem truePatch_measurable : MeasurableSet truePatch := truePatch_compact.isClosed.measurableSet

theorem truePatch_volume_lt_top : volume truePatch < ⊤ := truePatch_compact.measure_lt_top

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
