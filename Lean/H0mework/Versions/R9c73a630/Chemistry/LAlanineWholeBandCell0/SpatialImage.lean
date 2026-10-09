import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.Nondegenerate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Spatial

open SourceGaussianModel WholeBandActual WholeBandGeometry WholeBandCell0Geometry
open WholeBandCell0Differential Set MeasureTheory
noncomputable section

theorem cell0_domain_compact : IsCompact (cellDomain 0) := by
  rw [cell0_domain_eq_Icc]
  exact isCompact_Icc

theorem cell0_domain_measurable : MeasurableSet (cellDomain 0) :=
  cell0_domain_compact.isClosed.measurableSet

def cell0_actualDerivative (x : Point) : Point →L[ℝ] Point :=
  fderivWithin ℝ cell0ParameterMap (cellDomain 0) x

theorem cell0_actualDerivative_eq_trueJacobian (p : Cell0Point) :
    cell0_actualDerivative p.val = cell0_trueJacobian p :=
  (cell0_trueJacobian_eq_fderivWithin p).symm

theorem cell0_actualDerivative_hasFDerivWithinAt (x : Point) (inside : x ∈ cellDomain 0) :
    HasFDerivWithinAt cell0ParameterMap (cell0_actualDerivative x) (cellDomain 0) x :=
  (cell0_actualMap_hasFDerivWithinAt ⟨x, inside⟩).differentiableWithinAt.hasFDerivWithinAt

theorem cell0ParameterMap_continuousOn : ContinuousOn cell0ParameterMap (cellDomain 0) :=
  fun x hx => (cell0_actualDerivative_hasFDerivWithinAt x hx).continuousWithinAt

def cell0_truePatch : Set Point := cell0ParameterMap '' cellDomain 0

theorem cell0_truePatch_compact : IsCompact cell0_truePatch :=
  cell0_domain_compact.image_of_continuousOn cell0ParameterMap_continuousOn

theorem cell0_truePatch_nonempty : cell0_truePatch.Nonempty :=
  (cellDomain_nonempty 0).image cell0ParameterMap

theorem cell0_truePatch_measurable : MeasurableSet cell0_truePatch :=
  cell0_truePatch_compact.isClosed.measurableSet

theorem cell0_truePatch_volume_lt_top : volume cell0_truePatch < ⊤ :=
  cell0_truePatch_compact.measure_lt_top

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Spatial
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
