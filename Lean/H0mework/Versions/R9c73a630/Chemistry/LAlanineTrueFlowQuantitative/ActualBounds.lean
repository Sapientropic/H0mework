import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowQuantitative.SourceTrace
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.SpatialImage

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitative

open SourceGaussianModel SourceFiniteData SourceSignedEvaluator
open TrueTubeSource TrueTubeActual TrueTubeWholeActual TrueTubeWholeChecks
open TrueFlowDifferential TrueFlowGeometry WholeCellPartition Set
noncomputable section

theorem directionalFlow_laplacian_bounds (d : Direction) (initial : InitialAt d)
    (t : ℝ) (time : t ∈ Icc (0 : ℝ) (1 / 2)) :
    (-(3 / 4) : ℝ) < laplacian sourceTerms densityMatrix (wholeDirectionalFlow d initial t) ∧
      laplacian sourceTerms densityMatrix (wholeDirectionalFlow d initial t) < -(1 / 4) := by
  obtain ⟨i, hi⟩ := sixteen_intervals_cover t time
  have localTime : t - stepOffset i ∈ Icc 0 (stepSize : ℝ) := by
    constructor <;> linarith [hi.1, hi.2]
  have bounded := wholeDirectionalFlow_tubes d initial i (t - stepOffset i) localTime
  rw [sub_add_cancel] at bounded
  exact actual_call_laplacian_bounds (TrueTubeWholeSource.tubeCallAt d i) _
    ((tube_call_box d i).symm ▸ bounded)

theorem fullFlow_laplacian_bounds (p : BandPoint) (t : ℝ)
    (time : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    (-(3 / 4) : ℝ) < laplacian sourceTerms densityMatrix (fullFlow p t) ∧
      laplacian sourceTerms densityMatrix (fullFlow p t) < -(1 / 4) :=
  LAlanineTrueTube.Signed.full_mem
    (negative := negativeFlow p) (positive := positiveFlow p)
    (domain := {x : Point | (-(3 / 4) : ℝ) < laplacian sourceTerms densityMatrix x ∧
      laplacian sourceTerms densityMatrix x < -(1 / 4)})
    (fun s hs => directionalFlow_laplacian_bounds 0 (bandInitial 0 p) s hs)
    (fun s hs => directionalFlow_laplacian_bounds 1 (bandInitial 1 p) s hs) time

theorem trueParameterMap_laplacian_bounds (p : Point) (inside : p ∈ fullDomain) :
    (-(3 / 4) : ℝ) < laplacian sourceTerms densityMatrix (trueParameterMap p) ∧
      laplacian sourceTerms densityMatrix (trueParameterMap p) < -(1 / 4) :=
  fullFlow_laplacian_bounds ⟨p, inside⟩ (p 2) (actualParameterTime ⟨p, inside⟩).property

theorem truePatch_laplacian_bounds (x : Point) (inside : x ∈ truePatch) :
    (-(3 / 4) : ℝ) < laplacian sourceTerms densityMatrix x ∧
      laplacian sourceTerms densityMatrix x < -(1 / 4) := by
  obtain ⟨p, hp, rfl⟩ := inside
  exact trueParameterMap_laplacian_bounds p hp

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitative
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
