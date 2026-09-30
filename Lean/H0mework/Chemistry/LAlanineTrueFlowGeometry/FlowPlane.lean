import H0mework.Chemistry.LAlanineTrueFlowGeometry.SeedWholeTransverse
import H0mework.Chemistry.LAlanineTrueFlowGeometry.SeedAlgebra
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open SourceGaussianModel SourceSignedEvaluator ContinuousGradient ContinuousSeed Matrix
open TrueTubeSource TrueTubeActual TrueTubeWholeActual TrueTubeWholeChecks Set
open scoped Matrix
noncomputable section

theorem directionalFlow_transverse (d : Direction) (initial : InitialAt d)
    (t : ℝ) (time : t ∈ Icc (0 : ℝ) (1 / 2)) :
    0 < seedNormal ⬝ᵥ sourceGradient (wholeDirectionalFlow d initial t) := by
  obtain ⟨i, hi⟩ := sixteen_intervals_cover t time
  have localTime : t - stepOffset i ∈ Icc 0 (stepSize : ℝ) := by
    constructor <;> linarith [hi.1, hi.2]
  have bounded := wholeDirectionalFlow_tubes d initial i (t - stepOffset i) localTime
  rw [sub_add_cancel] at bounded
  exact actual_call_transverse (TrueTubeWholeSource.tubeCallAt d i) _
    ((tube_call_box d i).symm ▸ bounded)

theorem fullFlow_transverse (p : BandPoint) (t : ℝ)
    (time : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    0 < seedNormal ⬝ᵥ sourceGradient (fullFlow p t) :=
  LAlanineTrueTube.Signed.full_mem
    (negative := negativeFlow p) (positive := positiveFlow p)
    (domain := {x : Point | 0 < seedNormal ⬝ᵥ sourceGradient x})
    (fun s hs => directionalFlow_transverse 0 (bandInitial 0 p) s hs)
    (fun s hs => directionalFlow_transverse 1 (bandInitial 1 p) s hs) time

def normalRead : Point →L[ℝ] ℝ := ∑ i : Fin 3, seedNormal i • ContinuousLinearMap.proj i

theorem normalRead_apply (x : Point) : normalRead x = seedNormal ⬝ᵥ x := by
  simp only [normalRead, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct]

def planeCoordinate (x : Point) : ℝ := normalRead (x - centre)

theorem seed_plane_zero (p : Point) :
    planeCoordinate (ContinuousParameterMap.initialMap 0 4 p) = 0 := by
  rw [planeCoordinate, normalRead_apply]
  have offset : ContinuousParameterMap.initialMap 0 4 p - centre =
      bandU 4 (Geometry.Source.epsilon 0) p • basisVector 0 + p 1 • basisVector 1 := by
    change centre + _ + _ - centre = _
    abel
  rw [offset, dotProduct_add, dotProduct_smul, dotProduct_smul,
    seedNormal_dot_basis, seedNormal_dot_basis, smul_zero, smul_zero, add_zero]

theorem fullFlow_plane_start (p : BandPoint) : planeCoordinate (fullFlow p 0) = 0 := by
  rw [fullFlow_starts, seed_plane_zero]

theorem planeCoordinate_hasFDerivAt (x : Point) : HasFDerivAt planeCoordinate normalRead x := by
  have shifted := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const centre
  have composed := normalRead.hasFDerivAt.comp x shifted
  rw [ContinuousLinearMap.comp_id] at composed
  exact composed

theorem fullFlow_plane_derivative (p : BandPoint) (t : ℝ)
    (time : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    HasDerivWithinAt (fun s => planeCoordinate (fullFlow p s))
      (seedNormal ⬝ᵥ sourceGradient (fullFlow p t)) (Icc (-(1 / 2) : ℝ) (1 / 2)) t := by
  have derivative := (planeCoordinate_hasFDerivAt (fullFlow p t)).comp_hasDerivWithinAt t
    (fullFlow_original p t time)
  rwa [normalRead_apply] at derivative

theorem fullFlow_plane_strictMono (p : BandPoint) :
    StrictMonoOn (fun t => planeCoordinate (fullFlow p t)) (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
  · exact normalRead.continuous.comp_continuousOn
      ((fullFlow_original p).continuousOn.sub continuousOn_const)
  · intro t ht
    exact (fullFlow_plane_derivative p t (interior_subset ht)).mono interior_subset
  · intro t ht
    exact fullFlow_transverse p t (interior_subset ht)

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
