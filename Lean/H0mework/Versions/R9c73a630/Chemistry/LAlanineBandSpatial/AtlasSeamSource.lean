import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSpatial.AtlasCarrier
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.GeometryTangents
import Mathlib.Analysis.Calculus.TangentCone.Pi

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeCellBoundary WholeCellBoundary.Geometry Set
noncomputable section

abbrev Seam := Fin 31
def leftCell (s : Seam) : FullBandCell := ⟨s.val,by omega⟩
def rightCell (s : Seam) : FullBandCell := ⟨s.val+1,by omega⟩
def domain : Set FacePoint := Icc ![0,-(1/2)] ![1,1/2]
def coordinate (s : Seam) : ℝ := cellV (leftCell s) 1
def parameter (s : Seam) (u : FacePoint) : Point := (1 : Fin 3).insertNth (coordinate s) u

theorem original_coordinate (s : Seam) : coordinate s = (cellV (rightCell s) 0 : ℝ) :=
  congrArg (fun r : ℚ => (r : ℝ)) (consecutive_source_intervals s)

theorem domain_nonempty : domain.Nonempty := by
  refine ⟨![0,0],?_,?_⟩ <;> intro i <;> fin_cases i <;> norm_num

theorem domain_uniqueDiff : UniqueDiffOn ℝ domain := by
  have ordered : ∀ i : Fin 2, (![0,-(1/2)] : FacePoint) i < (![1,1/2] : FacePoint) i := by
    intro i
    fin_cases i <;> norm_num
  simpa only [pi_univ_Icc,domain] using UniqueDiffOn.univ_pi (fun i => uniqueDiffOn_Icc (ordered i))

theorem parameter_left (s : Seam) (u : FacePoint) (inside : u ∈ domain) :
    parameter s u ∈ cellDomain (leftCell s) := by
  change u 0 ∈ Icc (0 : ℝ) 1 ∧ coordinate s ∈ Icc (cellV (leftCell s) 0 : ℝ) (cellV (leftCell s) 1) ∧
    u 1 ∈ Icc (-(1/2 : ℝ)) (1/2)
  exact ⟨⟨inside.1 0,inside.2 0⟩,
    ⟨Rat.cast_le.mpr (source_cells_in_segments (leftCell s)).2.1.le,le_rfl⟩,⟨inside.1 1,inside.2 1⟩⟩

theorem parameter_right (s : Seam) (u : FacePoint) (inside : u ∈ domain) :
    parameter s u ∈ cellDomain (rightCell s) := by
  change u 0 ∈ Icc (0 : ℝ) 1 ∧ coordinate s ∈ Icc (cellV (rightCell s) 0 : ℝ) (cellV (rightCell s) 1) ∧
    u 1 ∈ Icc (-(1/2 : ℝ)) (1/2)
  rw [original_coordinate]
  exact ⟨⟨inside.1 0,inside.2 0⟩,
    ⟨le_rfl,Rat.cast_le.mpr (source_cells_in_segments (rightCell s)).2.1.le⟩,⟨inside.1 1,inside.2 1⟩⟩

theorem parameter_hasFDerivAt (s : Seam) (u : FacePoint) :
    HasFDerivAt (parameter s) (faceInclusion 1) u := by
  have identity : parameter s = fun v => Pi.single (1 : Fin 3) (coordinate s) + faceInclusion 1 v :=
    funext (fun v => insertNth_eq_affine 1 (coordinate s) v)
  rw [identity]
  convert! (hasFDerivAt_const (Pi.single (1 : Fin 3) (coordinate s)) u).add (faceInclusion 1).hasFDerivAt using 1
  simp only [zero_add]

theorem original_maps_agree (s : Seam) (u : FacePoint) (inside : u ∈ domain) :
    sourceParameterMap (leftCell s) (parameter s u) = sourceParameterMap (rightCell s) (parameter s u) := by
  unfold sourceParameterMap
  rw [seam_seed_agrees (leftCell s) (rightCell s) _ (parameter_left s u inside) (parameter_right s u inside)]

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
