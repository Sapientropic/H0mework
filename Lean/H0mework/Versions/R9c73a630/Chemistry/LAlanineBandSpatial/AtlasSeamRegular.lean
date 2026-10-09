import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSpatial.AtlasSeamArea
import Mathlib.LinearAlgebra.StdBasis

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
open SourceGaussianModel WholeBandContinuationParameter WholeCellBoundary WholeCellBoundary.Geometry Matrix
noncomputable section

theorem inclusion_injective : Function.Injective (faceInclusion 1) := by
  intro u v same
  have inserted : ((1 : Fin 3).insertNth (0 : ℝ) u : Point) = (1 : Fin 3).insertNth (0 : ℝ) v := by
    rw [insertNth_eq_affine,insertNth_eq_affine,same]
  exact (Fin.insertNth_inj.mp inserted).2

theorem actual_derivative_injective (fields : Fields) (bounds : Bounds) (positive : Normals)
    (s : Seam) (u : FacePoint) (inside : u ∈ domain) : Function.Injective (leftDerivative s u) :=
  (trueJacobian_injective (leftCell s) (fields _) (bounds _) (positive _) _ (parameter_left s u inside)).comp
    inclusion_injective

theorem actual_rank_two (fields : Fields) (bounds : Bounds) (positive : Normals)
    (s : Seam) (u : FacePoint) (inside : u ∈ domain) :
    Module.finrank ℝ (LinearMap.range (leftDerivative s u).toLinearMap) = 2 := by
  rw [LinearMap.finrank_range_of_inj (actual_derivative_injective fields bounds positive s u inside)]
  simp [FacePoint]

theorem actual_tangents_independent (fields : Fields) (bounds : Bounds) (positive : Normals)
    (s : Seam) (u : FacePoint) (inside : u ∈ domain) :
    LinearIndependent ℝ (fun k : Fin 2 => leftDerivative s u (Pi.single k 1)) := by
  have mapped := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map_injOn
    (leftDerivative s u).toLinearMap (actual_derivative_injective fields bounds positive s u inside).injOn
  simpa only [Function.comp_def,Pi.basisFun_apply,ContinuousLinearMap.coe_coe] using mapped

theorem leftArea_ne_zero (fields : Fields) (bounds : Bounds) (positive : Normals)
    (s : Seam) (u : FacePoint) (inside : u ∈ domain) : leftArea s u ≠ 0 := by
  rw [leftArea,neg_ne_zero]
  apply crossProduct_ne_zero_iff_linearIndependent.mpr
  have pair : ![leftDerivative s u (Pi.single 0 1),leftDerivative s u (Pi.single 1 1)] =
      fun k : Fin 2 => leftDerivative s u (Pi.single k 1) := by
    funext k
    fin_cases k <;> rfl
  rw [pair]
  exact actual_tangents_independent fields bounds positive s u inside

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
