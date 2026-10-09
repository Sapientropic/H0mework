import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.LAlanineMolecularControl.Scratch.LAlanineSpatialControl.SpatialProjectionDynamics
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open ContinuousLinearMap
open scoped BigOperators InnerProductSpace Matrix

variable {n E : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def fieldFrame (fields : n → E) : EuclideanSpace ℂ n →L[ℂ] E :=
  ∑ i : n, (PiLp.proj 2 (fun _ : n => ℂ) i).smulRight (fields i)

omit [DecidableEq n] [CompleteSpace E] in
theorem field_frame_apply (fields : n → E) (x : EuclideanSpace ℂ n) :
    fieldFrame fields x = ∑ i : n, x i • fields i := by
  simp only [fieldFrame,sum_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]

omit [CompleteSpace E] in
theorem field_frame_single (fields : n → E) (i : n) :
    fieldFrame fields (EuclideanSpace.single i 1) = fields i := by
  rw [field_frame_apply]
  simp [EuclideanSpace.single,PiLp.single_apply]

theorem field_frame_cross_gram (first second : n → E) :
    (fieldFrame first).adjoint ∘L fieldFrame second =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
        (Matrix.of (fun i j => inner ℂ (first i) (second j))) := by
  ext x i
  have coordinate : ((fieldFrame first).adjoint (fieldFrame second x)) i =
      inner ℂ (first i) (fieldFrame second x) := by
    calc
      _ = inner ℂ (EuclideanSpace.single i 1) ((fieldFrame first).adjoint (fieldFrame second x)) := by
        simp only [EuclideanSpace.inner_single_left,map_one,one_mul]
      _ = inner ℂ (fieldFrame first (EuclideanSpace.single i 1)) (fieldFrame second x) :=
        (fieldFrame first).adjoint_inner_right _ _
      _ = _ := by rw [field_frame_single]
  change ((fieldFrame first).adjoint (fieldFrame second x)) i = _
  rw [coordinate,field_frame_apply,inner_sum]
  simp only [inner_smul_right]
  change (∑ j : n, x j * inner ℂ (first i) (second j)) =
    ∑ j : n, inner ℂ (first i) (second j) * x j
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem field_frame_gram (fields : n → E) :
    LAlanineSpatialProjection.gram (fieldFrame fields) =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (Matrix.gram ℂ fields) :=
  field_frame_cross_gram fields fields

omit [DecidableEq n] [CompleteSpace E] in
theorem field_frame_equation (fields : ℝ → n → E) (rates : n → E) (time : ℝ)
    (source : ∀ i, HasDerivAt (fun t => fields t i) (rates i) time) :
    HasDerivAt (fun t => fieldFrame (fields t)) (fieldFrame rates) time := by
  apply HasDerivAt.fun_sum
  intro i _
  let embedding : E →L[ℂ] (EuclideanSpace ℂ n →L[ℂ] E) :=
    ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ n) E (PiLp.proj 2 (fun _ : n => ℂ) i)
  have generated := (embedding.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time (source i)
  simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars,embedding,
    ContinuousLinearMap.smulRightL_apply_apply] using! generated

theorem orthonormal_frame_unit (fields : n → E) (normalized : Orthonormal ℂ fields) :
    IsUnit (LAlanineSpatialProjection.gram (fieldFrame fields)) := by
  rw [field_frame_gram,Matrix.gram_eq_one_iff_orthonormal.mpr normalized,map_one]
  exact isUnit_one

end
end CPS1MolecularFrame
