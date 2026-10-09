import H0mework.Versions.AB.Chemistry.LAlanineParametric.MatrixBounds
import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalStage
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSignedEvaluator.Field
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeTrace

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap ContinuousChart ContinuousGradient Set
open scoped BigOperators NNReal
noncomputable section

def lowerPoint (box : Rectangle) : Point := fun i => (box i).1
def upperPoint (box : Rectangle) : Point := fun i => (box i).2

theorem inRectangle_iff (box : Rectangle) (x : Point) :
    InRectangle box x ↔ x ∈ Icc (lowerPoint box) (upperPoint box) :=
  ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩,
    fun h i => ⟨h.1 i, h.2 i⟩⟩

def fieldNormBound (field : FieldBox) : ℚ := ∑ i : Fin 3, ∑ j : Fin 3, magnitude (field.hessian i j)

theorem fieldNormBound_nonneg (field : FieldBox) : 0 ≤ fieldNormBound field := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact (abs_nonneg _).trans (le_max_left _ _)

def fieldLipschitz (field : FieldBox) : ℝ≥0 :=
  ⟨(fieldNormBound field : ℝ), Rat.cast_nonneg.mpr (fieldNormBound_nonneg field)⟩

theorem hessian_single (x : Point) (i j : Fin 3) :
    sourceHessianLinear x (Pi.single j 1) i = sourceHessian x i j := by
  rw [sourceHessianLinear_apply]
  classical
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, mul_one]
  · intro k _ hkj
    simp only [Pi.single_eq_of_ne hkj, mul_zero]
  · simp

theorem field_hessian_norm (field : FieldBox) (x : Point) (bounded : FieldHolds field x) :
    ‖sourceHessianLinear x‖ ≤ (fieldLipschitz field : ℝ) := by
  apply matrix_norm_le field.hessian _ (fieldNormBound field) (fieldNormBound_nonneg field)
  · intro i j
    rw [hessian_single]
    exact bounded.2 i j
  · intro i
    apply Finset.single_le_sum _ (Finset.mem_univ i)
    intro k _
    apply Finset.sum_nonneg
    intro j _
    exact (abs_nonneg _).trans (le_max_left _ _)

theorem field_lipschitz (box : Rectangle) (field : FieldBox)
    (bounded : ∀ x, InRectangle box x → FieldHolds field x) :
    LipschitzOnWith (fieldLipschitz field) sourceGradient (Icc (lowerPoint box) (upperPoint box)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (sourceGradient_hasFDerivAt x).differentiableAt) _ (convex_Icc _ _)
  intro x hx
  rw [(sourceGradient_hasFDerivAt x).fderiv]
  exact_mod_cast field_hessian_norm field x (bounded x ((inRectangle_iff box x).mpr hx))

def accelerationPair (field : FieldBox) : VectorPair := fun i => dotThree (field.hessian i) field.gradient

theorem acceleration_contains (field : FieldBox) (x : Point) (bounded : FieldHolds field x) :
    VectorHolds (accelerationPair field) (sourceHessianLinear x (sourceGradient x)) := by
  intro i
  rw [sourceHessianLinear_apply]
  exact dotThree_contains _ _ _ _ (bounded.2 i) bounded.1

end
end LAlanine40K2025.BasinRefinement.TrueTubeTrace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
