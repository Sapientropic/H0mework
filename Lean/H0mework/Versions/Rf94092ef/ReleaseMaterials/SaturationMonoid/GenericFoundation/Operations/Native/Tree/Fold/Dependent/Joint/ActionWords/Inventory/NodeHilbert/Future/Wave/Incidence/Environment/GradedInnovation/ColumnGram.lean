import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.ColumnAction

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation

open scoped InnerProductSpace

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (grade : Nat) (frame : Frame (K := K) grade)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current := current))

/-- Both sides of the same actual source write generate the four ordered Gram terms. -/
def columnActionGram : Matrix (Index grade frame) (Index grade frame) ℂ :=
  fun i j =>
    let left := columnAction read grade frame supplied i
    let right := columnAction read grade frame supplied j
    inner ℂ left.1 right.1+inner ℂ left.1 right.2+inner ℂ left.2 right.1+inner ℂ left.2 right.2

theorem actual_gram_from_column_actions :
    FG.gram (columns read grade frame supplied) = columnActionGram read grade frame supplied := by
  ext i j : 1
  change inner ℂ (columns read grade frame supplied i) (columns read grade frame supplied j) = _
  rw [actual_column_from_action read grade frame supplied i,actual_column_from_action read grade frame supplied j]
  simp only [columnActionGram, inner_add_left, inner_add_right, add_assoc]
  exact congrArg (_ + ·) (add_left_comm _ _ _)

/-- The same action supplies the full right-hand side of the existing Gram inverse. -/
def columnActionRhs (value : K) : SourceGeneratedFiniteGram.Coordinates (Index grade frame) :=
  WithLp.toLp 2 fun i =>
    let action := columnAction read grade frame supplied i
    inner ℂ action.1 value+inner ℂ action.2 value

theorem actual_gram_rhs_from_column_actions (value : K) :
    FG.rhs (columns read grade frame supplied) value = columnActionRhs read grade frame supplied value := by
  ext i
  change inner ℂ (columns read grade frame supplied i) value = _
  simp only [columnActionRhs, actual_column_from_action, inner_add_left]

private theorem column_action_hermitian : (columnActionGram read grade frame supplied).IsHermitian := by
  rw [← actual_gram_from_column_actions]
  exact Matrix.isHermitian_gram ℂ _

private theorem column_action_compatible (value : K) :
    SourceGeneratedFiniteGram.Compatible (columnActionGram read grade frame supplied)
      (columnActionRhs read grade frame supplied value) := by
  rw [← actual_gram_from_column_actions, ← actual_gram_rhs_from_column_actions]
  exact FG.compatible _ _

/-- Solve the generated action system in its actual image, retaining the kernel fibre. -/
def columnActionCoefficients (value : K) : SourceGeneratedFiniteGram.Coordinates (Index grade frame) :=
  SourceGeneratedFiniteGram.coefficients (columnActionGram read grade frame supplied)
    (column_action_hermitian read grade frame supplied) (columnActionRhs read grade frame supplied value)
    (column_action_compatible read grade frame supplied value)

theorem column_action_equation (value : K) :
    SourceGeneratedFiniteGram.action (columnActionGram read grade frame supplied)
      (columnActionCoefficients read grade frame supplied value) =
        columnActionRhs read grade frame supplied value :=
  SourceGeneratedFiniteGram.equation _ _ _ _

theorem actual_column_action_fibre (value : K) (a : SourceGeneratedFiniteGram.Coordinates (Index grade frame)) :
    SourceGeneratedFiniteGram.action (columnActionGram read grade frame supplied) a =
      columnActionRhs read grade frame supplied value ↔
      a-columnActionCoefficients read grade frame supplied value ∈
        SourceGeneratedFiniteGram.Kernel (columnActionGram read grade frame supplied) :=
  SourceGeneratedFiniteGram.full_fibre _ _ _ _ a

/-- Synthesis and residual write-back use the original whole column family. -/
def columnActionInnovation (value : K) : K :=
  value - SourceGeneratedFiniteGram.Projection.synthesis (columns read grade frame supplied)
    (columnActionCoefficients read grade frame supplied value)

theorem actual_innovation_from_column_actions (value : K) :
    FG.innovationCLM (columns read grade frame supplied) value =
      columnActionInnovation read grade frame supplied value := by
  have coefficients : columnActionCoefficients read grade frame supplied value =
      FG.coefficients (columns read grade frame supplied) value := by
    simp only [columnActionCoefficients, SourceGeneratedFiniteGram.Projection.coefficients, ← actual_gram_from_column_actions read grade frame supplied,
      ← actual_gram_rhs_from_column_actions read grade frame supplied]
  rw [SourceGeneratedFiniteGram.Projection.innovation_value,
    SourceGeneratedFiniteGram.Projection.predictable_source, columnActionInnovation, coefficients]

end PaidSourceContentEnvironment.GradedInnovation
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
