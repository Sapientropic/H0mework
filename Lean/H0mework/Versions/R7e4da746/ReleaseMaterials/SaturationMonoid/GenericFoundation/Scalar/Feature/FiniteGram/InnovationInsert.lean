import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.Projection
open scoped InnerProductSpace

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (source : ι → H)

theorem innovation_ne_zero_of_new_column {column : H} (novel : column ∉ sourceSpan source) :
    innovationCLM source column ≠ 0 := by
  intro zero
  rw [innovation_value, sub_eq_zero] at zero
  apply novel
  rw [zero]
  exact predictable_mem source column

def insertedCoefficient (column recorded : H) : ℂ :=
  let residual := innovationCLM source column
  inner ℂ residual recorded / inner ℂ residual residual

/-- The newly written column is read by its orthogonal residual, then the old solver consumes the same remainder. -/
theorem insertion_read (column : H) (novel : column ∉ sourceSpan source)
    (faithful : Function.Injective (synthesis source)) (a : Coordinates ι) (b : ℂ) :
    let value := synthesis source a + b • column
    let fresh := insertedCoefficient source column value
    fresh = b ∧ coefficients source (value-fresh • column) = a := by
  let residual := innovationCLM source column
  have orthogonal : residual ∈ (sourceSpan source)ᗮ := innovation_orthogonal source column
  have square : inner ℂ residual residual ≠ 0 := fun gone =>
    innovation_ne_zero_of_new_column source novel (inner_self_eq_zero.mp gone)
  have vanishes (x : H) (inSpan : x ∈ sourceSpan source) : inner ℂ residual x = 0 :=
    inner_eq_zero_symm.mp (orthogonal x inSpan)
  have returned : inner ℂ residual column = inner ℂ residual residual := by
    have split : column = predictable source column + residual := by
      dsimp only [residual]
      rw [innovation_value]
      abel
    calc
      _ = inner ℂ residual (predictable source column + residual) := congrArg (inner ℂ residual) split
      _ = _ := by rw [inner_add_right, vanishes _ (predictable_mem source column), zero_add]
  have first : insertedCoefficient source column (synthesis source a + b • column) = b := by
    change inner ℂ residual (synthesis source a + b • column) / inner ℂ residual residual = b
    rw [inner_add_right, vanishes _ ⟨a,rfl⟩, zero_add, inner_smul_right, returned]
    exact mul_div_cancel_right₀ _ square
  dsimp only
  rw [first, add_sub_cancel_right]
  refine ⟨rfl, faithful ?_⟩
  have paid := predictable_readback source (synthesis source a)
  rw [predictable_source, Submodule.starProjection_eq_self_iff.mpr
    (show synthesis source a ∈ sourceSpan source from ⟨a,rfl⟩)] at paid
  exact paid

end SourceGeneratedFiniteGram.Projection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
