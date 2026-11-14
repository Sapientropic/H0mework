import Mathlib.Analysis.InnerProductSpace.Adjoint
import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.PrefixImage.ActionImage

open scoped InnerProductSpace
open Set

variable {H F : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Pull each actual next-field test through the source action before running the finite inverse. -/
def pull (action : H →L[ℂ] F) (source : Nat → F) (i : Nat) : H :=
  action.adjoint (source i)

theorem action_read (action : H →L[ℂ] F) (source : Nat → F) (value : H) :
    read (pull action source) value = read source (action value) := by
  funext i
  exact action.adjoint_inner_left value (source i)

theorem admitted_iff_action_image (action : H →L[ℂ] F) (source : Nat → F) (data : Nat → ℂ) :
    ((∀ n, residual (pull action source) data n = 0) ∧
      BddAbove (range (energy (pull action source) data))) ↔
      ∃ value : H, read source (action value) = data := by
  refine (admitted_iff_image (pull action source) data).trans ?_
  constructor
  · rintro ⟨value,exactRead⟩
    exact ⟨value,(action_read action source value).symm.trans exactRead⟩
  · rintro ⟨value,exactRead⟩
    exact ⟨value,(action_read action source value).trans exactRead⟩

/-- The values passed to the inverse are the original next prices. -/
def captureNext (action : H →L[ℂ] F) (source : Nat → F) (value : H) :
    Admitted (pull action source) :=
  ⟨read source (action value),by
    rw [← action_read action source value]
    exact (capture (pull action source) value).property⟩

def inverse (action : H →L[ℂ] F) (source : Nat → F)
    (data : Admitted (pull action source)) : H :=
  realize (pull action source) data

theorem forward_equation (action : H →L[ℂ] F) (source : Nat → F)
    (data : Admitted (pull action source)) :
    read source (action (inverse action source data)) = data.val :=
  (action_read action source (inverse action source data)).symm.trans
    (read_realized (pull action source) data)

/-- The inverse gives the whole affine fibre, including the actual kernel of a noninjective action. -/
theorem complete_fibre (action : H →L[ℂ] F) (source : Nat → F)
    (readInjective : Function.Injective (read source))
    (data : Admitted (pull action source)) (value : H) :
    read source (action value) = data.val ↔
      value - inverse action source data ∈ LinearMap.ker action.toLinearMap := by
  have exactRead := forward_equation action source data
  rw [LinearMap.mem_ker]
  change read source (action value) = data.val ↔ action (value - inverse action source data) = 0
  rw [map_sub,sub_eq_zero]
  exact ⟨fun paid => readInjective (paid.trans exactRead.symm),
    fun paid => (congrArg (read source) paid).trans exactRead⟩

theorem inverse_capture (action : H →L[ℂ] F) (source : Nat → F)
    (actionInjective : Function.Injective action) (readInjective : Function.Injective (read source))
    (value : H) :
    inverse action source (captureNext action source value) = value :=
  actionInjective (readInjective (forward_equation action source (captureNext action source value)))

end SourceGeneratedFiniteGram.PrefixImage.ActionImage
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
