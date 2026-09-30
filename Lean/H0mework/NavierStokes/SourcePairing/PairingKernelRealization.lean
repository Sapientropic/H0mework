import H0mework.NavierStokes.SourceAction.PositiveKernelCarrier
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace SaturationMonoid.NavierStokes.NativePositiveKernelRealization
open NativePositiveKernelCarrier
noncomputable section
universe u v
variable {Index : Type u} {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def preMap (kernel : Kernel Index) (vectors : Index → H) : PreSpace kernel →ₗ[ℂ] H :=
  (Finsupp.linearCombination ℂ vectors).comp (ofPreSpace kernel).toLinearMap

omit [CompleteSpace H] in
theorem preMap_apply (kernel : Kernel Index) (vectors : Index → H) (value : PreSpace kernel) :
    preMap kernel vectors value = (ofPreSpace kernel value).sum (fun index scalar => scalar • vectors index) := rfl

omit [CompleteSpace H] in
theorem preMap_inner (kernel : Kernel Index) (vectors : Index → H)
    (gram : ∀ first last, inner ℂ (vectors first) (vectors last) = kernel.matrix first last)
    (first last : PreSpace kernel) :
    inner ℂ (preMap kernel vectors first) (preMap kernel vectors last) = inner ℂ first last := by
  rw [preMap_apply, preMap_apply]
  rw [Finsupp.sum_inner]
  simp only [Finsupp.sum, inner_sum, inner_smul_left, inner_smul_right, gram, starRingEnd_apply]
  change (∑ i ∈ (ofPreSpace kernel first).support, ∑ j ∈ (ofPreSpace kernel last).support,
    ofPreSpace kernel last j*(star (ofPreSpace kernel first i)*kernel.matrix i j)) = _
  change _ = pairing kernel first last
  unfold pairing Finsupp.sum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def preIsometry (kernel : Kernel Index) (vectors : Index → H)
    (gram : ∀ first last, inner ℂ (vectors first) (vectors last) = kernel.matrix first last) :
    PreSpace kernel →ₗᵢ[ℂ] H where
  toLinearMap := preMap kernel vectors
  norm_map' value := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), preMap_inner kernel vectors gram]

def extension (kernel : Kernel Index) (vectors : Index → H)
    (gram : ∀ first last, inner ℂ (vectors first) (vectors last) = kernel.matrix first last) :
    Space kernel →L[ℂ] H :=
  (preIsometry kernel vectors gram).toContinuousLinearMap.extend UniformSpace.Completion.toComplL

theorem extension_coe (kernel : Kernel Index) (vectors : Index → H)
    (gram : ∀ first last, inner ℂ (vectors first) (vectors last) = kernel.matrix first last)
    (value : PreSpace kernel) :
    extension kernel vectors gram (value : Space kernel) = preMap kernel vectors value := by
  exact (preIsometry kernel vectors gram).toContinuousLinearMap.extend_eq
    UniformSpace.Completion.denseRange_coe (UniformSpace.Completion.isUniformInducing_coe _) value

def realize (kernel : Kernel Index) (vectors : Index → H)
    (gram : ∀ first last, inner ℂ (vectors first) (vectors last) = kernel.matrix first last) :
    Space kernel →ₗᵢ[ℂ] H where
  toLinearMap := (extension kernel vectors gram).toLinearMap
  norm_map' value := by
    induction value using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq ((extension kernel vectors gram).continuous.norm) continuous_norm
    | ih value =>
      change ‖extension kernel vectors gram (value : Space kernel)‖ = ‖(value : Space kernel)‖
      rw [extension_coe, UniformSpace.Completion.norm_coe]
      exact (preIsometry kernel vectors gram).norm_map value

theorem realize_coe (kernel : Kernel Index) (vectors : Index → H)
    (gram : ∀ first last, inner ℂ (vectors first) (vectors last) = kernel.matrix first last)
    (value : PreSpace kernel) :
    realize kernel vectors gram (value : Space kernel) =
      (ofPreSpace kernel value).sum (fun index scalar => scalar • vectors index) :=
  extension_coe kernel vectors gram value

theorem realize_vector (kernel : Kernel Index) (vectors : Index → H)
    (gram : ∀ first last, inner ℂ (vectors first) (vectors last) = kernel.matrix first last)
    (index : Index) : realize kernel vectors gram (vector kernel index) = vectors index := by
  classical
  rw [vector, realize_coe, LinearEquiv.apply_symm_apply]
  simp

end
end SaturationMonoid.NavierStokes.NativePositiveKernelRealization
