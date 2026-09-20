import Mathlib.LinearAlgebra.TensorProduct.Map
import H0mework.Realization.FibreLinear.P558

/-!
# Proposition 559: sigma-zero fibers preserve algebraic tensor products

P555 identified every sigma-zero module fiber with its standard carrier by a
`LinearEquiv`, and P558 upgraded this to a full Hom equivalence.  This file
pushes the same annealing statement through the algebraic tensor product:

* the tensor product of two sigma-zero fibers is linearly equivalent to the
  standard tensor product;
* on pure tensors, the equivalence is exactly componentwise forgetful
  projection;
* the inverse sends a standard pure tensor to the tensor of the two canonical
  zero-fiber embeddings.

This is the tensor-composition face of the same thesis: at `σ = 0`, relaxed
mathematics does not sit beside standard mathematics; its composite carriers
anneal back to the standard composite carrier.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w v₂ w₂

/-! ## Tensor product compatibility at the zero fiber -/

/-- THEOREM 1: the algebraic tensor product of two sigma-zero fibers is
linearly equivalent to the standard algebraic tensor product. -/
def sigmaZeroTensorProductLinearEquiv
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] : by
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      exact
        TensorProduct 𝕜
            (SigmaRelaxedObject K X HX (0 : K))
            (SigmaRelaxedObject K Y HY (0 : K)) ≃ₗ[𝕜]
          TensorProduct 𝕜 X Y := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  exact TensorProduct.congr
    (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX)
    (sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY)

/-- THEOREM 2: the tensor equivalence is componentwise forgetful projection on
pure tensors. -/
@[simp] theorem sigmaZeroTensorProductLinearEquiv_tmul
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (x : SigmaRelaxedObject K X HX (0 : K))
    (y : SigmaRelaxedObject K Y HY (0 : K)) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    sigmaZeroTensorProductLinearEquiv K 𝕜 X HX Y HY
        (TensorProduct.tmul 𝕜 x y) =
      TensorProduct.tmul 𝕜
        (sigmaZeroForget (K := K) (X := X) (H := HX) x)
        (sigmaZeroForget (K := K) (X := Y) (H := HY) y) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  rfl

/-- THEOREM 3: the inverse tensor equivalence embeds pure tensors
componentwise into the zero fibers. -/
@[simp] theorem sigmaZeroTensorProductLinearEquiv_symm_tmul
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (x : X) (y : Y) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    (sigmaZeroTensorProductLinearEquiv K 𝕜 X HX Y HY).symm
        (TensorProduct.tmul 𝕜 x y) =
      TensorProduct.tmul 𝕜
        ((sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm x)
        ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).symm y) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  rfl

/-- A compact certificate bundling the zero-fiber tensor equivalence and its
pure-tensor boundary behavior. -/
structure SigmaZeroTensorProductCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] where
  tensor_linear_equiv : by
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    exact
      TensorProduct 𝕜
          (SigmaRelaxedObject K X HX (0 : K))
          (SigmaRelaxedObject K Y HY (0 : K)) ≃ₗ[𝕜]
        TensorProduct 𝕜 X Y
  forgets_pure_tensors :
    ∀ (x : SigmaRelaxedObject K X HX (0 : K))
      (y : SigmaRelaxedObject K Y HY (0 : K)),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      tensor_linear_equiv (TensorProduct.tmul 𝕜 x y) =
        TensorProduct.tmul 𝕜
          (sigmaZeroForget (K := K) (X := X) (H := HX) x)
          (sigmaZeroForget (K := K) (X := Y) (H := HY) y)
  embeds_pure_tensors :
    ∀ (x : X) (y : Y),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      tensor_linear_equiv.symm (TensorProduct.tmul 𝕜 x y) =
        TensorProduct.tmul 𝕜
          ((sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm x)
          ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).symm y)

/-- THEOREM 4: the canonical zero-fiber tensor certificate. -/
def sigmaZeroTensorProductCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] :
    SigmaZeroTensorProductCertificate K 𝕜 X HX Y HY where
  tensor_linear_equiv := sigmaZeroTensorProductLinearEquiv K 𝕜 X HX Y HY
  forgets_pure_tensors := by
    intro x y
    exact sigmaZeroTensorProductLinearEquiv_tmul K 𝕜 X HX Y HY x y
  embeds_pure_tensors := by
    intro x y
    exact sigmaZeroTensorProductLinearEquiv_symm_tmul K 𝕜 X HX Y HY x y


end AffineRelaxation
end SaturationMonoid
