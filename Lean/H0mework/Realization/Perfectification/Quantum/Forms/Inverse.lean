import H0mework.Realization.Perfectification.Quantum.Transfer.Polar
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! A bounded injective self-adjoint resolvent generates its inverse minus
the identity on its actual range. The adjoint-domain equation proves exact
self-adjointness, without supplying an inverse or an operator domain. -/

set_option autoImplicit false

open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.Quantum.Forms.Inverse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (R : H →L[ℂ] H) (injective : Function.Injective R)

def preimage : R.range →ₗ[ℂ] H := (LinearEquiv.ofInjective R.toLinearMap injective).symm.toLinearMap

theorem preimage_apply (x : R.range) : R (preimage R injective x) = x.val :=
  LinearEquiv.ofInjective_symm_apply R.toLinearMap (h := injective) x

def operator : H →ₗ.[ℂ] H where
  domain := R.range
  toFun := preimage R injective - R.range.subtype

def point (x : H) : (operator R injective).domain := ⟨R x, ⟨x, rfl⟩⟩

theorem point_preimage (x : (operator R injective).domain) : point R injective (preimage R injective x) = x :=
  Subtype.ext (preimage_apply R injective x)

theorem operator_point (x : H) : operator R injective (point R injective x) = x - R x := by
  change (LinearEquiv.ofInjective R.toLinearMap injective).symm
    (LinearEquiv.ofInjective R.toLinearMap injective x) - R x = x - R x
  rw [LinearEquiv.symm_apply_apply]

variable [CompleteSpace H] (symmetric : IsSelfAdjoint R)

include symmetric

theorem domain_dense : Dense ((operator R injective).domain : Set H) :=
  Transfer.Polar.selfAdjoint_denseRange R symmetric injective

theorem operator_formalAdjoint : (operator R injective).IsFormalAdjoint (operator R injective) := by
  intro x y
  rw [← point_preimage R injective x, ← point_preimage R injective y, operator_point, operator_point]
  change inner ℂ (preimage R injective x - R (preimage R injective x)) (R (preimage R injective y)) =
    inner ℂ (R (preimage R injective x)) (preimage R injective y - R (preimage R injective y))
  rw [inner_sub_left, inner_sub_right]
  exact congrArg (fun z : ℂ => z - inner ℂ (R (preimage R injective x)) (R (preimage R injective y)))
    (symmetric.isSymmetric (preimage R injective x) (preimage R injective y)).symm

theorem adjoint_identity (z : ((operator R injective)†).domain) :
    z.val = R (z.val + (operator R injective)† z) := by
  apply ext_inner_left ℂ
  intro a
  have pairing := (LinearPMap.adjoint_isFormalAdjoint (T := operator R injective)
    (domain_dense R injective symmetric)).symm (point R injective a) z
  rw [operator_point] at pairing
  change inner ℂ (a - R a) z.val = inner ℂ (R a) ((operator R injective)† z) at pairing
  rw [inner_sub_left] at pairing
  have symmetry : inner ℂ (R a) (z.val + (operator R injective)† z) =
      inner ℂ a (R (z.val + (operator R injective)† z)) := symmetric.isSymmetric _ _
  rw [← symmetry, inner_add_right]
  exact (sub_eq_iff_eq_add.mp pairing).trans (add_comm _ _)

theorem adjoint_mem_domain (z : ((operator R injective)†).domain) : z.val ∈ (operator R injective).domain := by
  rw [adjoint_identity R injective symmetric z]
  exact ⟨_, rfl⟩

theorem adjoint_value (z : ((operator R injective)†).domain) :
    operator R injective ⟨z.val, adjoint_mem_domain R injective symmetric z⟩ = (operator R injective)† z := by
  have same : (⟨z.val, adjoint_mem_domain R injective symmetric z⟩ : (operator R injective).domain) =
      point R injective (z.val + (operator R injective)† z) :=
    Subtype.ext (adjoint_identity R injective symmetric z)
  rw [same, operator_point, ← adjoint_identity R injective symmetric z]
  abel

theorem operator_selfAdjoint : IsSelfAdjoint (operator R injective) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨fun z hz => adjoint_mem_domain R injective symmetric ⟨z, hz⟩, ?_⟩
    intro z x same
    rw [← adjoint_value R injective symmetric z]
    exact congrArg (operator R injective) (Subtype.ext same)
  · exact (operator_formalAdjoint R injective symmetric).le_adjoint (domain_dense R injective symmetric)

theorem operator_closed : (operator R injective).IsClosed := (operator_selfAdjoint R injective symmetric).isClosed

end
end SaturationMonoid.Quantum.Forms.Inverse
