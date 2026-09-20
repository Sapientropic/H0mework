import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Neutral constitutive operators

This module contains only carrier-level linear algebra.  It has no action,
Euler--Lagrange residual, hard-gate target, or source-generation relation, so
it is safe for both upstream source modules and downstream Yang--Mills
recovery modules to import.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uScalar uTwoForm

section HodgeConstitutive

variable {Scalar : Type uScalar} {TwoForm : Type uTwoForm}
variable [Field Scalar] [AddCommGroup TwoForm] [Module Scalar TwoForm]

/-- The neutral constitutive operator `K = g² *`. -/
def hodgeConstitutiveOperator
    (hodge : TwoForm ≃ₗ[Scalar] TwoForm) (couplingSquared : Scalarˣ) :
    TwoForm ≃ₗ[Scalar] TwoForm :=
  hodge.trans (LinearEquiv.smulOfUnit couplingSquared)

@[simp]
theorem hodgeConstitutiveOperator_apply
    (hodge : TwoForm ≃ₗ[Scalar] TwoForm) (couplingSquared : Scalarˣ)
    (B : TwoForm) :
    hodgeConstitutiveOperator hodge couplingSquared B =
      (couplingSquared : Scalar) • hodge B := by
  rfl

@[simp]
theorem hodgeConstitutiveOperator_symm_apply
    (hodge : TwoForm ≃ₗ[Scalar] TwoForm) (couplingSquared : Scalarˣ)
    (F : TwoForm) :
    (hodgeConstitutiveOperator hodge couplingSquared).symm F =
      hodge.symm ((↑couplingSquared⁻¹ : Scalar) • F) := by
  rfl

end HodgeConstitutive

/-- A typed Standard-Model gauge block constructed from one spacetime Hodge
operator and three nonzero coupling normalizations. -/
structure StandardModelGaugeConstitutiveBlock
    (Scalar : Type uScalar) (TwoForm : Type uTwoForm)
    [Field Scalar] [AddCommGroup TwoForm] [Module Scalar TwoForm] where
  spacetimeHodge : TwoForm ≃ₗ[Scalar] TwoForm
  strongCouplingSquared : Scalarˣ
  weakCouplingSquared : Scalarˣ
  hyperchargeCouplingSquared : Scalarˣ

namespace StandardModelGaugeConstitutiveBlock

variable {Scalar : Type uScalar} {TwoForm : Type uTwoForm}
variable [Field Scalar] [AddCommGroup TwoForm] [Module Scalar TwoForm]

def strongOperator
    (block : StandardModelGaugeConstitutiveBlock Scalar TwoForm) :
    TwoForm ≃ₗ[Scalar] TwoForm :=
  hodgeConstitutiveOperator block.spacetimeHodge
    block.strongCouplingSquared

def weakOperator
    (block : StandardModelGaugeConstitutiveBlock Scalar TwoForm) :
    TwoForm ≃ₗ[Scalar] TwoForm :=
  hodgeConstitutiveOperator block.spacetimeHodge
    block.weakCouplingSquared

def hyperchargeOperator
    (block : StandardModelGaugeConstitutiveBlock Scalar TwoForm) :
    TwoForm ≃ₗ[Scalar] TwoForm :=
  hodgeConstitutiveOperator block.spacetimeHodge
    block.hyperchargeCouplingSquared

end StandardModelGaugeConstitutiveBlock

end PhysicsCore
end SaturationMonoid
