import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Source-generated scalar square-zero connecting kernel

For an endomorphism `F` and a source-owned first derivative `a`, the
constant/infinitesimal chart of `1 - (1 + aε)F` canonically generates a
connecting map from the fixed kernel to the fixed cokernel.  The connecting
map is exactly the basis-free first-variation Bockstein.  No finite,
perfect, determinant, domain endpoint, or global-prism premise is used.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarSquareZeroFirstOrder

noncomputable section

universe r m

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]

def fixedDifference (action : M →ₗ[R] M) : M →ₗ[R] M :=
  LinearMap.id - action

abbrev FixedKernel (action : M →ₗ[R] M) :=
  LinearMap.ker (fixedDifference action)

abbrev FixedCokernel (action : M →ₗ[R] M) :=
  M ⧸ LinearMap.range (fixedDifference action)

/-- Coefficient-one action on the fixed kernel, read in the fixed cokernel. -/
def firstVariationBockstein
    (action : M →ₗ[R] M) (derivative : R) :
    FixedKernel action →ₗ[R] FixedCokernel action :=
  (Submodule.mkQ (LinearMap.range (fixedDifference action))).comp
    ((derivative • action).comp
      (LinearMap.ker (fixedDifference action)).subtype)

theorem action_eq_on_fixedKernel
    (action : M →ₗ[R] M) (value : FixedKernel action) :
    action value.1 = value.1 := by
  have fixed := LinearMap.mem_ker.mp value.2
  change value.1 - action value.1 = 0 at fixed
  exact (sub_eq_zero.mp fixed).symm

@[simp] theorem firstVariationBockstein_apply
    (action : M →ₗ[R] M) (derivative : R)
    (value : FixedKernel action) :
    firstVariationBockstein action derivative value =
      Submodule.Quotient.mk
        (p := LinearMap.range (fixedDifference action))
        (derivative • value.1) := by
  unfold firstVariationBockstein
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.smul_apply]
  change Submodule.mkQ (LinearMap.range (fixedDifference action))
      (derivative • action value.1) = _
  rw [action_eq_on_fixedKernel]
  exact Submodule.mkQ_apply _ _

/-- Constant/infinitesimal matrix of `1 - (1 + aε)F`. -/
def pairOperator
    (action : M →ₗ[R] M) (derivative : R) :
    (M × M) →ₗ[R] (M × M) :=
  (((fixedDifference action).comp (LinearMap.fst R M M)).prod
    (((fixedDifference action).comp (LinearMap.snd R M M)) -
      ((derivative • action).comp (LinearMap.fst R M M))))

@[simp] theorem pairOperator_apply
    (action : M →ₗ[R] M) (derivative : R) (value : M × M) :
    pairOperator action derivative value =
      (value.1 - action value.1,
        value.2 - action value.2 - derivative • action value.1) := by
  rfl

def constantLift (action : M →ₗ[R] M) :
    FixedKernel action →ₗ[R] M × M :=
  (LinearMap.inl R M M).comp
    (LinearMap.ker (fixedDifference action)).subtype

def infinitesimalQuotientReadout (action : M →ₗ[R] M) :
    (M × M) →ₗ[R] FixedCokernel action :=
  (Submodule.mkQ (LinearMap.range (fixedDifference action))).comp
    (LinearMap.snd R M M)

/-- Apply the actual pair matrix to the constant lift, then read the
infinitesimal coordinate in the special-fibre cokernel. -/
def pairConnecting
    (action : M →ₗ[R] M) (derivative : R) :
    FixedKernel action →ₗ[R] FixedCokernel action :=
  (infinitesimalQuotientReadout action).comp
    ((pairOperator action derivative).comp (constantLift action))

@[simp] theorem pairOperator_constantLift
    (action : M →ₗ[R] M) (derivative : R)
    (value : FixedKernel action) :
    pairOperator action derivative (constantLift action value) =
      (0, (-derivative) • value.1) := by
  rw [pairOperator_apply]
  change (value.1 - action value.1,
      0 - action 0 - derivative • action value.1) = _
  rw [action_eq_on_fixedKernel, sub_self, map_zero, sub_zero]
  simp [neg_smul]

@[simp] theorem pairConnecting_apply
    (action : M →ₗ[R] M) (derivative : R)
    (value : FixedKernel action) :
    pairConnecting action derivative value =
      Submodule.Quotient.mk
        (p := LinearMap.range (fixedDifference action))
        ((-derivative) • value.1) := by
  unfold pairConnecting infinitesimalQuotientReadout
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change Submodule.mkQ (LinearMap.range (fixedDifference action))
      ((pairOperator action derivative (constantLift action value)).2) = _
  rw [pairOperator_constantLift]
  exact Submodule.mkQ_apply _ _

/-- The matrix connecting construction is not a second Bockstein: it is
definitionally forced to be the existing coefficient-one quotient map. -/
theorem pairConnecting_eq_firstVariationBockstein
    (action : M →ₗ[R] M) (derivative : R) :
    pairConnecting action derivative =
      firstVariationBockstein action (-derivative) := by
  apply LinearMap.ext
  intro value
  rw [pairConnecting_apply, firstVariationBockstein_apply]

end


end SourceGeneratedScalarSquareZeroFirstOrder
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
