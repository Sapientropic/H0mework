import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Scalar-polymorphic source perfectification

The original additive foundation uses integral linear maps.  Analytic source
carriers, however, naturally expose evaluations over coefficient rings such
as `ℂ`.  This kernel removes the coefficient privilege: for any commutative
ring `R` and actual evaluation `e : C →ₗ[R] Dual_R(D)`, it constructs the
canonical coimage `C / ker(e)`, its faithful dual embedding, quotient
universal property, and source-morphism transport.

No finite, projective, topological, perfect, determinant, or inverse premise
enters the constructor.  The integral producer is definitionally the
`R = ℤ` specialization of this carrier and map shape.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarPerfectification

noncomputable section

universe r c d a

variable {R : Type r} [CommRing R]
variable {C : Type c} {D : Type d}
variable [AddCommGroup C] [Module R C]
variable [AddCommGroup D] [Module R D]
variable (evaluation : C →ₗ[R] Module.Dual R D)

abbrev PerfectificationCarrier := C ⧸ LinearMap.ker evaluation

def canonicalMap : C →ₗ[R] PerfectificationCarrier evaluation :=
  Submodule.mkQ _

def dualEmbedding : PerfectificationCarrier evaluation →ₗ[R]
    Module.Dual R D :=
  (LinearMap.ker evaluation).liftQ evaluation le_rfl

@[simp] theorem dualEmbedding_comp_canonicalMap :
    (dualEmbedding evaluation).comp (canonicalMap evaluation) = evaluation := by
  apply LinearMap.ext
  intro value
  rfl

theorem dualEmbedding_injective :
    Function.Injective (dualEmbedding evaluation) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

def canonicalFactor
    {Q : Type a} [AddCommGroup Q] [Module R Q]
    (map : C →ₗ[R] Q)
    (kernel_compatibility : LinearMap.ker evaluation ≤ LinearMap.ker map) :
    PerfectificationCarrier evaluation →ₗ[R] Q :=
  (LinearMap.ker evaluation).liftQ map kernel_compatibility

@[simp] theorem canonicalFactor_comp
    {Q : Type a} [AddCommGroup Q] [Module R Q]
    (map : C →ₗ[R] Q)
    (kernel_compatibility : LinearMap.ker evaluation ≤ LinearMap.ker map) :
    (canonicalFactor evaluation map kernel_compatibility).comp
        (canonicalMap evaluation) = map := by
  unfold canonicalFactor canonicalMap
  apply Submodule.liftQ_mkQ

theorem canonicalFactor_unique
    {Q : Type a} [AddCommGroup Q] [Module R Q]
    (map : C →ₗ[R] Q)
    (kernel_compatibility : LinearMap.ker evaluation ≤ LinearMap.ker map)
    (other : PerfectificationCarrier evaluation →ₗ[R] Q)
    (other_commutes : other.comp (canonicalMap evaluation) = map) :
    other = canonicalFactor evaluation map kernel_compatibility := by
  apply LinearMap.ext
  intro quotientValue
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker evaluation) quotientValue
  have equality := LinearMap.congr_fun other_commutes value
  exact equality.trans (by rfl)

theorem canonicalMap_universal
    {Q : Type a} [AddCommGroup Q] [Module R Q]
    (map : C →ₗ[R] Q)
    (kernel_compatibility : LinearMap.ker evaluation ≤ LinearMap.ker map) :
    ∃! factor : PerfectificationCarrier evaluation →ₗ[R] Q,
      factor.comp (canonicalMap evaluation) = map := by
  refine ⟨canonicalFactor evaluation map kernel_compatibility,
    canonicalFactor_comp evaluation map kernel_compatibility, ?_⟩
  intro other other_eq
  exact canonicalFactor_unique evaluation map kernel_compatibility other other_eq

/-! ## Faithful-map factorization and explicit residual -/

variable {A : Type a} [AddCommGroup A] [Module R A]
variable (faithful : C →ₗ[R] A)

structure FaithfulFactorizationResidual where
  coordinate : C
  invisible_to_dual : coordinate ∈ LinearMap.ker evaluation
  visible_to_actual : faithful coordinate ≠ 0

theorem faithful_factorization_exists_iff :
    (∃ factor : PerfectificationCarrier evaluation →ₗ[R] A,
      factor.comp (canonicalMap evaluation) = faithful) ↔
      LinearMap.ker evaluation ≤ LinearMap.ker faithful := by
  constructor
  · rintro ⟨factor, factorization⟩ value value_mem
    rw [LinearMap.mem_ker] at value_mem ⊢
    have equality := LinearMap.congr_fun factorization value
    have canonical_zero : canonicalMap evaluation value = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 value_mem
    rw [LinearMap.comp_apply, canonical_zero, map_zero] at equality
    exact equality.symm
  · intro compatibility
    exact ⟨canonicalFactor evaluation faithful compatibility,
      canonicalFactor_comp evaluation faithful compatibility⟩

/-! ## Scalar source-morphism naturality -/

variable {C' : Type c} {D' : Type d}
variable [AddCommGroup C'] [Module R C']
variable [AddCommGroup D'] [Module R D']
variable (evaluation' : C' →ₗ[R] Module.Dual R D')

def inducedDualTarget (dualMap : D' →ₗ[R] D) :
    Module.Dual R D →ₗ[R] Module.Dual R D' :=
  dualMap.dualMap

@[simp] theorem inducedDualTarget_apply (dualMap : D' →ₗ[R] D)
    (functional : Module.Dual R D) (value : D') :
    inducedDualTarget dualMap functional value = functional (dualMap value) :=
  LinearMap.dualMap_apply dualMap functional value

def inducedPerfectificationMap
    (carrierMap : C →ₗ[R] C')
    (dualMap : D' →ₗ[R] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    PerfectificationCarrier evaluation →ₗ[R]
      PerfectificationCarrier evaluation' :=
  (LinearMap.ker evaluation).liftQ
    ((canonicalMap evaluation').comp carrierMap)
    (by
      intro value value_mem
      rw [LinearMap.mem_ker] at value_mem ⊢
      apply (Submodule.Quotient.mk_eq_zero _).2
      have equality := LinearMap.congr_fun naturality value
      have left_zero : inducedDualTarget dualMap (evaluation value) = 0 := by
        rw [value_mem]
        rfl
      exact LinearMap.mem_ker.mpr (equality.symm.trans left_zero))

theorem inducedPerfectificationMap_comp
    (carrierMap : C →ₗ[R] C')
    (dualMap : D' →ₗ[R] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    (inducedPerfectificationMap evaluation evaluation' carrierMap dualMap
      naturality).comp (canonicalMap evaluation) =
      (canonicalMap evaluation').comp carrierMap := by
  unfold inducedPerfectificationMap canonicalMap
  apply Submodule.liftQ_mkQ

theorem dualEmbedding_naturality
    (carrierMap : C →ₗ[R] C')
    (dualMap : D' →ₗ[R] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    (dualEmbedding evaluation').comp
        (inducedPerfectificationMap evaluation evaluation' carrierMap dualMap
          naturality) =
      (inducedDualTarget dualMap).comp (dualEmbedding evaluation) := by
  apply LinearMap.ext
  intro quotientValue
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker evaluation) quotientValue
  have equality := LinearMap.congr_fun naturality value
  exact equality.symm

end
end SourceGeneratedScalarPerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
