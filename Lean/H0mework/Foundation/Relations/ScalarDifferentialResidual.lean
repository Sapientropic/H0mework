import Mathlib.LinearAlgebra.Isomorphisms
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Scalar differential residuals

For any `R`-linear differential `d : C →ₗ[R] D`, the exact observable
residual is its coimage `C / ker(d)`.  It is canonically equivalent to the
actual range of `d`, has the quotient universal property, and is natural for
commuting squares.  No finiteness, projectivity, duality, determinant, or
chosen complement enters the construction.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarDifferentialResidual

noncomputable section

universe r c d q c₂ d₂ c₃ d₃ u

variable {R : Type r} [CommRing R]
variable {C : Type c} {D : Type d}
variable [AddCommGroup C] [Module R C]
variable [AddCommGroup D] [Module R D]
variable (differential : C →ₗ[R] D)

abbrev ResidualCarrier := C ⧸ LinearMap.ker differential

def canonicalResidual : C →ₗ[R] ResidualCarrier differential :=
  Submodule.mkQ _

@[simp] theorem canonicalResidual_eq_zero_iff (value : C) :
    canonicalResidual differential value = 0 ↔ differential value = 0 := by
  rw [canonicalResidual, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_ker]

theorem canonicalResidual_ne_zero_iff (value : C) :
    canonicalResidual differential value ≠ 0 ↔ differential value ≠ 0 :=
  not_congr (canonicalResidual_eq_zero_iff differential value)

def rangeMap : C →ₗ[R] LinearMap.range differential :=
  differential.codRestrict (LinearMap.range differential)
    (fun value => ⟨value, rfl⟩)

def residualToRange : ResidualCarrier differential →ₗ[R]
    LinearMap.range differential :=
  (LinearMap.ker differential).liftQ (rangeMap differential) (by
    intro value value_mem
    rw [LinearMap.mem_ker] at value_mem ⊢
    apply Subtype.ext
    exact value_mem)

@[simp] theorem residualToRange_canonicalResidual (value : C) :
    residualToRange differential (canonicalResidual differential value) =
      rangeMap differential value :=
  rfl

theorem residualToRange_injective :
    Function.Injective (residualToRange differential) := by
  intro left right equality
  obtain ⟨leftValue, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker differential) left
  obtain ⟨rightValue, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker differential) right
  apply (Submodule.Quotient.eq _).2
  rw [LinearMap.mem_ker]
  have valueEquality := congrArg Subtype.val equality
  change differential leftValue = differential rightValue at valueEquality
  rw [map_sub, valueEquality, sub_self]

theorem residualToRange_surjective :
    Function.Surjective (residualToRange differential) := by
  intro target
  rcases target.property with ⟨value, equality⟩
  refine ⟨canonicalResidual differential value, ?_⟩
  apply Subtype.ext
  exact equality

def residualEquivRange : ResidualCarrier differential ≃ₗ[R]
    LinearMap.range differential :=
  LinearEquiv.ofBijective (residualToRange differential)
    ⟨residualToRange_injective differential,
      residualToRange_surjective differential⟩

/-- Every source map killing the differential kernel factors uniquely
through the exact residual carrier. -/
theorem universal_factorization
    {Q : Type q} [AddCommGroup Q] [Module R Q]
    (map : C →ₗ[R] Q)
    (kernel_compatibility :
      LinearMap.ker differential ≤ LinearMap.ker map) :
    ∃! factor : ResidualCarrier differential →ₗ[R] Q,
      factor.comp (canonicalResidual differential) = map := by
  let factor : ResidualCarrier differential →ₗ[R] Q :=
    (LinearMap.ker differential).liftQ map kernel_compatibility
  refine ⟨factor, ?_, ?_⟩
  · apply LinearMap.ext
    intro value
    rfl
  · intro other other_commutes
    apply LinearMap.ext
    intro residual
    obtain ⟨value, rfl⟩ :=
      Submodule.mkQ_surjective (LinearMap.ker differential) residual
    have equality := LinearMap.congr_fun other_commutes value
    exact equality.trans (by rfl)

/-! ## Naturality for commuting differential squares -/

variable {C₂ : Type c₂} {D₂ : Type d₂}
variable [AddCommGroup C₂] [Module R C₂]
variable [AddCommGroup D₂] [Module R D₂]

structure Morphism (source : C →ₗ[R] D) (target : C₂ →ₗ[R] D₂) where
  sourceMap : C →ₗ[R] C₂
  targetMap : D →ₗ[R] D₂
  commutes : targetMap.comp source = target.comp sourceMap

namespace Morphism

def id (source : C →ₗ[R] D) : Morphism source source where
  sourceMap := LinearMap.id
  targetMap := LinearMap.id
  commutes := by rfl

variable {C₃ : Type c₃} {D₃ : Type d₃}
variable [AddCommGroup C₃] [Module R C₃]
variable [AddCommGroup D₃] [Module R D₃]

def comp {firstDifferential : C →ₗ[R] D}
    {middleDifferential : C₂ →ₗ[R] D₂}
    {lastDifferential : C₃ →ₗ[R] D₃}
    (second : Morphism middleDifferential lastDifferential)
    (first : Morphism firstDifferential middleDifferential) :
    Morphism firstDifferential lastDifferential where
  sourceMap := second.sourceMap.comp first.sourceMap
  targetMap := second.targetMap.comp first.targetMap
  commutes := by
    apply LinearMap.ext
    intro value
    have firstAt := LinearMap.congr_fun first.commutes value
    have secondAt := LinearMap.congr_fun second.commutes (first.sourceMap value)
    simp only [LinearMap.comp_apply] at firstAt secondAt ⊢
    rw [firstAt, secondAt]

end Morphism

def inducedResidualMap
    {source : C →ₗ[R] D} {target : C₂ →ₗ[R] D₂}
    (morphism : Morphism source target) :
    ResidualCarrier source →ₗ[R] ResidualCarrier target :=
  (LinearMap.ker source).liftQ
    ((canonicalResidual target).comp morphism.sourceMap) (by
      intro value value_mem
      rw [LinearMap.mem_ker] at value_mem ⊢
      apply (Submodule.Quotient.mk_eq_zero _).2
      rw [LinearMap.mem_ker]
      have square := LinearMap.congr_fun morphism.commutes value
      simp only [LinearMap.comp_apply] at square
      rw [value_mem, map_zero] at square
      exact square.symm)

@[simp] theorem inducedResidualMap_comp_canonical
    {source : C →ₗ[R] D} {target : C₂ →ₗ[R] D₂}
    (morphism : Morphism source target) :
    (inducedResidualMap morphism).comp (canonicalResidual source) =
      (canonicalResidual target).comp morphism.sourceMap := by
  apply LinearMap.ext
  intro value
  rfl

theorem inducedResidualMap_id (source : C →ₗ[R] D) :
    inducedResidualMap (Morphism.id source) = LinearMap.id := by
  apply LinearMap.ext
  intro residual
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker source) residual
  rfl

variable {C₃ : Type c₃} {D₃ : Type d₃}
variable [AddCommGroup C₃] [Module R C₃]
variable [AddCommGroup D₃] [Module R D₃]

theorem inducedResidualMap_comp
    {firstDifferential : C →ₗ[R] D}
    {middleDifferential : C₂ →ₗ[R] D₂}
    {lastDifferential : C₃ →ₗ[R] D₃}
    (second : Morphism middleDifferential lastDifferential)
    (first : Morphism firstDifferential middleDifferential) :
    inducedResidualMap (second.comp first) =
      (inducedResidualMap second).comp (inducedResidualMap first) := by
  apply LinearMap.ext
  intro residual
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker firstDifferential) residual
  rfl

/-! ## Same-root occurrence installation -/

variable {Root : Type u}

abbrev RootResidualPayload
    (differentialAt : Root → C →ₗ[R] D) :=
  Σ root : Root, ResidualCarrier (differentialAt root)

/-- Residual coordinates are installed by relabelling the complete source
occurrence.  This is not a new zero-step root. -/
def residualOccurrence
    (rootOccurrence : RootedAccountedUnfolding Root)
    (differentialAt : Root → C →ₗ[R] D)
    (valueAt : Root → C) :
    RootedAccountedUnfolding (RootResidualPayload differentialAt) :=
  rootOccurrence.map fun root =>
    ⟨root, canonicalResidual (differentialAt root) (valueAt root)⟩

theorem residualOccurrence_projects
    (rootOccurrence : RootedAccountedUnfolding Root)
    (differentialAt : Root → C →ₗ[R] D)
    (valueAt : Root → C) :
    (residualOccurrence rootOccurrence differentialAt valueAt).map Sigma.fst =
      rootOccurrence := by
  rw [residualOccurrence, RootedAccountedUnfolding.map_map]
  change rootOccurrence.map id = rootOccurrence
  exact RootedAccountedUnfolding.map_id rootOccurrence

@[simp] theorem residualOccurrence_root
    (rootOccurrence : RootedAccountedUnfolding Root)
    (differentialAt : Root → C →ₗ[R] D)
    (valueAt : Root → C) :
    (residualOccurrence rootOccurrence differentialAt valueAt).root =
      ⟨rootOccurrence.root,
        canonicalResidual (differentialAt rootOccurrence.root)
          (valueAt rootOccurrence.root)⟩ :=
  by
    unfold residualOccurrence
    exact RootedAccountedUnfolding.root_map _ rootOccurrence

theorem residualOccurrence_root_zero_iff
    (rootOccurrence : RootedAccountedUnfolding Root)
    (differentialAt : Root → C →ₗ[R] D)
    (valueAt : Root → C) :
    (residualOccurrence rootOccurrence differentialAt valueAt).root.2 = 0 ↔
      differentialAt rootOccurrence.root (valueAt rootOccurrence.root) = 0 :=
  by
    rw [residualOccurrence_root]
    exact canonicalResidual_eq_zero_iff _ _

end
end SourceGeneratedScalarDifferentialResidual
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
