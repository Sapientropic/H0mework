import H0mework.Arithmetic.CoPoisson.ThetaRoles

/-!
# Theta J-role Poisson relation quotient

All literal prime-power J-relations generate one integral relation
submodule.  Poisson summation places this whole span in the kernel of the
actual theta representation, so the representation descends to the presented
carrier.  Its faithful coimage is generated independently by the full
representation kernel.  The canonical map from the presented carrier to that
coimage retains its kernel as the exact remaining coupling/representation
residual; no vanishing claim is made.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace ThetaJRoleRelationQuotient

open ThetaJRoleRepresentation

noncomputable section

abbrev PrimePowerRelationIndex := Σ _prime : Nat.Primes, Nat

def primePowerRelationFamily (index : PrimePowerRelationIndex) :
    JRoleCarrier :=
  primePowerRelation index.1 index.2

/-- The integral span of every actual Poisson prime-power relation. -/
def PoissonRelationSubmodule : Submodule ℤ JRoleCarrier :=
  Submodule.span ℤ (Set.range primePowerRelationFamily)

theorem poissonRelationSubmodule_le_ker_representation :
    PoissonRelationSubmodule ≤ LinearMap.ker representation := by
  rw [PoissonRelationSubmodule, Submodule.span_le]
  rintro _ ⟨index, rfl⟩
  change representation (primePowerRelationFamily index) = 0
  exact representation_primePowerRelation_eq_zero index.1 index.2

/-- Presentation by the relations already certified by Poisson summation. -/
abbrev PresentedCarrier :=
  JRoleCarrier ⧸ PoissonRelationSubmodule

def presentedProjection : JRoleCarrier →ₗ[ℤ] PresentedCarrier :=
  Submodule.mkQ PoissonRelationSubmodule

def descendedRepresentation : PresentedCarrier →ₗ[ℤ] ComplexTempered :=
  PoissonRelationSubmodule.liftQ representation
    poissonRelationSubmodule_le_ker_representation

@[simp] theorem descendedRepresentation_projection :
    descendedRepresentation.comp presentedProjection = representation := by
  unfold descendedRepresentation presentedProjection
  exact Submodule.liftQ_mkQ _ _ _

theorem primePowerRelation_mem_poissonRelations
    (prime : Nat.Primes) (exponent : Nat) :
    primePowerRelation prime exponent ∈ PoissonRelationSubmodule := by
  apply Submodule.subset_span
  exact ⟨⟨prime, exponent⟩, rfl⟩

/-- Every generating Poisson relation is literally zero in the presented
carrier. -/
theorem presented_primePowerRelation_class_eq_zero
    (prime : Nat.Primes) (exponent : Nat) :
    presentedProjection (primePowerRelation prime exponent) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).2
    (primePowerRelation_mem_poissonRelations prime exponent)

theorem descendedRepresentation_primePowerRelation_class_eq_zero
    (prime : Nat.Primes) (exponent : Nat) :
    descendedRepresentation
        (presentedProjection (primePowerRelation prime exponent)) = 0 := by
  rw [presented_primePowerRelation_class_eq_zero, map_zero]

/-! ## Faithful coimage of the full representation -/

abbrev JRoleFaithfulCoimage :=
  JRoleCarrier ⧸ LinearMap.ker representation

def coimageProjection : JRoleCarrier →ₗ[ℤ] JRoleFaithfulCoimage :=
  Submodule.mkQ (LinearMap.ker representation)

def coimageRealization : JRoleFaithfulCoimage →ₗ[ℤ] ComplexTempered :=
  (LinearMap.ker representation).liftQ representation le_rfl

@[simp] theorem coimageRealization_projection :
    coimageRealization.comp coimageProjection = representation := by
  unfold coimageRealization coimageProjection
  exact Submodule.liftQ_mkQ _ _ _

theorem coimageRealization_injective :
    Function.Injective coimageRealization := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

/-- The canonical comparison generated only from the inclusion of the
Poisson relations in the full representation kernel. -/
def presentedToCoimage : PresentedCarrier →ₗ[ℤ] JRoleFaithfulCoimage :=
  PoissonRelationSubmodule.liftQ coimageProjection (by
    intro value relationMembership
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact poissonRelationSubmodule_le_ker_representation relationMembership)

@[simp] theorem presentedToCoimage_projection :
    presentedToCoimage.comp presentedProjection = coimageProjection := by
  unfold presentedToCoimage presentedProjection
  exact Submodule.liftQ_mkQ _ _ _

theorem coimageRealization_presentedToCoimage :
    coimageRealization.comp presentedToCoimage = descendedRepresentation := by
  apply LinearMap.ext
  intro presented
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective PoissonRelationSubmodule presented
  rfl

/-- The exact unresolved part after quotienting the known Poisson relations.
It is retained rather than declared zero. -/
abbrev RemainingCouplingResidual : Submodule ℤ PresentedCarrier :=
  LinearMap.ker presentedToCoimage

theorem remainingCouplingResidual_eq_representationKernel :
    RemainingCouplingResidual = LinearMap.ker descendedRepresentation := by
  apply le_antisymm
  · intro value valueKernel
    rw [LinearMap.mem_ker] at valueKernel ⊢
    have atValue := LinearMap.congr_fun
      coimageRealization_presentedToCoimage value
    rw [LinearMap.comp_apply, valueKernel, map_zero] at atValue
    exact atValue.symm
  · intro value valueKernel
    rw [LinearMap.mem_ker] at valueKernel ⊢
    apply coimageRealization_injective
    have atValue := LinearMap.congr_fun
      coimageRealization_presentedToCoimage value
    rw [LinearMap.comp_apply, valueKernel] at atValue
    simpa using atValue

theorem presentedToCoimage_injective_iff_residual_zero :
    Function.Injective presentedToCoimage ↔ RemainingCouplingResidual = ⊥ :=
  LinearMap.ker_eq_bot.symm

end
end ThetaJRoleRelationQuotient
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
