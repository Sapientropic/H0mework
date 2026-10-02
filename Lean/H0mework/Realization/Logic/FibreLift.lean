import H0mework.Realization.Logic.SourceScope
import H0mework.Foundation.Relations.Factorization.LivingLawRootGeneratedScalarSubfaceFactorizationKernel

/-! A source differential square generates fibre transport and the complete residual of reverse lifting. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationLogic.FibreLift

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedScalarDifferentialResidual

noncomputable section

universe r c d c' d'

variable {R : Type r} [CommRing R]
variable {C : Type c} {D : Type d} {C' : Type c'} {D' : Type d'}
variable [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
variable [AddCommGroup C'] [Module R C'] [AddCommGroup D'] [Module R D']
variable {e : C →ₗ[R] D} {e' : C' →ₗ[R] D'} (morphism : Morphism e e')

def kernelMap : LinearMap.ker e →ₗ[R] LinearMap.ker e' :=
  (morphism.sourceMap.comp (LinearMap.ker e).subtype).codRestrict (LinearMap.ker e') (by
    intro direction
    rw [LinearMap.mem_ker]
    have square := LinearMap.congr_fun morphism.commutes direction.val
    simp only [LinearMap.comp_apply] at square
    rw [show e direction.val = 0 from direction.property, map_zero] at square
    exact square.symm)

@[simp] theorem kernelMap_val (direction : LinearMap.ker e) :
    (kernelMap morphism direction).val = morphism.sourceMap direction.val := rfl

def mapFibre (source : C) : Fibre e (q e source) → Fibre e' (q e' (morphism.sourceMap source)) :=
  fun representative => ⟨morphism.sourceMap representative.val,
    congrArg (inducedResidualMap morphism) representative.property⟩

@[simp] theorem mapFibre_val (source : C) (representative : Fibre e (q e source)) :
    (mapFibre morphism source representative).val = morphism.sourceMap representative.val := rfl

@[simp] theorem mapFibre_sourceWitness (source : C) :
    mapFibre morphism source (sourceWitness e source) = sourceWitness e' (morphism.sourceMap source) := rfl

def targetCoordinate (source : C) (target : Fibre e' (q e' (morphism.sourceMap source))) : LinearMap.ker e' :=
  ⟨target.val - morphism.sourceMap source, (q_eq_iff e' _ _).mp target.property⟩

abbrev LiftingResidual := SourceGeneratedSubfaceFactorization.ResidualCarrier (kernelMap morphism)

def liftingResidual (source : C) (target : Fibre e' (q e' (morphism.sourceMap source))) : LiftingResidual morphism :=
  SourceGeneratedSubfaceFactorization.residualMap (LinearMap.id : LinearMap.ker e' →ₗ[R] LinearMap.ker e')
    (kernelMap morphism) (targetCoordinate morphism source target)

theorem liftingResidual_eq_zero_iff (source : C) (target : Fibre e' (q e' (morphism.sourceMap source))) :
    liftingResidual morphism source target = 0 ↔
      ∃ representative : Fibre e (q e source), mapFibre morphism source representative = target := by
  change Submodule.Quotient.mk (targetCoordinate morphism source target) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨direction, same⟩
    let representative : Fibre e (q e source) := ⟨source + direction.val, by
      apply (q_eq_iff e _ _).mpr
      simpa only [add_sub_cancel_left] using direction.property⟩
    refine ⟨representative, ?_⟩
    apply Subtype.ext
    have sourceEquality := congrArg Subtype.val same
    change morphism.sourceMap direction.val = target.val - morphism.sourceMap source at sourceEquality
    change morphism.sourceMap (source + direction.val) = target.val
    rw [map_add, sourceEquality]
    exact add_sub_cancel _ _
  · rintro ⟨representative, same⟩
    refine ⟨⟨representative.val - source, (q_eq_iff e _ _).mp representative.property⟩, ?_⟩
    apply Subtype.ext
    change morphism.sourceMap (representative.val - source) = target.val - morphism.sourceMap source
    rw [map_sub]
    exact congrArg (· - morphism.sourceMap source) (congrArg Subtype.val same)

@[simp] theorem liftingResidual_mapFibre (source : C) (representative : Fibre e (q e source)) :
    liftingResidual morphism source (mapFibre morphism source representative) = 0 :=
  (liftingResidual_eq_zero_iff morphism source _).mpr ⟨representative, rfl⟩

@[simp] theorem liftingResidual_sourceWitness (source : C) :
    liftingResidual morphism source (sourceWitness e' (morphism.sourceMap source)) = 0 :=
  (liftingResidual_eq_zero_iff morphism source _).mpr
    ⟨sourceWitness e source, mapFibre_sourceWitness morphism source⟩

end
end SaturationMonoid.SourceOperationLogic.FibreLift
