import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Consumer
import H0mework.Realization.Logic.FibreLift

/-! The actual update square transports every source representative. Its
reverse lifting residual retains the complete old/effect pair, including
directions invisible after addition at the literal next read. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceOperationLogic SourceOperationLogic.FibreLift
open SourceGeneratedScalarDifferentialResidual

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)

abbrev Word := Formal ℤ PhysicalValue PhysicalVar sort
def pairInventory (state : runtime.State) : Word (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort) →ₗ[ℤ] PhysicalValue sort × PhysicalValue sort :=
  updateInventory (R := ℤ) (readEnv runtime source state) (increment runtime source state)

def nextEvaluation (state : runtime.State) : Word (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort) →ₗ[ℤ] PhysicalValue sort :=
  evaluation (R := ℤ) (readEnv runtime source state.tick.nextState)

def actualMorphism (state : runtime.State) :
    Morphism (pairInventory runtime source state) (nextEvaluation runtime source state) where
  sourceMap := LinearMap.id
  targetMap := additionReadout (R := ℤ)
  commutes := by
    have square := (updateMorphism (R := ℤ) (s := sort) (readEnv runtime source state)
      (increment runtime source state)).commutes
    change (additionReadout (R := ℤ)).comp (updateInventory (R := ℤ)
      (readEnv runtime source state) (increment runtime source state)) =
      (evaluation (R := ℤ) (readEnv runtime source state + increment runtime source state)).comp LinearMap.id at square
    rw [updated_environment] at square
    exact square

def pairOnNextKernel (state : runtime.State) :
    LinearMap.ker (nextEvaluation runtime source state) →ₗ[ℤ] PhysicalValue sort × PhysicalValue sort :=
  (pairInventory runtime source state).comp (LinearMap.ker (nextEvaluation runtime source state)).subtype

theorem kernelMap_range (state : runtime.State) :
    LinearMap.range (kernelMap (actualMorphism runtime source state)) =
      LinearMap.ker (pairOnNextKernel runtime source state) := by
  ext direction
  constructor
  · rintro ⟨original, rfl⟩
    exact original.property
  · intro pairZero
    refine ⟨⟨direction.val, pairZero⟩, ?_⟩
    exact Subtype.ext rfl

def residualEquiv (state : runtime.State) :
    LiftingResidual (actualMorphism runtime source state) ≃ₗ[ℤ]
      LinearMap.range (pairOnNextKernel runtime source state) :=
  (Submodule.quotEquivOfEq _ _ (kernelMap_range runtime source state)).trans
    (residualEquivRange (pairOnNextKernel runtime source state))

def recover (state : runtime.State) :
    LiftingResidual (actualMorphism runtime source state) →ₗ[ℤ] PhysicalValue sort × PhysicalValue sort :=
  (LinearMap.range (pairOnNextKernel runtime source state)).subtype.comp
    (residualEquiv runtime source state).toLinearMap

theorem recover_injective (state : runtime.State) : Function.Injective (recover runtime source state) := by
  intro first second same
  apply (residualEquiv runtime source state).injective
  exact Subtype.ext same

theorem recover_liftingResidual (state : runtime.State) (word : Word (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort))
    (target : Fibre (nextEvaluation runtime source state) (q (nextEvaluation runtime source state) ((actualMorphism runtime source state).sourceMap word))) :
    recover runtime source state (liftingResidual (actualMorphism runtime source state) word target) =
      pairInventory runtime source state (target.val - word) := by
  unfold recover residualEquiv liftingResidual
  rw [LinearMap.comp_apply]
  change (((Submodule.quotEquivOfEq _ _ (kernelMap_range runtime source state)).trans
    (residualEquivRange (pairOnNextKernel runtime source state)))
      (Submodule.Quotient.mk (targetCoordinate (actualMorphism runtime source state) word target))).val = _
  rw [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

theorem recover_balanced (state : runtime.State)
    (residual : LiftingResidual (actualMorphism runtime source state)) :
    (recover runtime source state residual).1 + (recover runtime source state residual).2 = 0 := by
  obtain ⟨direction, same⟩ := (residualEquiv runtime source state residual).property
  change (residualEquiv runtime source state residual).val.1 +
    (residualEquiv runtime source state residual).val.2 = 0
  rw [← same]
  exact (LinearMap.congr_fun (actualMorphism runtime source state).commutes direction.val).trans direction.property

def relationWitness (state : runtime.State) :
    Fibre (pairInventory runtime source state)
      (q (pairInventory runtime source state)
        (relationMap (R := ℤ) (readEnv runtime source state) (relationWords runtime source state))) :=
  sourceWitness _ _

theorem actual_relation_transport (state : runtime.State) :
    (mapFibre (actualMorphism runtime source state)
      (relationMap (R := ℤ) (readEnv runtime source state) (relationWords runtime source state))
      (relationWitness runtime source state)).val =
        relationMap (R := ℤ) (readEnv runtime source state) (relationWords runtime source state) := rfl

end SourceOperationInquiry.Context.Faces
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
