import H0mework.Versions.X.Fock.PrimeField.ClockResidualJoint

/-! Actual finite boundary words generate a compatible clock unit in the existing paired completion. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open CategoryTheory CategoryTheory.Limits

noncomputable section

def sourceCoordinate (stage : Nat) : jointData.StageQuotient stage := jointData.quotientMap stage (word stage)

theorem coordinate_transition (stage : Nat) :
    jointData.quotientTransition jointLaws stage (sourceCoordinate (stage + 1)) = sourceCoordinate stage := by
  change jointData.quotientTransition jointLaws stage (jointData.quotientMap (stage + 1) (word (stage + 1))) = _
  have source := LinearMap.congr_fun (jointData.quotientTransition_quotientMap jointLaws stage) (word (stage + 1))
  refine source.trans ?_
  apply jointData.stageRealization_injective stage
  change prefixEvaluator nativeAction jointObservation stage (word (stage + 1)) =
    prefixEvaluator nativeAction jointObservation stage (word stage)
  exact (joint_prefix (stage + 1) stage (by omega)).trans (joint_prefix stage stage le_rfl).symm

def coordinateMap (stage : Nat) : ℤ →ₗ[ℤ] jointData.StageQuotient stage :=
  LinearMap.toSpanSingleton ℤ _ (sourceCoordinate stage)

theorem coordinateMap_transition (stage : Nat) :
    (jointData.quotientTransition jointLaws stage).comp (coordinateMap (stage + 1)) = coordinateMap stage := by
  apply LinearMap.ext_ring
  simpa only [LinearMap.comp_apply, coordinateMap, LinearMap.toSpanSingleton_apply_one] using coordinate_transition stage

def sourceCone : Cone (jointData.quotientTower jointLaws) :=
  Cone.mk (ModuleCat.of ℤ ℤ) (NatTrans.ofOpSequence
    (fun stage => ModuleCat.ofHom (coordinateMap stage))
    (fun stage => by
      simp only [Functor.const_obj_map, SourceGeneratedScalarCofinalKernelCompletion.Data.quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact (coordinateMap_transition stage).symm))

def residual : JointField := (limit.lift (jointData.quotientTower jointLaws) sourceCone) (1 : ℤ)

theorem residual_coordinate (stage : Nat) :
    (jointData.restriction jointLaws stage).hom residual = sourceCoordinate stage := by
  have generated : (jointData.restriction jointLaws stage).hom residual = coordinateMap stage 1 :=
    ConcreteCategory.congr_hom (limit.lift_π sourceCone (Opposite.op stage)) (1 : ℤ)
  simpa only [coordinateMap, LinearMap.toSpanSingleton_apply_one] using generated

theorem residual_read (stage : Nat) :
    stageRead nativeAction jointObservation stage residual = fun _ => (0, 1) := by
  have source := congrArg (jointData.stageRealization stage) (residual_coordinate stage)
  change stageRead nativeAction jointObservation stage residual = prefixEvaluator nativeAction jointObservation stage (word stage) at source
  exact source.trans (joint_prefix stage stage le_rfl)

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
