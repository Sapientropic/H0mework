import H0mework.Versions.AD.Realization.Perfectification.Occurrence.Temporal.Action.Installation
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Consumer
/-! The existing normal and debt consumers read the exact full temporal
inverse word, its original source receipt, whole write and canonical next. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceTemporalMaterial.Action
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceGeneratedScalarDifferentialResidual SourceOperationLogic SourceOperationLogic.FibreLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLivingRootClosure N V)
variable (origin : SourceNativeTemporalVisitAt (lower root))
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history original_material original_observation)
end O
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end M
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment activeContinuation no_refill wellFounded)
end P

theorem original_visit : decode (lower root) (actual root (code root origin)).1.1 = origin :=
  decode_encode (lower root) origin

theorem original_material : (actual root (code root origin)).1.2 =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      root.toAuthoritativeRoot (root.emitted origin.current) := rfl

theorem inverse_zero_iff : type_of%
    (liftingResidual_eq_zero_iff (morphism root (code root origin)) (oldWord root (code root origin))
      (target root (code root origin))) :=
  liftingResidual_eq_zero_iff (morphism root (code root origin)) _ _

theorem normal_inventory : O.value root.toAuthoritativeRoot origin.current (reader root origin) =
    updateInventory (R:=ℤ) (environment root (code root origin)) (delta root (code root origin))
      (nextWord root (code root origin)) :=
  (O.value_source root.toAuthoritativeRoot origin.current (reader root origin)).trans
    (residual_raw_value root (code root origin))

theorem normal_inverse_coordinate : O.value root.toAuthoritativeRoot origin.current (reader root origin) =
    updateInventory (R:=ℤ) (environment root (code root origin)) (delta root (code root origin))
      (targetCoordinate (morphism root (code root origin)) (oldWord root (code root origin))
        (target root (code root origin))).val :=
  (normal_inventory root origin).trans (congrArg
    (updateInventory (R:=ℤ) (environment root (code root origin)) (delta root (code root origin)))
    (reverse_coordinate root (code root origin)).symm)

theorem exact_cost : (O.trace root.toAuthoritativeRoot origin.current (reader root origin)).length =
    SaturationMonoid.SourceOperationExecution.Coefficients.cost (nextWord root (code root origin)) :=
  (O.paid_history root.toAuthoritativeRoot origin.current (reader root origin)).trans
    (SaturationMonoid.SourceOperationExecution.Coefficients.lifted_remaining _)

abbrev paid (count : Fin (remaining (residualRaw root (code root origin)).expression)) :=
  P.activePayment root.toAuthoritativeRoot origin.current (reader root origin) count
abbrev paidContinuation (count : Fin (remaining (residualRaw root (code root origin)).expression)) :=
  P.activeContinuation root.toAuthoritativeRoot origin.current (reader root origin) count

theorem no_refill (count : Nat) : type_of% (P.no_refill root.toAuthoritativeRoot origin.current (reader root origin) count) :=
  P.no_refill root.toAuthoritativeRoot origin.current (reader root origin) count

theorem wellFounded : type_of% (P.wellFounded root.toAuthoritativeRoot origin.current (reader root origin)) :=
  P.wellFounded root.toAuthoritativeRoot origin.current (reader root origin)

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query (C.sourceRoot (materialRoot root origin) (materialVisit root origin)) (materialVisit root origin) U7 calculus (reader root origin) offset) ∧
    type_of% (M.activated_answer (C.sourceRoot (materialRoot root origin) (materialVisit root origin)) (materialVisit root origin) U7 calculus (reader root origin) offset) ∧
    type_of% (M.activated_next (C.sourceRoot (materialRoot root origin) (materialVisit root origin)) (materialVisit root origin) U7 calculus (reader root origin) offset) :=
  ⟨M.activated_query (C.sourceRoot (materialRoot root origin) (materialVisit root origin)) (materialVisit root origin) U7 calculus (reader root origin) offset,
    M.activated_answer (C.sourceRoot (materialRoot root origin) (materialVisit root origin)) (materialVisit root origin) U7 calculus (reader root origin) offset,
    M.activated_next (C.sourceRoot (materialRoot root origin) (materialVisit root origin)) (materialVisit root origin) U7 calculus (reader root origin) offset⟩

theorem retained_visit (count : Nat) : type_of% (C.readback (materialRoot root origin) (materialVisit root origin) U7 calculus (reader root origin) count) :=
  C.readback (materialRoot root origin) (materialVisit root origin) U7 calculus (reader root origin) count

theorem material_read (count : Nat) : (materialFace root origin U7 calculus count).rootRead = material root origin := rfl

theorem parent_next (count : Nat) : root.generatedNextCurrentAt
    (decode (lower root) (materialFace root origin U7 calculus count).rootRead.1.1.1) =
      root.generatedNextCurrentAt origin :=
  congrArg root.generatedNextCurrentAt (decode_encode (lower root) origin)

theorem all_stage_whole_next (count : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (C.sourceRoot (materialRoot root origin) (materialVisit root origin)).toAuthoritativeRoot
      origin.current (reader root origin) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (C.sourceRoot (materialRoot root origin) (materialVisit root origin)).toAuthoritativeRoot
    origin.current (reader root origin) count
end SourceTemporalMaterial.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
