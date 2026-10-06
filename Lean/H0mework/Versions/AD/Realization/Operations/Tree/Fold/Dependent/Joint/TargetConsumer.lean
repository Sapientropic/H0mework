import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.TargetCalculation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (node : GeneratedNodeAt (recognition.generateStepAt visit) successor transition.history)
variable (sourceWord : SourceWord root visit recognition) (targetWord : TargetWord root visit recognition successor)
namespace TargetO
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end TargetO
theorem target_normal : TargetO.value root.toAuthoritativeRoot visit.current
    (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) =
      (targetDifference root visit recognition successor transition node (fromSourceWord root visit recognition sourceWord) (fromTargetWord root visit recognition successor targetWord),
        targetObservationResidual root visit recognition successor transition node (fromSourceWord root visit recognition sourceWord) (fromTargetWord root visit recognition successor targetWord),
        targetRangeResidual root visit recognition successor transition node (fromSourceWord root visit recognition sourceWord) (fromTargetWord root visit recognition successor targetWord)) :=
  (TargetO.value_source root.toAuthoritativeRoot visit.current (targetCalculationReader root visit recognition successor transition node sourceWord targetWord)).trans
    (target_programme_value root visit recognition successor transition node sourceWord targetWord)
theorem target_normal_inverse :
    (∃ representative : SourceOperationLogic.Fibre (sourceDifferential root visit recognition successor transition node)
      (SourceOperationLogic.q (sourceDifferential root visit recognition successor transition node)
        (sourceActionValue root visit recognition successor transition node (fromSourceWord root visit recognition sourceWord))),
      RootLawDependentJointTransition.carrierMap transition.history representative.val =
        targetActionValue root visit recognition successor transition node (fromTargetWord root visit recognition successor targetWord)) ↔
    (TargetO.value root.toAuthoritativeRoot visit.current (targetCalculationReader root visit recognition successor transition node sourceWord targetWord)).2.1 = 0 ∧
      (TargetO.value root.toAuthoritativeRoot visit.current (targetCalculationReader root visit recognition successor transition node sourceWord targetWord)).2.2 = 0 := by
  rw [target_normal]
  exact fibre_preimage_exact root visit recognition successor transition node _ _

theorem target_programme_cost : (TargetO.trace root.toAuthoritativeRoot visit.current
    (targetCalculationReader root visit recognition successor transition node sourceWord targetWord)).length = 25 :=
  (TargetO.paid_history root.toAuthoritativeRoot visit.current (targetCalculationReader root visit recognition successor transition node sourceWord targetWord)).trans (by rfl)
namespace TargetP
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment no_refill wellFounded)
end TargetP
abbrev target_payment (count : Fin 25) := TargetP.activePayment root.toAuthoritativeRoot visit.current
  (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) ⟨count.1, count.2⟩
theorem target_no_refill (count : Nat) : type_of% (TargetP.no_refill root.toAuthoritativeRoot visit.current
    (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) count) :=
  TargetP.no_refill root.toAuthoritativeRoot visit.current (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) count
theorem target_wellFounded : type_of% (TargetP.wellFounded root.toAuthoritativeRoot visit.current
    (targetCalculationReader root visit recognition successor transition node sourceWord targetWord)) :=
  TargetP.wellFounded root.toAuthoritativeRoot visit.current (targetCalculationReader root visit recognition successor transition node sourceWord targetWord)
theorem target_whole_next (count : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord).toAuthoritativeRoot visit.current
      (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord).toAuthoritativeRoot visit.current
    (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) count
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
namespace TargetM
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end TargetM
theorem target_query_answer_next (offset : Nat) :
    type_of% (TargetM.activated_query (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord) visit U7 calculus (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) offset) ∧
    type_of% (TargetM.activated_answer (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord) visit U7 calculus (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) offset) ∧
    type_of% (TargetM.activated_next (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord) visit U7 calculus (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) offset) :=
  ⟨TargetM.activated_query (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord) visit U7 calculus (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) offset,
    TargetM.activated_answer (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord) visit U7 calculus (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) offset,
    TargetM.activated_next (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord) visit U7 calculus (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) offset⟩
end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
