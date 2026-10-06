import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Calculation
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
variable (value : C root visit recognition)
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end O
theorem normal : O.value root.toAuthoritativeRoot visit.current
    (pairedReader root visit recognition successor transition node value) =
      (sourceResidual root visit recognition successor transition node value,
        targetResidual root visit recognition successor transition node (RootLawDependentJointTransition.carrierMap transition.history value)) :=
  (O.value_source root.toAuthoritativeRoot visit.current (pairedReader root visit recognition successor transition node value)).trans
    (paired_value root visit recognition successor transition node value)
theorem normal_equation : (O.value root.toAuthoritativeRoot visit.current
    (pairedReader root visit recognition successor transition node value)).2 =
      (O.value root.toAuthoritativeRoot visit.current
        (pairedReader root visit recognition successor transition node value)).1 := by
  rw [normal]
  exact vector_transport root visit recognition successor transition node value

theorem cost : (O.trace root.toAuthoritativeRoot visit.current
    (pairedReader root visit recognition successor transition node value)).length = 19 :=
  (O.paid_history root.toAuthoritativeRoot visit.current (pairedReader root visit recognition successor transition node value)).trans (by rfl)
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment no_refill wellFounded)
end P
abbrev payment (count : Fin 19) := P.activePayment root.toAuthoritativeRoot visit.current
  (pairedReader root visit recognition successor transition node value) ⟨count.1, count.2⟩
theorem no_refill (count : Nat) : type_of% (P.no_refill root.toAuthoritativeRoot visit.current
    (pairedReader root visit recognition successor transition node value) count) :=
  P.no_refill root.toAuthoritativeRoot visit.current (pairedReader root visit recognition successor transition node value) count
theorem wellFounded : type_of% (P.wellFounded root.toAuthoritativeRoot visit.current
    (pairedReader root visit recognition successor transition node value)) :=
  P.wellFounded root.toAuthoritativeRoot visit.current (pairedReader root visit recognition successor transition node value)
theorem whole_next (count : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (SourceTemporalMaterial.Calculation.sourceRoot root visit).toAuthoritativeRoot visit.current
      (pairedReader root visit recognition successor transition node value) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (SourceTemporalMaterial.Calculation.sourceRoot root visit).toAuthoritativeRoot visit.current
    (pairedReader root visit recognition successor transition node value) count
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end M
theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query (SourceTemporalMaterial.Calculation.sourceRoot root visit) visit U7 calculus (pairedReader root visit recognition successor transition node value) offset) ∧
    type_of% (M.activated_answer (SourceTemporalMaterial.Calculation.sourceRoot root visit) visit U7 calculus (pairedReader root visit recognition successor transition node value) offset) ∧
    type_of% (M.activated_next (SourceTemporalMaterial.Calculation.sourceRoot root visit) visit U7 calculus (pairedReader root visit recognition successor transition node value) offset) :=
  ⟨M.activated_query (SourceTemporalMaterial.Calculation.sourceRoot root visit) visit U7 calculus (pairedReader root visit recognition successor transition node value) offset,
    M.activated_answer (SourceTemporalMaterial.Calculation.sourceRoot root visit) visit U7 calculus (pairedReader root visit recognition successor transition node value) offset,
    M.activated_next (SourceTemporalMaterial.Calculation.sourceRoot root visit) visit U7 calculus (pairedReader root visit recognition successor transition node value) offset⟩
end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
