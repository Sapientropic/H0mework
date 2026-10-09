import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)


variable (point : Carrier root recognition visit successor)
variable (word : List (Letter root recognition visit successor))
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count point word)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count point word =
    Inventory.normal root recognition visit successor transition alignment U7 calculus count point word :=
  ((RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point word)).trans
    (programme_value root recognition visit successor transition alignment U7 calculus count point word)).trans
    (Inventory.normal_value root recognition visit successor transition alignment U7 calculus count point word).symm

theorem normal_read (following : List (Letter root recognition visit successor)) :
    readout root recognition visit successor transition alignment U7 calculus count following
      (normal root recognition visit successor transition alignment U7 calculus count point word) =
      read root recognition visit successor transition alignment U7 calculus count
        (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) (word++following) point) := by
  rw [normal_value]
  exact Inventory.normal_read root recognition visit successor transition alignment U7 calculus count point word following

theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point word)).length = word.length+3 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_budget root recognition visit successor transition alignment U7 calculus count word)
theorem acted_cost : (acted root recognition visit successor transition alignment U7 calculus count point word).2.1.length = word.length+2 :=
  (acted root recognition visit successor transition alignment U7 calculus count point word).2.1.length_to_const.trans
    (by rw [whole_budget]; change 2+word.length=word.length+2; omega)
def materialFace : SourceNativeRootSemanticFaceAt
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point word) visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (EffectHistory.sourceRoot root recognition visit successor transition alignment U7 calculus count point word).source.base
    (component root recognition visit successor transition alignment U7 calculus count point word)).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem acted_read : (materialFace root recognition visit successor transition alignment U7 calculus count point word).rootRead.2.2.2.1.1 =
    actedComplete root recognition visit successor transition alignment U7 calculus count
      (sourceMap root recognition visit successor transition alignment U7 calculus count point) word :=
  acted_value root recognition visit successor transition alignment U7 calculus count point word

theorem same_execution : HEq
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
      (reader root recognition visit successor transition alignment U7 calculus count point word))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (original root recognition visit successor transition alignment U7 calculus count point word) visit.current
      (originalReader root recognition visit successor transition alignment U7 calculus count point word)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (raw root recognition visit successor transition alignment U7 calculus count point word)
theorem actual_environment {current : (frame root recognition visit successor transition alignment U7 calculus count point word).V.Current}
    (occurrence : (frame root recognition visit successor transition alignment U7 calculus count point word).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (frame root recognition visit successor transition alignment U7 calculus count point word).environment occurrence =
      updatedEnvironment root recognition visit successor transition alignment U7 calculus count
        (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point)
        (actedComplete root recognition visit successor transition alignment U7 calculus count
          (sourceMap root recognition visit successor transition alignment U7 calculus count point) word) :=
  congrArg₂ (updatedEnvironment root recognition visit successor transition alignment U7 calculus count)
    (Inventory.acted_value root recognition visit successor transition alignment U7 calculus count point word)
    (acted_value root recognition visit successor transition alignment U7 calculus count point word)
namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian installed_born_inventory old_past_born)
end Request

theorem query_next (stage : Nat) : type_of% (Request.queryAt
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word) stage) ∧
    type_of% (Request.nextAt
      (seed root recognition visit successor transition alignment U7 calculus count point word)
      (frame root recognition visit successor transition alignment U7 calculus count point word) stage) :=
  ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word) stage) ∧
    type_of% (Request.noetherian
      (seed root recognition visit successor transition alignment U7 calculus count point word)
      (frame root recognition visit successor transition alignment U7 calculus count point word) stage) :=
  ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem born_inventory : type_of% (Request.installed_born_inventory
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word)) :=
  Request.installed_born_inventory _ _
theorem all_inventory : type_of% (Request.old_past_born
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word)) :=
  Request.old_past_born _ _
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
