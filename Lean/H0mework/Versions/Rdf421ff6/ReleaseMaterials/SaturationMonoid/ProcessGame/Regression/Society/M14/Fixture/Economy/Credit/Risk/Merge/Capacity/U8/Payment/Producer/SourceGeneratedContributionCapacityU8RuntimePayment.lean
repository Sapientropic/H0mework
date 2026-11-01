import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Action.SourceGeneratedContributionCapacityU8TargetState

/-!
# Source-generated U8-root runtime payment

The U8 root no longer advances on a `Unit` write.  Every exact local current
generates the actual-service occurrence at global depth `current + 2`; the
same event indexes its complete Fin-3 write and compiler successor.  This is
the source-native payment needed by runtime depth four and the depth-five
reopening action source.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityU8RuntimePayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState

def contributionCapacityU8RuntimePaymentCurrentAt
    (oldVisit : OldVisit) (index : Nat) : Nat :=
  show Nat from (contributionCapacityU8TemporalVisitAt oldVisit index).current

@[simp] theorem contributionCapacityU8RuntimePaymentCurrentAt_exact
    (oldVisit : OldVisit) (index : Nat) :
    contributionCapacityU8RuntimePaymentCurrentAt oldVisit index = index :=
  contributionCapacityU8Visit_current_exact oldVisit index

def contributionCapacityU8RuntimePaymentRootEventAt
    (oldVisit : OldVisit) (index : Nat) :
    ExactTemporalCausalRootEventAt
      (CapacityU8RootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityU8TemporalVisitAt oldVisit index) :=
  (CapacityU8RootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt
      (contributionCapacityU8TemporalVisitAt oldVisit index)

@[simp] theorem contributionCapacityU8RuntimePaymentRootEvent_occurrence_exact
    (oldVisit : OldVisit) (index : Nat) :
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).occurrence =
      contributionCapacityU8Emitted oldVisit
        (contributionCapacityU8RuntimePaymentCurrentAt oldVisit index) :=
  rfl

def contributionCapacityU8RuntimePaymentAt
    (oldVisit : OldVisit) (index : Nat) :
    ContributionCapacityU8ExactWholeLedgerPaymentAt
      (contributionCapacityU8RuntimePaymentCurrentAt oldVisit index) :=
  PLift.up
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).occurrence.2.periodicExitGenerated

def contributionCapacityU8RuntimePaymentRowEvolutionAt
    (oldVisit : OldVisit) (index : Nat) (entryIndex : Fin 3) :=
  (contributionCapacityU8Evolution oldVisit
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).occurrence).destination
      (contributionCapacityU8EntryAt oldVisit entryIndex) |>.2

theorem contributionCapacityU8RuntimePaymentCompiler_nativeWrite_exact
    (oldVisit : OldVisit) (index : Nat) :
    (contributionCapacityU8LedgerCompiler oldVisit).compile
        (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
          ).occurrence =
      .nativeWrite
        (contributionCapacityU8RuntimePaymentAt oldVisit index) rfl
        (contributionCapacityU8Emitted oldVisit
          (contributionCapacityU8RuntimePaymentCurrentAt oldVisit index + 1))
        (contributionCapacityU8Evolution oldVisit
          (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
            ).occurrence) :=
  rfl

theorem contributionCapacityU8RuntimePaymentRootReceipt_nativeWrite_exact
    (oldVisit : OldVisit) (index : Nat) :
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).wholeLedgerWriteBack =
      (contributionCapacityU8LedgerCompiler oldVisit).compile
        (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
          ).occurrence :=
  rfl

theorem contributionCapacityU8RuntimePayment_everyRow_evolved
    (oldVisit : OldVisit) (index : Nat) (entryIndex : Fin 3) :
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityU8EntryAt oldVisit entryIndex) =
      .evolved
        (contributionCapacityU8RuntimePaymentRowEvolutionAt oldVisit index
          entryIndex) := by
  rw [contributionCapacityU8RuntimePaymentRootReceipt_nativeWrite_exact]
  rw [contributionCapacityU8RuntimePaymentCompiler_nativeWrite_exact]
  rfl

def contributionCapacityU8RuntimePaymentSuccessorAt
    (oldVisit : OldVisit) (index : Nat) :
    SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
        ).occurrence
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
        ).wholeLedgerWriteBack :=
  PUnit.unit

/-- Payment carries the event/write/whole-ledger seal but no next or target. -/
structure SourceGeneratedContributionCapacityU8RuntimePaymentAt
    (oldVisit : OldVisit) (index : Nat) : Prop where
  private mk ::
  currentExact :
    contributionCapacityU8RuntimePaymentCurrentAt oldVisit index = index
  paymentWitnessExact :
    contributionCapacityU8RuntimePaymentAt oldVisit index =
      PLift.up
        (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
          ).occurrence.2.periodicExitGenerated
  rootReceiptNativeWriteExact :
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).wholeLedgerWriteBack =
      (contributionCapacityU8LedgerCompiler oldVisit).compile
        (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
          ).occurrence
  compilerNativeWriteExact :
    (contributionCapacityU8LedgerCompiler oldVisit).compile
        (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
          ).occurrence =
      .nativeWrite
        (contributionCapacityU8RuntimePaymentAt oldVisit index) rfl
        (contributionCapacityU8Emitted oldVisit
          (contributionCapacityU8RuntimePaymentCurrentAt oldVisit index + 1))
        (contributionCapacityU8Evolution oldVisit
          (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
            ).occurrence)
  everyRowEvolved : ∀ entryIndex : Fin 3,
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityU8EntryAt oldVisit entryIndex) =
      .evolved
        (contributionCapacityU8RuntimePaymentRowEvolutionAt oldVisit index
          entryIndex)
  successorGenerated : Nonempty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
        ).occurrence
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
        ).wholeLedgerWriteBack)

theorem sourceGeneratedContributionCapacityU8RuntimePaymentAt
    (oldVisit : OldVisit) (index : Nat) :
    SourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit index where
  currentExact :=
    contributionCapacityU8RuntimePaymentCurrentAt_exact oldVisit index
  paymentWitnessExact := rfl
  rootReceiptNativeWriteExact :=
    contributionCapacityU8RuntimePaymentRootReceipt_nativeWrite_exact oldVisit
      index
  compilerNativeWriteExact :=
    contributionCapacityU8RuntimePaymentCompiler_nativeWrite_exact oldVisit
      index
  everyRowEvolved :=
    contributionCapacityU8RuntimePayment_everyRow_evolved oldVisit index
  successorGenerated :=
    ⟨contributionCapacityU8RuntimePaymentSuccessorAt oldVisit index⟩

theorem contributionCapacityU8RuntimePayment_hasNoNextOrTarget
    (oldVisit : OldVisit) (index : Nat) : True := by
  let payment := contributionCapacityU8RuntimePaymentAt oldVisit index
  fail_if_success exact payment.next
  fail_if_success exact payment.target
  fail_if_success exact payment.future
  trivial

end
end M14SourceGeneratedContributionCapacityU8RuntimePayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8RuntimePayment.sourceGeneratedContributionCapacityU8RuntimePaymentAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8RuntimePayment.contributionCapacityU8RuntimePaymentCompiler_nativeWrite_exact
