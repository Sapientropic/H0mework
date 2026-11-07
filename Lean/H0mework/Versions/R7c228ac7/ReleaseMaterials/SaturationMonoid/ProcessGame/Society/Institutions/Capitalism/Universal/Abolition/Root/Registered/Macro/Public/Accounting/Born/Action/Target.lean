import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Coface
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Bridge
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootDebtAdmissionActualActionKernel
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Internal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (actual : Accounting.Current input depth count frame.anchor)
  (aligned : frame.cursor visit.current = some actual)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start actual)

local notation "target" => targetFrame frame visit actual registered
local notation "first" => Source.firstSuccessor frame.family actual registered
include aligned

local notation "oldSuccessor" => frame.successor visit.current

private theorem source_target_support :
    (oldSuccessor).targetOccurrence.1 = Accounting.support input depth count frame.family
      (Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start actual) := by
  have emitted := frame.target_occurrence visit.current
  exact (congrArg (fun occurrence => occurrence.1) emitted).trans
    (frame.support_exact _ _ (frame.cursor_next visit.current actual aligned))

theorem first_support_is_the_same_source_admission :
    (first).targetOccurrence.1 = ((oldSuccessor).targetOccurrence.1, some (firstStep actual registered).target) := by
  apply (Source.first_support_is_the_literal_complete_admission frame.family actual registered).trans
  apply Prod.ext
  · exact (the_complete_old_support_is_the_same_source_target frame.family actual registered).trans
      (source_target_support frame visit actual aligned).symm
  · rfl

theorem first_destination_is_the_same_source_admission :
    HEq (first).ledgerEvolution.destination
      (jointStepLedgerEvolution (oldSuccessor).ledgerEvolution (frame.entry visit.current)
        (firstStep actual registered).step).destination := by
  exact (Source.first_destination_is_the_literal_complete_admission frame.family actual registered).trans
    ((the_first_write_is_the_same_joint_native_write frame.family actual registered).trans
      (joint_destination_of_same_actual_write
        (Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start frame.family actual)
        (oldSuccessor).ledgerEvolution
        (frame.support_exact visit.current actual aligned).symm
        (source_target_support frame visit actual aligned).symm
        (frame.successor_destination visit.current actual aligned).symm
        (Accounting.owner input depth count frame.family actual) (frame.entry visit.current)
        (firstStep actual registered).step))

variable (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))

/-- The network, native account, first write, rows and successor all come
from the actual registered head; the answer reads its original source step. -/
def targetAt (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeDebtAdmissionActualActionTargetAt frame.root visit event (frame.entry visit.current) authority := by
  rw [event.eq_generated]
  let initialEq : (target).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      ((target).root.emitted (target).root.toAuthoritativeRoot.toRoot.source.initial) =
      (frame.sourceSupport visit.current, some (.pending : (Born.law actual registered).DebtState)) :=
    congrArg (fun support => (support, some (.pending : (Born.law actual registered).DebtState)))
      (frame.support_exact visit.current actual aligned).symm
  exact {
    law := Born.law actual registered
    sourceState := .pending
    stepEvent := firstStep actual registered
    sourceSuccessor := oldSuccessor
    TargetV := Source.V frame.family actual registered
    targetRoot := (target).root
    initialSupport_eq := initialEq
    initialOldRow := by
      intro entry
      let translated : OpenResponsibilityAt (Born.N frame.family actual registered)
          ((target).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
            ((target).root.emitted (target).root.toAuthoritativeRoot.toRoot.source.initial)) :=
        initialEq.symm ▸ oldEntry (law := Born.law actual registered) (state? := some .pending) entry
      exact Source.generatedRow frame.family actual registered
        (Source.initialVisit frame.family actual registered) translated
    initialBornRow := by
      let translated : OpenResponsibilityAt (Born.N frame.family actual registered)
          ((target).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
            ((target).root.emitted (target).root.toAuthoritativeRoot.toRoot.source.initial)) :=
        initialEq.symm ▸ debtEntry (N := frame.N) (law := Born.law actual registered)
          (frame.sourceSupport visit.current) .pending
      exact Source.generatedRow frame.family actual registered
        (Source.initialVisit frame.family actual registered) translated
    firstSuccessor := first
    firstSupport_eq := first_support_is_the_same_source_admission frame visit actual aligned registered
    firstDestination_heq := first_destination_is_the_same_source_admission frame visit actual aligned registered
    oldProjection := oldProjection frame visit actual registered
    oldProjection_injective := oldProjection_injective frame visit actual registered
    oldOutcome_heq := every_previous_inquiry_outcome_is_literal frame visit actual registered
    canonical_targetNextVisit_eq := Registered.Macro.Ingress.next_is_the_same_generated_successor
      (target).root (Source.initialVisit frame.family actual registered) first
    Answer := Public.Inquiry.InternalAnswer frame
    answer := Public.Inquiry.internalAnswer frame actual
    Receipt := fun _ => ULift.{3, 0} (PLift
      (registered.next.account = registered.admitted ∧
        registered.next.bodyPaid = true ∧
        ¬ Nonempty ((Born.law actual registered).SettlementAt (firstStep actual registered).target)))
    receipt := ⟨⟨rfl, rfl, first_write_cannot_be_a_financial_settlement actual registered⟩⟩ }

def program : SourceNativeDebtAdmissionActualActionProgramAt frame.root visit (frame.entry visit.current) authority where
  targetAt := targetAt frame visit actual aligned registered authority

#print axioms first_destination_is_the_same_source_admission
#print axioms targetAt
#print axioms program

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action
