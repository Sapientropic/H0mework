import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Inquiry
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Origin
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootDebtAdmissionActualActionKernel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (origin : Source.OriginAt input frame visit claim)
  (word : RawEvent Party Good Port Technology Instrument)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (Source.sourceEntry input frame visit))

local notation "F" => Source.flow input frame visit claim word
local notation "newRoot" => Source.Inquiry.root input frame visit claim word
local notation "initial" => Compiler.initialVisit F
local notation "first" => Compiler.successor F Source.Phase.pending

def targetAt (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeDebtAdmissionActualActionTargetAt frame.root visit event (Source.sourceEntry input frame visit) authority := by
  rw [event.eq_generated]
  exact {
    law := Responsibility.Family.activationLaw claim
    sourceState := Source.initialState input frame visit claim
    stepEvent := Source.firstStep input frame visit claim
    sourceSuccessor := Source.sourceSuccessor input frame visit
    TargetV := Source.V input frame visit claim word
    targetRoot := newRoot
    initialSupport_eq := rfl
    initialOldRow := fun entry => Compiler.generatedRow F initial
      (oldEntry (law := Responsibility.Family.activationLaw claim)
        (state? := some (Source.initialState input frame visit claim)) entry)
    initialBornRow := Compiler.generatedRow F initial
      (debtEntry (N := frame.N) (law := Responsibility.Family.activationLaw claim)
        (Source.sourceSupport input frame visit) (Source.initialState input frame visit claim))
    firstSuccessor := first
    firstSupport_eq := Compiler.successor_support F Source.Phase.pending
    firstDestination_heq := Compiler.successor_destination F Source.Phase.pending
    oldProjection := Source.Inquiry.oldProjection input frame visit claim word
    oldProjection_injective := Source.Inquiry.oldProjection_injective input frame visit claim word
    oldOutcome_heq := Source.Inquiry.oldOutcome input frame visit claim word
    canonical_targetNextVisit_eq :=
      Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor newRoot initial first
    Answer := Responsibility.Family.State claim
    answer := Source.declared input frame visit claim
    Receipt := fun answer => ULift.{3,0} (PLift
      ((Control.responseExecution mechanism past nature response).items =
        input.law.rawItems (ProgrammeSource.rawCurrent input (Source.originalVisit input frame visit).current)
          (ProgrammeSource.rawEvent input (Source.originalVisit input frame visit).current) ∧
       (∀ before after person good, Source.OriginalFourComponents input frame visit before after person good) ∧
       answer.remaining = (Source.initialState input frame visit claim).remaining ∧
        answer.raw = (Source.initialState input frame visit claim).raw ∧
        ¬ Nonempty ((Responsibility.Family.activationLaw claim).SettlementAt answer)))
    receipt := ⟨⟨Source.the_assessed_inventory_is_the_literal_original_execution input frame visit claim origin,
      Source.the_same_original_profit_read_has_all_four_components input frame visit,rfl,rfl,by
      rintro ⟨settled⟩
      have unpaid := Responsibility.Family.State.atCursor_is_unpaid claim
        (Source.initialState input frame visit claim).raw
      exact unpaid settled.paid⟩⟩ }

def program : SourceNativeDebtAdmissionActualActionProgramAt frame.root visit
    (Source.sourceEntry input frame visit) authority where
  targetAt := targetAt input frame visit claim origin word authority

def generated := (program input frame visit claim origin word authority).generate
  (frame.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit)

theorem liability_admission_is_the_actual_same_root_next :
    (generated input frame visit claim origin word authority).target.targetAnswerAndNext.nextCurrent =
      ⟨Source.V input frame visit claim word,(newRoot).toAuthoritativeRoot,
        (initial).next (first).next_eq⟩ :=
  (generated input frame visit claim origin word authority).target.targetAnswerAndNext_next_eq

theorem no_original_row_can_be_deleted_by_admitting_the_control_obligation
    (entry : OpenResponsibilityAt frame.N (Source.sourceSupport input frame visit)) :
    ((Source.evolution input frame visit claim word .pending).destination
      (oldEntry (law := Responsibility.Family.activationLaw claim)
        (state? := some (Source.initialState input frame visit claim)) entry)).1 =
      oldEntry (law := Responsibility.Family.activationLaw claim) (state? := some (Source.declared input frame visit claim))
        ((Source.sourceSuccessor input frame visit).ledgerEvolution.destination entry).1 := rfl

#print axioms targetAt
#print axioms liability_admission_is_the_actual_same_root_next

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action
