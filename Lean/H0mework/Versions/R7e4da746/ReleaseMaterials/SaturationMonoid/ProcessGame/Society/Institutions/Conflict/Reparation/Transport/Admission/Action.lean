import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Admission.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Admission

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

variable {law : DebtActivationLaw} {joint : WorldRelationNetwork}
  {native : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {shape : Shape law native.frame.N joint} {phase : law.DebtState} {wait : law.TransportAt phase phase}
  (current : Resident shape phase wait) (registered : Registration native)
  (work : Public.Inquiry.HasWork native.frame native.actual.actual)

local notation "candidate" => frame current registered
local notation "newRoot" => Frame.rooted (frame current registered) wait
  (Frame.inherit current (frame current registered) wait)
local notation "newWorld" => ExtendedNetwork joint (finance registered)

def landed : Resident (native := nextNative registered) (nextShape (shape := shape) registered) phase wait :=
  (candidate).resident wait (Frame.inherit current (candidate) wait)
    (firstOwner current registered) (firstOwner_lands_on_repair current registered)

private theorem joint_support_exact :
    ((candidate).first wait).targetOccurrence.1 =
      ((current.structural work).val.targetOccurrence.1, some (financialStep registered).target) := by
  refine (Compiler.successor_support ((candidate).flow wait) none).trans ?_
  exact (joined_support (shape := shape) (phase := phase) registered).symm.trans
    (congrArg (fun s => (s, some (financialStep registered).target))
      (current.structural work).property.1.symm)

private theorem joint_destination_exact :
    HEq ((candidate).first wait).ledgerEvolution.destination
      (jointStepLedgerEvolution (current.structural work).val.ledgerEvolution current.entry
        (financialStep registered).step).destination := by
  refine (Compiler.successor_destination ((candidate).flow wait) none).trans ?_
  refine (Whole.rebase_destination _ _ (joined current registered)).trans ?_
  exact Public.Accounting.Born.joint_destination_of_same_actual_write
    (held current).val (current.structural work).val.ledgerEvolution current.support_eq.symm
    (current.structural work).property.1.symm (current.structural work).property.2.symm
    (shape.repair (sourceSupport native) phase) current.entry (financialStep registered).step

set_option maxHeartbeats 1000000 in
def targetAt (event : ExactTemporalCausalRootEventAt
    current.root.toAuthoritativeRoot.toLedgerRoot current.visit) :
    SourceNativeDebtAdmissionActualActionTargetAt current.root current.visit event current.entry current.authority := by
  rw [event.eq_generated]
  exact {
    law := finance registered
    sourceState := pending registered
    stepEvent := financialStep registered
    sourceSuccessor := (current.structural work).val
    TargetV := Compiler.V ((candidate).flow wait)
    targetRoot := newRoot
    initialSupport_eq := rfl
    initialOldRow := fun entry => Compiler.generatedRow ((candidate).flow wait) ((candidate).initial wait)
      (oldEntry (law := finance registered) (state? := some (pending registered)) entry)
    initialBornRow := Compiler.generatedRow ((candidate).flow wait) ((candidate).initial wait)
      (debtEntry current.support (pending registered))
    firstSuccessor := (candidate).first wait
    firstSupport_eq := joint_support_exact current registered work
    firstDestination_heq := joint_destination_exact current registered work
    oldProjection := fun projection => .component projection
    oldProjection_injective := by intro left right same; injection same
    oldOutcome_heq := by
      intro projection
      let base := Compiler.livingRoot ((candidate).flow wait)
      let inherited := Frame.inherit current (candidate) wait
      have atInitial := (SourceNativeProjectionLaw.InstallationAt.componentCoface
        base.source.base inherited).outcome_heq (base.emitted none) projection
      have same := QueryHistory.every_frozen_outcome_is_the_same_original_dependent_outcome
        current.root.source.base.projectionLaw (current.root.emitted current.visit.current)
        (Compiler.ledgerSource ((candidate).flow wait)) (base.emitted none) projection
      exact atInitial.trans same
    canonical_targetNextVisit_eq :=
      Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
        (newRoot) ((candidate).initial wait) ((candidate).first wait)
    Answer := Public.Inquiry.InternalAnswer native.full
    answer := Public.Inquiry.internalAnswer native.full native.actual.actual
    Receipt := fun _ => ULift.{3,0} (PLift
      (registered.next.account = registered.admitted ∧
        registered.next.bodyPaid = true ∧
        ¬ Nonempty ((finance registered).SettlementAt (financialStep registered).target)))
    receipt := ⟨⟨rfl, rfl,
      Public.Accounting.Born.first_write_cannot_be_a_financial_settlement native.actual.actual registered⟩⟩ }

def program : SourceNativeDebtAdmissionActualActionProgramAt current.root current.visit current.entry current.authority where
  targetAt := targetAt current registered work

def generated := (program current registered work).generate
  (current.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt current.visit)

theorem actual_admission_generates_the_next_resident :
    (⟨newWorld, (generated current registered work).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (landed current registered).erase :=
  congrArg (fun visit => (⟨newWorld, visit⟩ : AnyAuthoritativeRootCurrent))
    (generated current registered work).target.targetAnswerAndNext_next_eq

theorem the_birth_write_keeps_every_existing_row
    (entry : OpenResponsibilityAt joint current.support) :
    let source := oldEntry (law := finance registered) (state? := some (pending registered)) entry
    let written := (candidate).initialWrite.val.destination source
    written.1.1 = .inl entry.1 ∧ written.1.claim = .inl entry.claim ∧
      written.1.progressBudget ≤ entry.progressBudget :=
  ⟨(candidate).initialWrite.property.1 _,
    ((candidate).initialWrite.val.destination _).2.toDebtLineage.claim_eq.symm,
    ((candidate).initialWrite.val.destination _).2.progressBudget_not_refilled⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Admission
