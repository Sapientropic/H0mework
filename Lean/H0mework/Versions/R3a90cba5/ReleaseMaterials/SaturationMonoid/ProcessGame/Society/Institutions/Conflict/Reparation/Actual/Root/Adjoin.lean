import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Compile
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Finiteness

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Draft

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open Capitalism.Universal.Abolition.Root.Epoch.Finance.Future
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite
open Transport

noncomputable section

variable {N : WorldRelationNetwork} {law : DebtActivationLaw} {before : law.DebtState}
  (draft : Draft N) (activation : SourceFixedDebtAdmissionEventAt law before)

def joined : First (ExtendedNetwork N law) where
  before := (draft.resident.support, some before)
  after := (draft.afterSupport, some activation.target)
  whole := Whole.jointStep draft.whole draft.resident.entry activation.step
  beforeFinite := Finiteness.active_finite before draft.beforeFinite
  afterFinite := Finiteness.active_finite activation.target draft.afterFinite
  openFibres := Structure.extended_subsingleton law draft.openFibres
  writes := true

local notation "joining" => Draft.joined draft activation
local notation "coface" => First.inherit joining draft.resident
local notation "newRoot" => First.rooted joining coface

abbrev inheritedEntry := oldEntry (law := law) (state? := some before) draft.resident.entry

set_option maxHeartbeats 1200000 in
/-- Attach a native debt coordinate to the selected source's first write.
Repeated attachments refine this one write before its target is entered. -/
def targetAt (event : ExactTemporalCausalRootEventAt
    draft.resident.root.toAuthoritativeRoot.toLedgerRoot draft.resident.visit) :
    SourceNativeDebtAdmissionActualActionTargetAt draft.resident.root draft.resident.visit event
      draft.resident.entry draft.resident.authority := by
  rw [event.eq_generated]
  exact {
    law := law
    sourceState := before
    stepEvent := activation
    sourceSuccessor := draft.write
    TargetV := Compiler.V (joining).flow
    targetRoot := newRoot
    initialSupport_eq := rfl
    initialOldRow := fun row => Compiler.generatedRow (joining).flow (joining).initial
      (oldEntry (law := law) (state? := some before) row)
    initialBornRow := Compiler.generatedRow (joining).flow (joining).initial (debtEntry draft.resident.support before)
    firstSuccessor := (joining).successor
    firstSupport_eq := (joining).first_support
    firstDestination_heq := (joining).first_destination
    oldProjection := fun p => .component p
    oldProjection_injective := by intro left right same; injection same
    oldOutcome_heq := by
      intro p
      let base := Compiler.livingRoot (joining).flow
      have toCoface := (SourceNativeProjectionLaw.InstallationAt.componentCoface
        base.source.base coface).outcome_heq (base.emitted false) p
      exact toCoface.trans (QueryHistory.every_frozen_outcome_is_the_same_original_dependent_outcome
        draft.resident.root.source.base.projectionLaw (draft.resident.root.emitted draft.resident.visit.current)
        (Compiler.ledgerSource (joining).flow) (base.emitted false) p)
    canonical_targetNextVisit_eq :=
      Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
        newRoot (joining).initial (joining).successor
    Answer := law.DebtClaim
    answer := law.debtClaim
    Receipt := fun claim => ULift.{3, 0} (PLift (claim = law.debtClaim))
    receipt := ⟨⟨rfl⟩⟩ }

def program : SourceNativeDebtAdmissionActualActionProgramAt
    draft.resident.root draft.resident.visit draft.resident.entry draft.resident.authority where
  targetAt := targetAt draft activation

def generated := (program draft activation).generate draft.resident.event

def extended : Draft (ExtendedNetwork N law) := (joining).draft coface (inheritedEntry draft (before := before))

def landed : Resident (ExtendedNetwork N law) := (joining).landed coface (inheritedEntry draft (before := before))

theorem the_joint_write_generates_its_own_successor :
    (⟨ExtendedNetwork N law, (generated draft activation).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (landed draft activation).erase :=
  congrArg (fun next => (⟨ExtendedNetwork N law, next⟩ : AnyAuthoritativeRootCurrent))
    (generated draft activation).target.targetAnswerAndNext_next_eq

theorem the_joint_first_support_is_the_original_successor_with_the_new_row :
    (extended draft activation).afterSupport = (draft.afterSupport, some activation.target) :=
  (joining).first_support

def bornAtLanding : OpenResponsibilityAt (ExtendedNetwork N law) (landed draft activation).support :=
  (newRoot).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (joining).successor.next_eq
    (generated draft activation).target.bornEntry

def bornAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (landed draft activation).root
    (landed draft activation).visit (bornAtLanding draft activation) :=
  (generated draft activation).target.bornAuthority.next (joining).successor.next_eq

theorem the_born_row_at_the_successor_is_the_original_claim :
    HEq (bornAtLanding draft activation) (debtEntry (N := N) draft.afterSupport activation.target) := by
  let seed := (generated draft activation).target.bornEntry
  have actual := Compiler.canonical_destination_heq (newRoot).toAuthoritativeRoot.toLedgerRoot
    _ _ (joining).successor.next_eq (joining).successor seed
  exact actual.trans (destination_congr rfl (joining).first_support (joining).successor.ledgerEvolution
    (joining).whole.val (joining).first_destination seed (debtEntry draft.resident.support before) HEq.rfl)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Draft
