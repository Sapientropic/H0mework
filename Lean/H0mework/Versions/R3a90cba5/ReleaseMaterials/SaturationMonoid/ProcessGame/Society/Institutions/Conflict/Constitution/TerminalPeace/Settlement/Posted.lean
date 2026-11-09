import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Writer
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation Reparation.Actual
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open private PostedPosition.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.CoSigned.Posted

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (anchor : Script Party Good Port Technology Instrument)
  (visit : Installation.Core.Landed seed community (endAt seed anchor)
    (PostedMaterial Party Good Port Technology Instrument))
  (ordered : anchor.length ≤ visit.read.ordinal)
  (accepted : visit.read.effect.isAccepted = true)
  (position : Fin visit.read.effect.execution.items.length)

/-- Only a root-landed material read can supply the new input to the
original allocator. The original history still orders the old rows. -/
def postedPosition : PostedPosition seed :=
  PostedPosition.mk anchor visit.read ordered
    ⟨visit.state.world, visit.state.resident, visit.material, visit.materialType, rfl⟩
    accepted position

variable (site : PostedPosition seed)

def postedOffer (key : Key Party Good) : Option (JointReceipt seed key) :=
  if signed : site.material.deliveryReplies key.2.1 = true ∧ site.material.deliveryReplies key.1 = true ∧
      0 < payerCredit site.material.programme.law site.item key then
    some (.posted site signed.1 signed.2.1 signed.2.2)
  else none

theorem posted_offer_is_at_its_actual_position (key : Key Party Good) (receipt : JointReceipt seed key)
    (issued : postedOffer site key = some receipt) :
    ∃ (payer : site.material.deliveryReplies key.2.1 = true) (victim : site.material.deliveryReplies key.1 = true)
      (positive : 0 < payerCredit site.material.programme.law site.item key),
      receipt = .posted site payer victim positive := by
  unfold postedOffer at issued
  split at issued
  · rename_i signed
    exact ⟨signed.1, signed.2.1, signed.2.2, (Option.some.inj issued).symm⟩
  · cases issued

theorem posted_offer_reads_both_actual_replies (key : Key Party Good) (receipt : JointReceipt seed key)
    (issued : postedOffer site key = some receipt) :
    receipt.address = site.address ∧ receipt.item = site.item ∧
      receipt.law = site.material.programme.law ∧ site.material.deliveryReplies key.2.1 = true ∧ site.material.deliveryReplies key.1 = true := by
  obtain ⟨payer, victim, _, rfl⟩ := posted_offer_is_at_its_actual_position site key receipt issued
  exact ⟨rfl, rfl, rfl, payer, victim⟩

theorem a_posted_receipt_cannot_be_reused_at_another_ordinal (key : Key Party Good)
    (receipt : JointReceipt seed key) (issued : postedOffer site key = some receipt)
    (other : PostedPosition seed)
    (later : site.material.ordinal < other.material.ordinal) :
    postedOffer other key ≠ some receipt := by
  intro replay
  have first := (posted_offer_reads_both_actual_replies site key receipt issued).1
  have second := (posted_offer_reads_both_actual_replies other key receipt replay).1
  exact (ne_of_lt later) (congrArg Prod.fst (first.symm.trans second))

theorem posted_limit_eq_quantity (key : Key Party Good) (receipt : JointReceipt seed key)
    (issued : postedOffer site key = some receipt) :
    deliveryLimit site.material.programme.law site.item key.2.2 = receipt.quantity := by
  obtain ⟨_, _, positive, rfl⟩ := posted_offer_is_at_its_actual_position site key receipt issued
  exact deliveryLimit_eq_credit _ _ _ positive

section Writer

local notation "Site" => postedPosition anchor visit ordered accepted position
local notation "OfferAt" => postedOffer Site
local notation "Limit" => deliveryLimit visit.read.programme.law (PostedPosition.item Site)

def allocatePosted :=
  allocate OfferAt Limit
    (fun key receipt issued => (posted_limit_eq_quantity Site key receipt issued).le)
    visit.state.stack (Available.full (deliveryLimit_nonnegative _ _))

local notation "Plan" => allocatePosted anchor visit ordered accepted position

/-- Only the original whole state of this physical posting may consume
its delivery. No later resident or second stack is passed to the writer. -/
def consumePosted :=
  visit.state.consumeMotion (Plan).move true

local notation "Next" => consumePosted anchor visit ordered accepted position

theorem consumePosted_exact (good : Good) :
    outstanding good (Next).stack.balances + min (Limit good)
        (demand OfferAt good visit.state.stack.balances) =
        outstanding good visit.state.stack.balances := by
  rw [consumePosted, StateAt.consumeMotion_balances]
  have conservation := (Plan).conservation good
  have tight := (Plan).tight good
  change _ - _ = min (Limit good) (demand OfferAt good visit.state.stack.balances) at tight
  rw [← tight]
  exact conservation

theorem consumePosted_keeps_the_original_addresses :
    (Next).stack.balances.map Prod.fst = visit.state.stack.balances.map Prod.fst := by
  rw [consumePosted, StateAt.consumeMotion_balances]
  exact (Plan).move.keeps_origins

theorem consumePosted_is_the_whole_successor :
    (⟨visit.state.world, ((visit.state.moveFirst (Plan).move true).sequential visit.state.resident
      visit.state.exactSupport.symm).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      (Next).resident.erase :=
  visit.state.the_motion_is_the_original_visit_write _ _

theorem consumePosted_retains_the_original_material_read
    (projection : visit.state.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (Next).resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.component projection)
      (arrived.root.emitted arrived.visit.current))
      (visit.state.resident.root.source.base.projectionLaw.outcomeAt projection
        (visit.state.resident.root.emitted visit.state.resident.visit.current)) := by
  let before := visit.state.resident
  let first := visit.state.moveFirst (Plan).move true
  let ledger := Compiler.ledgerSource first.flow
  let freeze := first.inherit before
  let installed := SourceNativeProjectionLaw.InstallationAt.componentCoface
    (Compiler.livingRoot first.flow).source.base freeze
  let occurrence := Compiler.emitted first.flow (Next).resident.visit.current
  exact (installed.outcome_heq occurrence projection).trans
    (QueryHistory.every_frozen_outcome_is_the_same_original_dependent_outcome
      before.root.source.base.projectionLaw (before.root.emitted before.visit.current) ledger occurrence projection)

end Writer

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement
