import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut.Repayment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut

open Source.Program Institutions.Capitalism.Universal.Root PublicFunction PublicFunction.Mandate
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

noncomputable section

variable {epoch : Epoch}

def ReviewCutFailure (inventory : Inventory epoch) : Prop :=
  ¬ 2 ≤ (oldCut inventory).inputs.length ∨
  ¬ (2 ≤ reviewOrdinal inventory ∧ reviewOrdinal inventory ≤ (oldCut inventory).inputs.length + 1) ∨
  (Handoff.reviewsAt epoch.bound (oldCut inventory).inputs (reviewOrdinal inventory)).head? = none ∨
  ¬ Handoff.Quiet (Handoff.after epoch.bound (oldCut inventory).inputs)

theorem a_failed_selected_cut_names_its_native_reason (inventory : Inventory epoch)
    (absent : choose inventory = none) : ReviewCutFailure inventory := by
  unfold choose Handoff.chooseAt at absent
  split at absent
  · split at absent
    · split at absent
      · split at absent
        · contradiction
        · exact Or.inr (Or.inr (Or.inr (by assumption)))
      · exact Or.inr (Or.inr (Or.inl (by assumption)))
    · exact Or.inr (Or.inl (by assumption))
  · exact Or.inl (by assumption)

def refusedReviewCut (inventory : Inventory epoch) : Inventory epoch :=
  if World.reviewWord inventory = [] then inventory else World.staged inventory

def refusedReviewPath (inventory : Inventory epoch) :
    Input.Event.Evolution ⟨epoch, inventory⟩ ⟨epoch, refusedReviewCut inventory⟩ := by
  unfold refusedReviewCut
  split
  · exact .same _
  · exact .submit inventory (World.reviewWord inventory)

abbrev Drafts (inventory : Inventory epoch) :=
  Handoff.Ready epoch.bound (oldCut inventory).inputs → Install.Words

structure Installed (inventory : Inventory epoch) (draft : Drafts inventory) where
  payment : ReviewPaid inventory
  reviewed : World.chooseReview inventory = some payment
  repayment : CheckedRepayment inventory
  fresh : Handoff.Ready epoch.bound (oldCut inventory).inputs
  chosen : choose inventory = some fresh
  opening : Install.DraftPaid (oldCut inventory) fresh (draft fresh)

inductive Outcome (inventory : Inventory epoch) (draft : Drafts inventory) where
  | reviewBlocked (absent : World.chooseReview inventory = none) (reason : ReviewOutcome inventory)
  | repaymentBlocked (reason : RepaymentIssue inventory)
  | cutBlocked (absent : choose inventory = none) (reason : ReviewCutFailure inventory)
  | draftBlocked (fresh : Handoff.Ready epoch.bound (oldCut inventory).inputs)
      (chosen : choose inventory = some fresh) (reason : Install.DraftFailure (oldCut inventory) fresh (draft fresh))
  | installed (checked : Installed inventory draft)

def produce (inventory : Inventory epoch) (draft : Drafts inventory) : Outcome inventory draft :=
  match review : World.chooseReview inventory with
  | none => .reviewBlocked review (World.reviewOutcome inventory)
  | some payment =>
    match inspectRepayment inventory with
    | .blocked reason => .repaymentBlocked reason
    | .paid repayment =>
      match selected : choose inventory with
      | none => .cutBlocked selected (a_failed_selected_cut_names_its_native_reason inventory selected)
      | some fresh =>
        match Install.checkDraft (oldCut inventory) fresh (draft fresh) with
        | .blocked reason => .draftBlocked fresh selected reason
        | .paid opening => .installed ⟨payment, review, repayment, fresh, selected, opening⟩

def nativeDraft (inventory : Inventory epoch) : Drafts inventory := fun fresh =>
  let payment := Handoff.responseWord fresh
  if payment = [] then [Handoff.firstWord fresh] else Handoff.epochInputs fresh

variable {inventory : Inventory epoch} {draft : Drafts inventory}

def Installed.packet (installed : Installed inventory draft) : Packet :=
  ⟨Epoch.ofFresh installed.fresh, World.handoffAt (oldCut inventory) installed.fresh (draft installed.fresh)⟩

def Outcome.packet : Outcome inventory draft → Packet
  | .reviewBlocked .. => ⟨epoch, refusedReviewCut inventory⟩
  | .repaymentBlocked .. | .cutBlocked .. | .draftBlocked .. => ⟨epoch, oldCut inventory⟩
  | .installed checked => checked.packet

def Outcome.evolution (result : Outcome inventory draft) :
    Input.Event.Evolution ⟨epoch, inventory⟩ result.packet :=
  match result with
  | .reviewBlocked .. => refusedReviewPath inventory
  | .repaymentBlocked .. | .cutBlocked .. | .draftBlocked .. => oldRoute inventory
  | .installed checked =>
    .append (oldRoute inventory) (.handoffAt (oldCut inventory) checked.fresh (draft checked.fresh))

def Outcome.isInstalled : Outcome inventory draft → Bool
  | .installed _ => true
  | _ => false

theorem producer_installs_iff_actual_review_settlement_and_draft_are_paid :
    (produce inventory draft).isInstalled = true ↔ Nonempty (Installed inventory draft) := by
  cases produce inventory draft with
  | installed checked => exact ⟨fun _ => ⟨checked⟩, fun _ => rfl⟩
  | reviewBlocked absent _ =>
    refine ⟨fun check => Bool.noConfusion check, ?_⟩
    rintro ⟨paid⟩
    cases absent.symm.trans paid.reviewed
  | repaymentBlocked reason =>
    exact ⟨fun check => Bool.noConfusion check, fun ⟨paid⟩ => (reason.rules_out inventory paid.repayment).elim⟩
  | cutBlocked absent _ =>
    refine ⟨fun check => Bool.noConfusion check, ?_⟩
    rintro ⟨paid⟩
    cases absent.symm.trans paid.chosen
  | draftBlocked fresh chosen reason =>
    refine ⟨fun check => Bool.noConfusion check, ?_⟩
    rintro ⟨paid⟩
    have same := Option.some.inj (chosen.symm.trans paid.chosen)
    exact (reason.refutes ((congrArg (fun next => Install.DraftPaid (oldCut inventory) next (draft next)) same.symm).mp paid.opening)).elim

theorem Installed.no_extra_period_iff_original_balances_clear (_installed : Installed inventory draft) :
    (repaymentSuffix inventory).length = 0 ↔ originalBalancesClear inventory :=
  extra_periods_are_zero_iff_original_balances_clear inventory

theorem Installed.original_service_is_in_the_new_native_census (installed : Installed inventory draft)
    (slot : epoch.source.Slot) :
    (World.openingCurrentService (oldCut inventory) installed.fresh (draft installed.fresh) slot) ∈
      installed.packet.2.pastServices := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨slot, List.mem_finRange _, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut
