import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.CrossingDebt
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Review.Decision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution

open Capitalism.Universal.Source.Program
open PublicFunction.Mandate
open Reparation (continuationItems continuation_requests)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

theorem a_tail_without_delivery_cannot_discharge_any_original_debt
    (source : C) (attack past next : Word) (community : Party → Community)
    (key : Reparation.Key Party Good)
    (noDelivery : ∀ request ∈ next, ∀ debtor victim goods,
      request.operation ≠ .transfer debtor victim goods) :
    Reparation.remaining source attack (past ++ next) community key =
      Reparation.remaining source attack past community key := by
  let law := source.native.input.law
  have prefixItems : Reparation.occurred source (attack ++ past) <+:
      Reparation.occurred source (attack ++ (past ++ next)) := by
    rw [← List.append_assoc]
    change (law.execute source.raw 0 (attack ++ past)).items <+:
      (law.execute source.raw 0 ((attack ++ past) ++ next)).items
    rw [law.execute_append source.raw 0 (attack ++ past) next]
    exact ⟨_, rfl⟩
  have follows := prefixItems.drop attack.length
  change continuationItems source attack past <+: continuationItems source attack (past ++ next) at follows
  obtain ⟨extra, exactItems⟩ := follows
  have requests := congrArg (List.map ExecutionItem.request) exactItems
  simp only [List.map_append, continuation_requests, List.append_cancel_left_eq] at requests
  have zero : (extra.map (fun item => Reparation.receiptCredit law item key)).sum = 0 := by
    apply List.sum_eq_zero
    rintro amount listed
    obtain ⟨item, present, rfl⟩ := List.mem_map.mp listed
    have inTail : item.request ∈ next := by
      rw [← requests]
      exact List.mem_map_of_mem present
    unfold Reparation.receiptCredit
    split
    · cases operation : item.request.operation
      case transfer payer payee goods => exact (noDelivery item.request inTail payer payee goods operation).elim
      all_goals rfl
    · rfl
  unfold Reparation.remaining Reparation.received
  rw [← exactItems, List.map_append, List.sum_append, zero, add_zero]

variable [DecidableEq Technology]

/-- The same paid raw and native review may contain the victim's signature
as a reviewer. Only a new original delivery can discharge the loss. -/
theorem dual_review_never_consumes_a_cross_community_reparation
    {source : Root.Cut Party Good Port (State Party Technology) Instrument}
    {attack past tail : RawEvent Party Good Port (State Party Technology) Instrument}
    {community : Party → Community}
    {base : RawLaw Party Good Port Technology Instrument}
    {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
    {first second : Party} {good : Good}
    (invasion : Boundary.AggressionAt source attack community)
    (review : Emergency.ReviewPaid base scope (Root.terminal source (attack ++ past)) first second good tail) :
    let cut := Root.terminal source (attack ++ past)
    let reviews := Emergency.reviewWord base scope cut first second tail
    Reparation.remaining source attack (past ++ reviews) community (debtAddress invasion) =
      Reparation.remaining source attack past community (debtAddress invasion) := by
  exact a_tail_without_delivery_cannot_discharge_any_original_debt _ _ _ _ _ _
    (Emergency.review_word_has_no_transfer base scope _ first second review.localTail)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution
