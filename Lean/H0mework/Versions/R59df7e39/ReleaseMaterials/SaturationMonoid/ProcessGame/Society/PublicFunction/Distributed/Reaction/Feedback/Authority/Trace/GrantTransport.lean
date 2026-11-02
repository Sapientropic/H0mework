import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Grant

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Mandate.Lifecycle.Observed

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
  {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {currentAt otherCurrent : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument}
  {wordAt otherWord : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
  {birth : Nat} {grant : Mandate.Grant base scope (currentAt birth) (wordAt birth)}
  {otherGrant : Mandate.Grant base scope (otherCurrent birth) (otherWord birth)}

theorem grant_consume_images_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (old : Mandate.Lifecycle.Observed.History base scope currentAt wordAt birth grant)
    (new : Mandate.Lifecycle.Observed.History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state) (sameTrace : grantHistoryImage code new = grantHistoryImage code old)
    (visit : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit)
    (oldItem : {item // item ∈ (Mandate.law base scope).rawItems (currentAt visit) (wordAt visit)})
    (newItem : {item // item ∈ (Mandate.law base scope).rawItems (otherCurrent visit) (otherWord visit)})
    (sameItem : newItem.val = oldItem.val) :
    grantHistoryImage code (new.consume visit newItem) = grantHistoryImage code (old.consume visit oldItem) := by
  have sameObligation := Mandate.Lifecycle.Observed.History.obligation_eq_of_state_eq old new sameState
  rcases old with ⟨oldObligation, oldOrigin, oldState, oldSlots, oldRun⟩
  rcases new with ⟨newObligation, newOrigin, newState, newSlots, newRun⟩
  dsimp only at sameState sameObligation
  subst newState
  subst newObligation
  have images := grant_read_images_congr code sameIndex oldObligation oldOrigin newOrigin visit 0
    sameCurrent sameWord oldItem newItem sameItem
  unfold Mandate.Lifecycle.Observed.History.consume
  cases oldRead : readEvent oldObligation oldOrigin visit oldItem <;>
    cases newRead : readEvent oldObligation newOrigin visit newItem <;>
    simp only [oldRead, newRead, Option.map_none, Option.map_some] at images
  · exact sameTrace
  · cases images
  · cases images
  · dsimp only [grantHistoryImage, Mandate.Lifecycle.Observed.History.cross, Mandate.Lifecycle.Observed.History.edge, grantRunImage]
    exact congrArg₂ List.append sameTrace (congrArg (fun record => [record]) (Option.some.inj images))

private theorem grant_consume_many_images_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (visit : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit)
    (items : List {item // item ∈ (Mandate.law base scope).rawItems (currentAt visit) (wordAt visit)})
    (old : Mandate.Lifecycle.Observed.History base scope currentAt wordAt birth grant)
    (new : Mandate.Lifecycle.Observed.History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state) (sameTrace : grantHistoryImage code new = grantHistoryImage code old) :
    grantHistoryImage code ((items.map (reindexItem sameCurrent sameWord)).foldl (fun history item => history.consume visit item) new) =
      grantHistoryImage code (items.foldl (fun history item => history.consume visit item) old) := by
  induction items generalizing old new with
  | nil => exact sameTrace
  | cons item rest ih =>
    exact ih (old.consume visit item) (new.consume visit (reindexItem sameCurrent sameWord item))
      (Mandate.Lifecycle.Observed.History.consume_state_congr sameIndex old new sameState visit sameCurrent sameWord item _ rfl)
      (grant_consume_images_congr code sameIndex old new sameState sameTrace visit sameCurrent sameWord item _ rfl)

private theorem attach_grant_reindex
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord) :
    ((Mandate.law base scope).rawItems second secondWord).attach =
      ((Mandate.law base scope).rawItems first firstWord).attach.map (reindexItem sameCurrent sameWord) := by
  cases sameCurrent; cases sameWord
  change _ = List.map id _
  exact (List.map_id _).symm

theorem grant_visit_images_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (old : Mandate.Lifecycle.Observed.History base scope currentAt wordAt birth grant)
    (new : Mandate.Lifecycle.Observed.History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state) (sameTrace : grantHistoryImage code new = grantHistoryImage code old)
    (visit : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit) :
    grantHistoryImage code (new.visit visit) = grantHistoryImage code (old.visit visit) := by
  unfold Mandate.Lifecycle.Observed.History.visit
  rw [attach_grant_reindex sameCurrent sameWord]
  exact grant_consume_many_images_congr code sameIndex visit sameCurrent sameWord _ old new sameState sameTrace

private theorem grant_visits_images_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (visits : List Nat) (sameCurrent : ∀ visit ∈ visits, otherCurrent visit = currentAt visit)
    (sameWord : ∀ visit ∈ visits, otherWord visit = wordAt visit)
    (old : Mandate.Lifecycle.Observed.History base scope currentAt wordAt birth grant)
    (new : Mandate.Lifecycle.Observed.History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state) (sameTrace : grantHistoryImage code new = grantHistoryImage code old) :
    grantHistoryImage code (visits.foldl (fun history visit => history.visit visit) new) =
      grantHistoryImage code (visits.foldl (fun history visit => history.visit visit) old) := by
  induction visits generalizing old new with
  | nil => exact sameTrace
  | cons visit rest ih =>
    exact ih (fun later member => sameCurrent later (List.mem_cons_of_mem _ member))
      (fun later member => sameWord later (List.mem_cons_of_mem _ member)) (old.visit visit) (new.visit visit)
      (Mandate.Lifecycle.Observed.History.visit_state_congr sameIndex old new sameState visit (sameCurrent visit List.mem_cons_self) (sameWord visit List.mem_cons_self))
      (grant_visit_images_congr code sameIndex old new sameState sameTrace visit
        (sameCurrent visit List.mem_cons_self) (sameWord visit List.mem_cons_self))

theorem grant_through_images_congr (last : Nat)
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (sameInitial : initialState base scope otherCurrent otherWord birth otherGrant = initialState base scope currentAt wordAt birth grant)
    (sameCurrent : ∀ visit ≤ last, otherCurrent visit = currentAt visit)
    (sameWord : ∀ visit ≤ last, otherWord visit = wordAt visit) :
    grantHistoryImage code (through (base := base) (scope := scope) (currentAt := otherCurrent) (wordAt := otherWord)
      (birth := birth) (grant := otherGrant) last) =
      grantHistoryImage code (through (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt)
        (birth := birth) (grant := grant) last) :=
  grant_visits_images_congr code sameIndex (List.range (last + 1))
    (fun visit member => sameCurrent visit (Nat.le_of_lt_succ (List.mem_range.mp member)))
    (fun visit member => sameWord visit (Nat.le_of_lt_succ (List.mem_range.mp member)))
    initial initial sameInitial rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
