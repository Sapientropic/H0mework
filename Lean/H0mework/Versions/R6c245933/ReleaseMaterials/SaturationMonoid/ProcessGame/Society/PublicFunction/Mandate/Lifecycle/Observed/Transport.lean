import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Local

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {currentAt otherCurrent : Nat → RawCurrent Party Good (State Party Technology) Instrument}
  {wordAt otherWord : Nat → RawEvent Party Good Port (State Party Technology) Instrument}
  {birth : Nat}
  {grant : Grant base scope (currentAt birth) (wordAt birth)}
  {otherGrant : Grant base scope (otherCurrent birth) (otherWord birth)}


theorem History.obligation_eq_of_state_eq
    (old : History base scope currentAt wordAt birth grant)
    (new : History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state) : new.obligation = old.obligation := by
  have slots := congrArg ResponsibilityState.slots sameState
  rw [new.slots, old.slots] at slots
  exact ObligationSlot.live.inj (List.cons.inj slots).1

theorem History.consume_state_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (old : History base scope currentAt wordAt birth grant)
    (new : History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state)
    (visit : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit)
    (oldItem : {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)})
    (newItem : {item // item ∈ (law base scope).rawItems (otherCurrent visit) (otherWord visit)})
    (sameItem : newItem.val = oldItem.val) :
    (new.consume visit newItem).state = (old.consume visit oldItem).state := by
  have sameObligation := History.obligation_eq_of_state_eq old new sameState
  rcases old with ⟨oldObligation, oldOrigin, oldState, oldSlots, oldRun⟩
  rcases new with ⟨newObligation, newOrigin, newState, newSlots, newRun⟩
  dsimp only at sameState sameObligation
  subst newState
  subst newObligation
  have effects := read_effect_congr sameIndex oldObligation oldOrigin newOrigin visit sameCurrent sameWord oldItem newItem sameItem
  unfold History.consume
  cases oldRead : readEvent oldObligation oldOrigin visit oldItem <;>
    cases newRead : readEvent oldObligation newOrigin visit newItem <;>
    simp only [oldRead, newRead, Option.map_none, Option.map_some] at effects
  · rfl
  · cases effects
  · cases effects
  · rename_i oldEvent newEvent
    have dispositions := congrArg (fun data => data.2.1) (Option.some.inj effects)
    dsimp only [effect] at dispositions
    dsimp only [History.cross, History.edge, NativeResponsibilityProcess.Edge.target,
      NativeResponsibilityProcess.Edge.lifecycleEvent, process]
    rw [dispositions]
    rfl


def reindexItem
    {first second : RawCurrent Party Good (State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (item : {item // item ∈ (law base scope).rawItems first firstWord}) :
    {item // item ∈ (law base scope).rawItems second secondWord} :=
  ⟨item.val, by rw [sameCurrent, sameWord]; exact item.property⟩

private theorem attach_reindex
    {first second : RawCurrent Party Good (State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord) :
    ((law base scope).rawItems second secondWord).attach =
      ((law base scope).rawItems first firstWord).attach.map (reindexItem sameCurrent sameWord) := by
  cases sameCurrent
  cases sameWord
  change _ = List.map id _
  exact (List.map_id _).symm

private theorem consume_many_state_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (visit : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit)
    (items : List {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)})
    (old : History base scope currentAt wordAt birth grant)
    (new : History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state) :
    ((items.map (reindexItem sameCurrent sameWord)).foldl (fun history item => history.consume visit item) new).state =
      (items.foldl (fun history item => history.consume visit item) old).state := by
  induction items generalizing old new with
  | nil => exact sameState
  | cons item rest ih =>
    exact ih (old.consume visit item) (new.consume visit (reindexItem sameCurrent sameWord item))
      (History.consume_state_congr sameIndex old new sameState visit sameCurrent sameWord item _ rfl)

theorem History.visit_state_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (old : History base scope currentAt wordAt birth grant)
    (new : History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state)
    (visit : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit) :
    (new.visit visit).state = (old.visit visit).state := by
  unfold History.visit
  rw [attach_reindex sameCurrent sameWord]
  exact consume_many_state_congr sameIndex visit sameCurrent sameWord _ old new sameState

private theorem visits_state_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (visits : List Nat)
    (sameCurrent : ∀ visit ∈ visits, otherCurrent visit = currentAt visit)
    (sameWord : ∀ visit ∈ visits, otherWord visit = wordAt visit)
    (old : History base scope currentAt wordAt birth grant)
    (new : History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state) :
    (visits.foldl (fun history visit => history.visit visit) new).state =
      (visits.foldl (fun history visit => history.visit visit) old).state := by
  induction visits generalizing old new with
  | nil => exact sameState
  | cons visit rest ih =>
    exact ih (fun later member => sameCurrent later (List.mem_cons_of_mem _ member))
      (fun later member => sameWord later (List.mem_cons_of_mem _ member))
      (old.visit visit) (new.visit visit)
      (History.visit_state_congr sameIndex old new sameState visit
        (sameCurrent visit List.mem_cons_self) (sameWord visit List.mem_cons_self))

theorem through_state_congr (last : Nat)
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (sameInitial : initialState base scope otherCurrent otherWord birth otherGrant =
      initialState base scope currentAt wordAt birth grant)
    (sameCurrent : ∀ visit ≤ last, otherCurrent visit = currentAt visit)
    (sameWord : ∀ visit ≤ last, otherWord visit = wordAt visit) :
    (through (base := base) (scope := scope) (currentAt := otherCurrent) (wordAt := otherWord)
      (birth := birth) (grant := otherGrant) last).state =
    (through (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt)
      (birth := birth) (grant := grant) last).state :=
  visits_state_congr sameIndex (List.range (last + 1))
    (fun visit member => sameCurrent visit (Nat.le_of_lt_succ (List.mem_range.mp member)))
    (fun visit member => sameWord visit (Nat.le_of_lt_succ (List.mem_range.mp member)))
    initial initial sameInitial


def History.visitPrefix (history : History base scope currentAt wordAt birth grant) (visit count : Nat) :=
  (((law base scope).rawItems (currentAt visit) (wordAt visit)).attach.take count).foldl
    (fun prior item => prior.consume visit item) history

theorem History.visitPrefix_state_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (old : History base scope currentAt wordAt birth grant)
    (new : History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state)
    (visit count : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit) :
    (new.visitPrefix visit count).state = (old.visitPrefix visit count).state := by
  unfold History.visitPrefix
  rw [attach_reindex sameCurrent sameWord, ← List.map_take]
  exact consume_many_state_congr sameIndex visit sameCurrent sameWord _ old new sameState

theorem History.read_effect_heq
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (old : History base scope currentAt wordAt birth grant)
    (new : History base scope otherCurrent otherWord birth otherGrant)
    (sameState : new.state = old.state)
    (visit : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit)
    (oldItem : {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)}) :
    HEq ((readEvent new.obligation new.origin visit (reindexItem sameCurrent sameWord oldItem)).map effect)
      ((readEvent old.obligation old.origin visit oldItem).map effect) := by
  have sameObligation := History.obligation_eq_of_state_eq old new sameState
  rcases old with ⟨oldObligation, oldOrigin, oldState, oldSlots, oldRun⟩
  rcases new with ⟨newObligation, newOrigin, newState, newSlots, newRun⟩
  dsimp only at sameState sameObligation
  subst newState
  subst newObligation
  exact heq_of_eq (read_effect_congr sameIndex oldObligation oldOrigin newOrigin visit
    sameCurrent sameWord oldItem _ rfl)

def beforeVisit (visit : Nat) : History base scope currentAt wordAt birth grant :=
  match visit with
  | 0 => initial
  | prior + 1 => through prior

theorem beforeVisit_state_congr (last visit : Nat) (inside : visit ≤ last)
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (sameInitial : initialState base scope otherCurrent otherWord birth otherGrant =
      initialState base scope currentAt wordAt birth grant)
    (sameCurrent : ∀ visit ≤ last, otherCurrent visit = currentAt visit)
    (sameWord : ∀ visit ≤ last, otherWord visit = wordAt visit) :
    (beforeVisit (base := base) (scope := scope) (currentAt := otherCurrent) (wordAt := otherWord)
      (birth := birth) (grant := otherGrant) visit).state =
    (beforeVisit (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt)
      (birth := birth) (grant := grant) visit).state := by
  cases visit with
  | zero => exact sameInitial
  | succ prior =>
    exact through_state_congr prior sameIndex sameInitial
      (fun visit earlier => sameCurrent visit (by omega)) (fun visit earlier => sameWord visit (by omega))


theorem History.visit_empty (history : History base scope currentAt wordAt birth grant)
    (visit : Nat) (empty : wordAt visit = []) : history.visit visit = history := by
  unfold History.visit
  have noItems : ((law base scope).rawItems (currentAt visit) (wordAt visit)).attach = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    rw [List.length_attach, empty]
    rfl
  rw [noItems]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed
