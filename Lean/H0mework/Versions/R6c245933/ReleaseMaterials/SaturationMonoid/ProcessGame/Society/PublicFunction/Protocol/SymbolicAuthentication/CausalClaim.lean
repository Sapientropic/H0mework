import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquiry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CausalClaim

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type}
  (bound : Mandate.Challenge.ProgrammeFamily base scope Index) (inputs : Index)

abbrev Key := Nat × Nat
def later (first second : Key) : Prop := first.1 < second.1 ∨ (first.1 = second.1 ∧ first.2 < second.2)
instance (first second : Key) : Decidable (later first second) := by unfold later; infer_instance

structure Target (Party Technology : Type) where
  key : Key
  snapshot : Mandate.State Party Technology
  deriving DecidableEq

structure Entry (Party Good Port Technology Instrument : Type) where
  key : Key
  item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument

abbrev target (claim : Mandate.Challenge.Claim bound inputs) : Target Party Technology :=
  ⟨(claim.position.ordinal, claim.position.index.val), claim.snapshot bound inputs⟩
abbrev entry (position : Mandate.Challenge.Position bound inputs) : Entry Party Good Port Technology Instrument :=
  ⟨(position.ordinal, position.index.val), position.item bound inputs⟩

def admitted (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument) : Prop :=
  Mandate.Challenge.Submission (scope := scope) item.request ∧ (Mandate.law base scope).Valid item.before item.request ∧
    (item.before.technology.holder.isSome = true ∨ item.before.technology.offered.isSome = true)
instance (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument) :
    Decidable (admitted (base := base) (scope := scope) item) := by unfold admitted; infer_instance

def receive (origin : Key) (signer : Party) (current : Option (Target Party Technology))
    (next : Entry Party Good Port Technology Instrument) : Option (Target Party Technology) :=
  match current with
  | none => none
  | some previous =>
    if admitted (base := base) (scope := scope) next.item ∧ later origin next.key ∧ next.item.request.signer = signer then
      if later previous.key next.key then some ⟨next.key, next.item.before.technology⟩ else current
    else if later previous.key next.key ∧ Mandate.Challenge.Withdrawal (scope := scope) next.item.before next.item.request ∧
        next.item.before.technology = previous.snapshot ∧ (Mandate.law base scope).Valid next.item.before next.item.request
      then none else current

def view {original : Mandate.Challenge.Claim bound inputs} : Mandate.Challenge.History bound inputs original → Option (Target Party Technology)
  | .pending selected .. => some (target bound inputs (selected.claim bound inputs))
  | .closed .. => none

theorem pending_is_exactly_the_native_pending_bit {original : Mandate.Challenge.Claim bound inputs}
    (history : Mandate.Challenge.History bound inputs original) :
    (view bound inputs history).isSome = history.isPending bound inputs := by cases history <;> rfl

private theorem read_some (position : Mandate.Challenge.Position bound inputs)
    (claim : Mandate.Challenge.Claim bound inputs) (read : Mandate.Challenge.read bound inputs position = some claim) :
    claim.position = position ∧ admitted (base := base) (scope := scope) (position.item bound inputs) := by
  unfold Mandate.Challenge.read at read
  split_ifs at read
  cases read
  exact ⟨rfl, by assumption, by assumption, by assumption⟩

private theorem read_none (position : Mandate.Challenge.Position bound inputs)
    (read : Mandate.Challenge.read bound inputs position = none) :
    ¬ admitted (base := base) (scope := scope) (position.item bound inputs) := by
  unfold Mandate.Challenge.read at read
  unfold admitted
  split_ifs at read <;> simp_all

private theorem target_signer (original : Mandate.Challenge.Claim bound inputs)
    (selected : Mandate.Challenge.Target bound inputs original) :
    (selected.claim bound inputs).signer bound inputs = original.signer bound inputs := by
  cases selected with
  | initial => rfl
  | renewed receipt => exact receipt.signer

theorem receiving_an_actual_item_preserves_the_complete_native_pending_view
    (original : Mandate.Challenge.Claim bound inputs) (history : Mandate.Challenge.History bound inputs original)
    (position : Mandate.Challenge.Position bound inputs) :
    view bound inputs (history.receive bound inputs position) =
      receive (base := base) (scope := scope) (target bound inputs original).key (original.signer bound inputs)
        (view bound inputs history) (entry bound inputs position) := by
  cases history with
  | closed state archive slots => rfl
  | pending selected state slots =>
    simp only [Mandate.Challenge.History.receive]
    cases decoded : Mandate.Challenge.readReconfirmation bound inputs original position with
    | some receipt =>
      have fresh := decoded
      unfold Mandate.Challenge.readReconfirmation at fresh
      cases claimRead : Mandate.Challenge.read bound inputs position with
      | none => simp only [claimRead] at fresh; contradiction
      | some claim =>
        simp only [claimRead] at fresh
        split_ifs at fresh with eligible
        cases Option.some.inj fresh
        have material := read_some bound inputs position claim claimRead
        have chosen := material.1
        subst chosen
        have renew : admitted (base := base) (scope := scope) (claim.position.item bound inputs) ∧
            later (target bound inputs original).key (target bound inputs claim).key ∧
            claim.signer bound inputs = original.signer bound inputs := ⟨material.2, eligible⟩
        by_cases newer : Mandate.Challenge.Later bound inputs (selected.claim bound inputs).position claim.position
        · simp only [dif_pos newer]
          change some (target bound inputs claim) = _
          have now : later (target bound inputs (selected.claim bound inputs)).key (target bound inputs claim).key := newer
          simp only [view, receive, if_pos renew, if_pos now]
        · simp only [dif_neg newer]
          change some (target bound inputs (selected.claim bound inputs)) = _
          have now : ¬ later (target bound inputs (selected.claim bound inputs)).key (target bound inputs claim).key := newer
          simp only [view, receive, if_pos renew, if_neg now]
    | none =>
      have unavailable : ¬ (admitted (base := base) (scope := scope) (position.item bound inputs) ∧
          Mandate.Challenge.Later bound inputs original.position position ∧
          (position.item bound inputs).request.signer = original.signer bound inputs) := by
        intro eligible
        unfold Mandate.Challenge.readReconfirmation at decoded
        cases claimRead : Mandate.Challenge.read bound inputs position with
        | none => exact read_none bound inputs position claimRead eligible.1
        | some claim =>
          have material := read_some bound inputs position claim claimRead
          have equal : claim.signer bound inputs = original.signer bound inputs := by
            rw [Mandate.Challenge.Claim.signer, material.1]; exact eligible.2.2
          have checked : Mandate.Challenge.Later bound inputs original.position claim.position ∧
              claim.signer bound inputs = original.signer bound inputs :=
            ⟨by simpa only [material.1] using eligible.2.1, equal⟩
          simp only [claimRead, dif_pos checked, reduceCtorEq] at decoded
      change ¬ (admitted (base := base) (scope := scope) (position.item bound inputs) ∧
        later (target bound inputs original).key (entry bound inputs position).key ∧
        (position.item bound inputs).request.signer = original.signer bound inputs) at unavailable
      dsimp only
      cases attempt : Mandate.Challenge.readAttempt bound inputs (selected.claim bound inputs) position with
      | none =>
        have absent := attempt
        unfold Mandate.Challenge.readAttempt at absent
        split_ifs at absent with checked
        simp only [view, receive]
        dsimp only [target, entry]
        rw [if_neg unavailable]
        exact (if_neg (fun all => checked ⟨all.1, all.2.1, all.2.2.1⟩)).symm
      | some receipt =>
        have found := attempt
        unfold Mandate.Challenge.readAttempt at found
        split_ifs at found with checked
        cases Option.some.inj found
        dsimp only
        by_cases paid : (Mandate.law base scope).Valid (position.item bound inputs).before (position.item bound inputs).request
        · simp only [dif_pos paid, view, receive]
          dsimp only [target, entry]
          rw [if_neg unavailable, if_pos ⟨checked.1, checked.2.1, checked.2.2, paid⟩]
        · simp only [dif_neg paid, view, receive]
          dsimp only [target, entry]
          rw [if_neg unavailable, if_neg (fun all => paid all.2.2.2)]

def trace (count : Nat) : List (Entry Party Good Port Technology Instrument) :=
  (List.range count).flatMap fun ordinal => (Mandate.Challenge.positionsAt bound inputs ordinal).map (entry bound inputs)

private theorem fold_view (original : Mandate.Challenge.Claim bound inputs)
    (positions : List (Mandate.Challenge.Position bound inputs))
    (history : Mandate.Challenge.History bound inputs original) :
    view bound inputs (positions.foldl (Mandate.Challenge.History.receive bound inputs) history) =
      (positions.map (entry bound inputs)).foldl
        (receive (base := base) (scope := scope) (target bound inputs original).key (original.signer bound inputs))
        (view bound inputs history) := by
  induction positions generalizing history with
  | nil => rfl
  | cons position tail ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, receiving_an_actual_item_preserves_the_complete_native_pending_view]

theorem complete_native_history_has_the_causal_trace_view
    (original : Mandate.Challenge.Claim bound inputs) (count : Nat) :
    view bound inputs (Mandate.Challenge.through bound inputs original count) =
      (trace bound inputs count).foldl
        (receive (base := base) (scope := scope) (target bound inputs original).key (original.signer bound inputs))
        (some (target bound inputs original)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Mandate.Challenge.through, fold_view, ih]
    simp only [trace, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.foldl_append]

def seed (next : Entry Party Good Port Technology Instrument) : Option (Party × Target Party Technology) :=
  if admitted (base := base) (scope := scope) next.item then some (next.item.request.signer, ⟨next.key, next.item.before.technology⟩)
  else none

private theorem seed_is_the_original_native_admission (position : Mandate.Challenge.Position bound inputs) :
    seed (base := base) (scope := scope) (entry bound inputs position) =
      (Mandate.Challenge.read bound inputs position).map (fun claim => (claim.signer bound inputs, target bound inputs claim)) := by
  cases decoded : Mandate.Challenge.read bound inputs position with
  | none =>
    have denied := read_none bound inputs position decoded
    simp only [seed, if_neg denied, Option.map_none]
  | some claim =>
    have actual := read_some bound inputs position claim decoded
    rcases actual with ⟨rfl, accepted⟩
    simp only [seed, if_pos accepted, Option.map_some]

private theorem seeds_of_positions (positions : List (Mandate.Challenge.Position bound inputs)) :
    (positions.filterMap (Mandate.Challenge.read bound inputs)).map
        (fun claim => (claim.signer bound inputs, target bound inputs claim)) =
      (positions.map (entry bound inputs)).filterMap (seed (base := base) (scope := scope)) := by
  induction positions with
  | nil => rfl
  | cons position tail ih =>
    simp only [List.filterMap_cons, List.map_cons]
    rw [seed_is_the_original_native_admission]
    cases decoded : Mandate.Challenge.read bound inputs position <;> simp [ih]

def seeds (count : Nat) := (trace bound inputs count).filterMap (seed (base := base) (scope := scope))

private theorem all_native_admissions_are_generated (count : Nat) :
    (List.range count).flatMap (fun ordinal => (Mandate.Challenge.claimsAt bound inputs ordinal).map
        (fun claim => (claim.signer bound inputs, target bound inputs claim))) = seeds bound inputs count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ih, Mandate.Challenge.claimsAt, seeds_of_positions]
    simp only [seeds, trace, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.filterMap_append]

def render (events : List (Entry Party Good Port Technology Instrument)) (original : Party × Target Party Technology) :=
  (original.2.key, original.1,
    events.foldl (receive (base := base) (scope := scope) original.2.key original.1) (some original.2))

def records (events : List (Entry Party Good Port Technology Instrument)) :=
  (events.filterMap (seed (base := base) (scope := scope))).map (render (base := base) (scope := scope) events)

theorem the_complete_original_native_inventory_has_exactly_the_generated_causal_records (count : Nat) :
    (Mandate.Challenge.recordsAt bound inputs count).map
        (fun row => ((target bound inputs row.1).key, row.1.signer bound inputs, view bound inputs row.2)) =
      records (base := base) (scope := scope) (trace bound inputs count) := by
  unfold records
  change _ = (seeds bound inputs count).map _
  rw [← all_native_admissions_are_generated]
  simp only [Mandate.Challenge.recordsAt, List.map_flatMap, List.map_map, Function.comp_def, render,
    complete_native_history_has_the_causal_trace_view]

def ownPending (events : List (Entry Party Good Port Technology Instrument)) (signer : Party) : Bool :=
  (records (base := base) (scope := scope) events).any fun row => row.2.1 == signer && row.2.2.isSome

theorem own_pending_consumes_every_original_and_newborn_native_claim (count : Nat) (signer : Party) :
    ownPending (base := base) (scope := scope) (trace bound inputs count) signer =
      (Mandate.Challenge.recordsAt bound inputs count).any
        (fun row => row.1.signer bound inputs == signer && row.2.isPending bound inputs) := by
  unfold ownPending
  rw [← the_complete_original_native_inventory_has_exactly_the_generated_causal_records]
  simp only [List.any_map, Function.comp_def, pending_is_exactly_the_native_pending_bit]

private theorem flatMap_same {α β : Type} (xs : List α) (f g : α → List β)
    (same : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [same x List.mem_cons_self, ih (fun y member => same y (List.mem_cons_of_mem _ member))]

theorem the_view_depends_only_on_the_completed_actual_items
    (nextInputs : Index) (count : Nat)
    (common : ∀ ordinal < count,
      Registered.traceItems (Mandate.Challenge.I bound inputs) (ProgrammeHistory.visitAt (Mandate.Challenge.I bound inputs) ordinal).current =
        Registered.traceItems (Mandate.Challenge.I bound nextInputs) (ProgrammeHistory.visitAt (Mandate.Challenge.I bound nextInputs) ordinal).current) :
    trace bound inputs count = trace bound nextInputs count := by
  unfold trace
  apply flatMap_same
  intro ordinal inside
  have same := common ordinal (List.mem_range.mp inside)
  simp only [Mandate.Challenge.positionsAt, List.map_map, Function.comp_def]
  change ((List.finRange _).map (fun index =>
    (⟨(ordinal, index.val), (Registered.traceItems (Mandate.Challenge.I bound inputs)
      (ProgrammeHistory.visitAt (Mandate.Challenge.I bound inputs) ordinal).current).get index⟩ : Entry Party Good Port Technology Instrument))) =
    ((List.finRange _).map (fun index =>
    (⟨(ordinal, index.val), (Registered.traceItems (Mandate.Challenge.I bound nextInputs)
      (ProgrammeHistory.visitAt (Mandate.Challenge.I bound nextInputs) ordinal).current).get index⟩ : Entry Party Good Port Technology Instrument)))
  rw [same]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CausalClaim
