import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Feed
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

inductive CellResult (prepared : Prepared input) (index : Index prepared) where
  | stopped (header : Prepaid.Protocol (Policy.initial input prepared.saved[index].point) input.pricing input.future
      (Policy.reference input prepared.saved[index].point) input.actor input.position) (same : prepared.saved[index].stage = .stopped header)
  | prior (failure : ReservationFailure input prepared.saved[index].point) (same : prepared.saved[index].stage = .blocked failure)
  | unpriced (scope : Scope prepared.saved[index].point) (same : prepared.saved[index].stage = .ready scope)
      (why : feeAt (feePoint scope) input.actor input.position = none)
  | negative (scope : Scope prepared.saved[index].point) (same : prepared.saved[index].stage = .ready scope)
      (fee : Fee scope) (observed : read scope = .found fee)
      (good : G) (listed : good ∈ fee.keys) (broken : fee.stock good < 0)
  | available (scope : Scope prepared.saved[index].point) (same : prepared.saved[index].stage = .ready scope)
      (fee : Fee scope) (observed : read scope = .found fee) (capacity : Fee.Available fee)

def observeCell (prepared : Prepared input) (index : Index prepared) : CellResult prepared index :=
  match same : prepared.saved[index].stage with
  | .stopped header => .stopped header same
  | .blocked failure => .prior failure same
  | .ready scope =>
      match observed : read scope with
      | .absent why => .unpriced scope same why
      | .found fee => match fee.analyse with
        | .negative good listed broken => .negative scope same fee observed good listed broken
        | .available capacity => .available scope same fee observed capacity

namespace CellResult
variable {index : Index prepared}
def units : CellResult prepared index → Option Nat
  | .available _ _ _ _ capacity => some capacity.units
  | _ => none

def Allows (count : Nat) : CellResult prepared index → Prop
  | .available _ _ fee _ _ => fee.MaterialGate count
  | _ => False

def Legal (count : Nat) : CellResult prepared index → Prop
  | .available _ _ fee _ _ | .negative _ _ fee .. => fee.Legal count
  | _ => False

theorem legal_implies_allowed (cell : CellResult prepared index) (count : Nat)
    (legal : cell.Legal count) : cell.Allows count := by
  cases cell with
  | stopped | prior | unpriced => exact False.elim legal
  | negative scope same fee observed good listed broken =>
      exact False.elim ((fee.negative_stock_prevents_every_payment good listed broken count)
        ((fee.fits_is_the_original_material_gate count).mpr (fee.legal_has_original_material_gate count legal)))
  | available scope same fee observed capacity => exact fee.legal_has_original_material_gate count legal

theorem unavailable_excludes_legal (cell : CellResult prepared index)
    (blocked : cell.units.isSome = false) (count : Nat) : ¬ cell.Legal count := by
  intro legal
  have allowed := cell.legal_implies_allowed count legal
  cases cell <;> cases blocked <;> exact allowed

theorem exact_capacity (cell : CellResult prepared index) (ready : cell.units.isSome = true) (count : Nat) :
    count ≤ cell.units.getD 0 ↔ cell.Allows count := by
  cases cell with
  | available _ _ fee _ capacity => exact capacity.exact_source_debit_capacity count
  | _ => cases ready
end CellResult

abbrev CachedCell (prepared : Prepared input) := Sigma (CellResult prepared)
def observations (prepared : Prepared input) : List (CachedCell prepared) :=
  (keys prepared).map fun index => ⟨index,observeCell prepared index⟩

structure Snapshot (prepared : Prepared input) where
  private mk ::
  cached : List (CachedCell prepared)
  generated : cached = observations prepared
  keys_exact : cached.map Sigma.fst = keys prepared

def capture (prepared : Prepared input) : Snapshot prepared :=
  ⟨observations prepared,rfl,by
    simp only [observations,List.map_map,Function.comp_def]
    induction keys prepared with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih⟩

namespace Snapshot
variable (snapshot : Snapshot prepared)

theorem cached_length : snapshot.cached.length = prepared.saved.length := by
  have sizes := congrArg List.length snapshot.keys_exact
  simpa only [List.length_map,keys,List.length_finRange] using sizes

def cachedIndex (index : Index prepared) : Fin snapshot.cached.length :=
  ⟨index.val,by rw [snapshot.cached_length];exact index.isLt⟩

theorem cached_key (index : Index prepared) : snapshot.cached[snapshot.cachedIndex index].1 = index := by
  have selected : (snapshot.cached.map Sigma.fst)[index.val]? = some index := by
    rw [snapshot.keys_exact]
    simp [keys,List.finRange]
  obtain ⟨bounded,same⟩ := List.getElem?_eq_some_iff.mp selected
  simpa only [List.getElem_map,Fin.getElem_fin,cachedIndex] using same

def resultAt (index : Index prepared) : CellResult prepared index :=
  snapshot.cached_key index ▸ snapshot.cached[snapshot.cachedIndex index].2

theorem every_original_point_keeps_its_order_and_multiplicity :
    snapshot.cached.map (fun entry => prepared.saved[entry.1].point) = prepared.saved.map Cell.point := by
  have mapped := congrArg (List.map (fun index : Index prepared => prepared.saved[index].point)) snapshot.keys_exact
  rw [List.map_map] at mapped
  exact mapped.trans (by
    simpa only [keys,List.finRange,List.map_ofFn,Function.comp_def,Fin.getElem_fin] using
      congrArg (List.map Cell.point) (List.ofFn_getElem (xs := prepared.saved)))
end Snapshot

structure Catalogue (snapshot : Snapshot prepared) where
  private mk ::
  first : CachedCell prepared
  rest : List (CachedCell prepared)
  same : snapshot.cached = first::rest
  all_available : ∀ cell ∈ snapshot.cached,cell.2.units.isSome = true

namespace Catalogue
variable {snapshot : Snapshot prepared} (domain : Catalogue snapshot)

def bound : Nat := minimum (domain.first.2.units.getD 0) (domain.rest.map fun cell => cell.2.units.getD 0)
abbrev Quota := Fin (domain.bound+1)

theorem exact_common_material_domain (count : Nat) : count ≤ domain.bound ↔
    ∀ cell ∈ snapshot.cached,cell.2.Allows count := by
  rw [bound,bounded_iff]
  constructor
  · rintro ⟨first,later⟩ cell inside
    have ready := domain.all_available cell inside
    apply (cell.2.exact_capacity ready count).mp
    rw [domain.same] at inside
    rcases List.mem_cons.mp inside with same | following
    · subst cell;exact first
    · exact later _ (List.mem_map.mpr ⟨cell,following,rfl⟩)
  · intro all
    have firstInside : domain.first ∈ snapshot.cached := by rw [domain.same];exact List.mem_cons_self
    refine ⟨(domain.first.2.exact_capacity (domain.all_available _ firstInside) count).mpr (all _ firstInside),?_⟩
    intro limit inside
    obtain ⟨cell,later,same⟩ := List.mem_map.mp inside
    subst limit
    have listed : cell ∈ snapshot.cached := by rw [domain.same];exact List.mem_cons_of_mem _ later
    exact (cell.2.exact_capacity (domain.all_available _ listed) count).mpr (all _ listed)

def admit (count : Nat) (affordable : ∀ cell ∈ snapshot.cached,cell.2.Allows count) : domain.Quota :=
  ⟨count,Nat.lt_succ_iff.mpr ((domain.exact_common_material_domain count).mpr affordable)⟩

theorem every_materially_affordable_quota_is_generated (count : Nat)
    (affordable : ∀ cell ∈ snapshot.cached,cell.2.Allows count) :
    ∃ quota : domain.Quota,quota.val = count := ⟨domain.admit count affordable,rfl⟩

def quotas : List domain.Quota := List.finRange (domain.bound+1)

theorem every_affordable_quantity_occurs_in_the_source_domain (count : Nat)
    (affordable : ∀ cell ∈ snapshot.cached,cell.2.Allows count) :
    ∃ quota ∈ domain.quotas,quota.val = count :=
  ⟨domain.admit count affordable,List.mem_finRange _,rfl⟩

theorem every_uniform_legal_fee_quantity_is_generated (count : Nat)
    (legal : ∀ cell ∈ snapshot.cached,cell.2.Legal count) :
    ∃ quota ∈ domain.quotas,quota.val = count :=
  domain.every_affordable_quantity_occurs_in_the_source_domain count
    (fun cell inside => cell.2.legal_implies_allowed count (legal cell inside))

-- Generate each offer on demand; the original comparison retains the spending choice.
def offer (quota : domain.Quota) : EscrowBudget.Attempt prepared quota.val := EscrowBudget.generate prepared quota.val

theorem each_offer_has_the_exact_source_material_bound (quota : domain.Quota) :
    ∀ cell ∈ snapshot.cached,cell.2.Allows quota.val :=
  (domain.exact_common_material_domain quota.val).mp (Nat.le_of_lt_succ quota.isLt)
end Catalogue

inductive Result (prepared : Prepared input) (snapshot : Snapshot prepared) where
  | empty (absent : snapshot.cached = [])
  | blocked (cell : CachedCell prepared) (listed : cell ∈ snapshot.cached) (failure : cell.2.units.isSome = false)
  | domain (made : Catalogue snapshot)

def inspect (snapshot : Snapshot prepared) : Result prepared snapshot :=
  match Distributed.inspect (fun cell : CachedCell prepared => cell.2.units.isSome = true) snapshot.cached with
  | .rejected cell listed broken => .blocked cell listed (Bool.eq_false_iff.mpr broken)
  | .accepted all => match same : snapshot.cached with
    | [] => .empty same
    | first::rest => .domain ⟨first,rest,same,all⟩

structure Generated (prepared : Prepared input) where
  private mk ::
  snapshot : Snapshot prepared
  source : snapshot = capture prepared
  result : Result prepared snapshot
  generated : result = inspect snapshot

def generate (prepared : Prepared input) : Generated prepared :=
  let snapshot := capture prepared
  ⟨snapshot,rfl,inspect snapshot,rfl⟩

inductive Debt (prepared : Prepared input) where
  | original (old : Policy.Obligation prepared)
  | source (cell : CachedCell prepared)
  | lookup (index : Index prepared)
  | quotaEnumeration
  | comparison
  | storage

def Generated.pending (made : Generated prepared) : List (Debt prepared) :=
  (Policy.obligations prepared).map Debt.original ++ made.snapshot.cached.map Debt.source ++
    (keys prepared).map Debt.lookup ++ [.quotaEnumeration,.comparison,.storage]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota
namespace Acquisition
set_option backward.isDefEq.respectTransparency false
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

def availableTag {index : Index prepared} : CellResult prepared index → Bool
  | .available .. => true
  | _ => false
theorem availableTag_exact {index : Index prepared} (cell : CellResult prepared index) :
    availableTag cell = cell.units.isSome := by cases cell <;> rfl

private theorem snapshot_is_capture (snapshot : Snapshot prepared) : snapshot = capture prepared := by
  rcases snapshot with ⟨cached,generated,keys⟩
  cases generated;rfl
private theorem generated_is_canonical (source : Generated prepared) : source = generate prepared := by
  rcases source with ⟨snapshot,same,result,generated⟩
  cases same;cases generated;rfl

private def snapshotFrom (cached : List (CachedCell prepared)) (generated : cached = observations prepared) : Snapshot prepared :=
  ⟨cached,generated,by rw [generated];exact (capture prepared).keys_exact⟩
abbrev Check (prepared : Prepared input) (cells : List (CachedCell prepared)) :=
  Distributed.Inspection (fun cell : CachedCell prepared => cell.2.units.isSome = true) cells
private def liftCheck (head : CachedCell prepared) {tail : List (CachedCell prepared)}
    (checked : head.2.units.isSome = true) : Check prepared tail → Check prepared (head::tail)
  | .accepted all => .accepted (by
      intro cell inside
      rcases List.mem_cons.mp inside with same | later
      · subst cell;exact checked
      · exact all cell later)
  | .rejected cell listed broken => .rejected cell (List.mem_cons_of_mem _ listed) broken
private theorem liftCheck_exact (head : CachedCell prepared) (tail : List (CachedCell prepared))
    (checked : head.2.units.isSome = true) :
    liftCheck head checked (Distributed.inspect (fun cell : CachedCell prepared => cell.2.units.isSome = true) tail) = Distributed.inspect (fun cell : CachedCell prepared => cell.2.units.isSome = true) (head::tail) := by
  simp only [Distributed.inspect,checked,↓reduceDIte]
  cases Distributed.inspect (fun cell : CachedCell prepared => cell.2.units.isSome = true) tail <;> rfl
private def resultFrom (snapshot : Snapshot prepared) : Check prepared snapshot.cached → Result prepared snapshot
  | .rejected cell listed broken => .blocked cell listed (Bool.eq_false_iff.mpr broken)
  | .accepted all => match same : snapshot.cached with
    | [] => .empty same
    | first::rest => .domain ⟨first,rest,same,all⟩
private theorem resultFrom_nil (snapshot : Snapshot prepared)
    (all : ∀ cell ∈ snapshot.cached,cell.2.units.isSome = true) (same : snapshot.cached = []) :
    resultFrom snapshot (.accepted all) = .empty same := by
  dsimp only [resultFrom]
  split
  · rfl
  · rename_i first rest contrary
    cases same.symm.trans contrary
private theorem resultFrom_cons (snapshot : Snapshot prepared)
    (all : ∀ cell ∈ snapshot.cached,cell.2.units.isSome = true) (first : CachedCell prepared)
    (rest : List (CachedCell prepared)) (same : snapshot.cached = first::rest) :
    resultFrom snapshot (.accepted all) = .domain ⟨first,rest,same,all⟩ := by
  dsimp only [resultFrom]
  split
  · rename_i contrary
    cases same.symm.trans contrary
  · rename_i head tail eq
    rcases List.cons.inj (same.symm.trans eq) with ⟨rfl,rfl⟩
    rfl
private def realize (snapshot : Snapshot prepared) (checked : Check prepared snapshot.cached)
    (actual : checked = Distributed.inspect (fun cell : CachedCell prepared => cell.2.units.isSome = true) snapshot.cached) : Generated prepared :=
  ⟨snapshot,snapshot_is_capture snapshot,resultFrom snapshot checked,congrArg (resultFrom snapshot) actual⟩

inductive Output (prepared : Prepared input) where
  | unavailable (source : Generated prepared) (generated : source = generate prepared)
      (outside : match source.result with | .domain _ => False | _ => True)
  | domain (source : Generated prepared) (generated : source = generate prepared)
      (catalogue : Catalogue source.snapshot) (same : source.result = .domain catalogue)
      (limit : Nat) (bound : limit = catalogue.bound)

-- All observations finish before validation, so even a blocked result retains the entire source.
inductive State (prepared : Prepared input) where
  | observing (cached : List (CachedCell prepared)) (remaining : List (Index prepared))
      (conserved : cached ++ remaining.map (fun index => ⟨index,observeCell prepared index⟩) = observations prepared)
  | validating (snapshot : Snapshot prepared) (remaining : List (CachedCell prepared))
      (embed : Check prepared remaining → Check prepared snapshot.cached)
      (coherent : embed (Distributed.inspect (fun cell : CachedCell prepared => cell.2.units.isSome = true) remaining) = Distributed.inspect (fun cell : CachedCell prepared => cell.2.units.isSome = true) snapshot.cached)
  | seeding (source : Generated prepared) (generated : source = generate prepared)
      (catalogue : Catalogue source.snapshot) (same : source.result = .domain catalogue)
  | folding (source : Generated prepared) (generated : source = generate prepared)
      (catalogue : Catalogue source.snapshot) (same : source.result = .domain catalogue)
      (remaining : List (CachedCell prepared)) (limit : Nat)
      (conserved : minimum limit (remaining.map fun cell => cell.2.units.getD 0) = catalogue.bound)
  | reducing (source : Generated prepared) (generated : source = generate prepared)
      (catalogue : Catalogue source.snapshot) (same : source.result = .domain catalogue)
      (remaining : List (CachedCell prepared)) (limit units : Nat)
      (conserved : minimum limit (units::remaining.map fun cell => cell.2.units.getD 0) = catalogue.bound)
  | finished (output : Output prepared)

def initial (prepared : Prepared input) : State prepared := .observing [] (keys prepared) rfl
inductive Event (prepared : Prepared input) where
  | observed (index : Index prepared) (cell : CellResult prepared index) (actual : cell = observeCell prepared index)
  | captured (snapshot : Snapshot prepared)
  | checked (cell : CachedCell prepared) (value : Bool) (actual : value = availableTag cell.2)
  | validated (snapshot : Snapshot prepared)
  | seeded (cell : CachedCell prepared) (units : Nat) (actual : units = cell.2.units.getD 0)
  | capacity (cell : CachedCell prepared) (units : Nat) (actual : units = cell.2.units.getD 0)
  | reduced (before units after : Nat) (actual : after = min units before)
  | completed (output : Output prepared)

private theorem minimum_shift (limit units : Nat) (tail : List Nat) :
    minimum (min units limit) tail = minimum limit (units::tail) := by
  induction tail with
  | nil => rfl
  | cons head rest ih =>
      simp only [minimum] at *
      rw [ih]
      omega
private def finishValidation (snapshot : Snapshot prepared) (checked : Check prepared snapshot.cached)
    (actual : checked = Distributed.inspect (fun cell : CachedCell prepared => cell.2.units.isSome = true) snapshot.cached) : State prepared :=
  match checked with
  | .rejected cell listed broken =>
      .finished (.unavailable (realize snapshot (.rejected cell listed broken) actual)
        (generated_is_canonical _) trivial)
  | .accepted all => match same : snapshot.cached with
    | [] => .finished (.unavailable (realize snapshot (.accepted all) actual) (generated_is_canonical _) (by
        simp only [realize,resultFrom_nil snapshot all same]))
    | first::rest =>
        let source := realize snapshot (.accepted all) actual
        let catalogue : Catalogue source.snapshot := ⟨first,rest,same,all⟩
        .seeding source (generated_is_canonical source) catalogue (resultFrom_cons snapshot all first rest same)

def move : State prepared → Option (State prepared × Event prepared)
  | .observing cached (index::remaining) conserved =>
      let cell := observeCell prepared index
      some (.observing (cached++[⟨index,cell⟩]) remaining (by
        simpa only [List.map_cons,List.append_assoc,List.singleton_append] using conserved),.observed index cell rfl)
  | .observing cached [] conserved =>
      let snapshot := snapshotFrom cached (by simpa only [List.map_nil,List.append_nil] using conserved)
      some (.validating snapshot snapshot.cached id rfl,.captured snapshot)
  | .validating snapshot [] embed coherent =>
      some (finishValidation snapshot (embed (.accepted (by simp))) coherent,.validated snapshot)
  | .validating snapshot (head::tail) embed coherent =>
      if available : availableTag head.2 = true then
        let checked : head.2.units.isSome = true := (availableTag_exact head.2).symm.trans available
        some (.validating snapshot tail (fun later => embed (liftCheck head checked later))
          (by rw [liftCheck_exact];exact coherent),.checked head true available.symm)
      else
        let checked : ¬ head.2.units.isSome = true := fun yes => available ((availableTag_exact head.2).trans yes)
        some (finishValidation snapshot (embed (.rejected head List.mem_cons_self checked)) (by
          rw [← coherent];congr 1;rw [Distributed.inspect,dif_neg checked]),
          .checked head false (Bool.eq_false_iff.mpr available).symm)
  | .seeding source generated catalogue same =>
      let units := catalogue.first.2.units.getD 0
      some (.folding source generated catalogue same catalogue.rest units rfl,.seeded catalogue.first units rfl)
  | .folding source generated catalogue same (head::tail) limit conserved =>
      let units := head.2.units.getD 0
      some (.reducing source generated catalogue same tail limit units (by simpa only [List.map_cons] using conserved),
        .capacity head units rfl)
  | .reducing source generated catalogue same remaining limit units conserved =>
      some (.folding source generated catalogue same remaining (min units limit)
        ((minimum_shift limit units _).trans conserved),.reduced limit units (min units limit) rfl)
  | .folding source generated catalogue same [] limit conserved =>
      let output := Output.domain source generated catalogue same limit conserved
      some (.finished output,.completed output)
  | .finished _ => none

def State.done : State prepared → Bool | .finished _ => true | _ => false
def State.rank : State prepared → Nat
  | .observing _ remaining _ => remaining.length+3*(keys prepared).length+5
  | .validating snapshot remaining .. => remaining.length+2*snapshot.cached.length+4
  | .seeding _ _ catalogue _ => 2*catalogue.rest.length+2
  | .folding _ _ _ _ remaining .. => 2*remaining.length+1
  | .reducing _ _ _ _ remaining .. => 2*remaining.length+2
  | .finished _ => 0
private theorem finishValidation_rank (snapshot : Snapshot prepared) (checked : Check prepared snapshot.cached)
    (actual : checked = Distributed.inspect (fun cell : CachedCell prepared => cell.2.units.isSome = true) snapshot.cached) :
    (finishValidation snapshot checked actual).rank < 2*snapshot.cached.length+4 := by
  cases checked with
  | rejected => simp only [finishValidation,State.rank];omega
  | accepted all =>
      dsimp only [finishValidation]
      split
      · simp only [State.rank];omega
      · rename_i first rest same
        simp only [State.rank]
        rw [same,List.length_cons];omega

theorem each_actual_step_decreases_source_rank {before after : State prepared} {event : Event prepared}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | observing cached remaining conserved =>
      cases remaining with
      | cons index tail =>
          dsimp only [move] at actual;cases Option.some.inj actual
          simp only [State.rank,List.length_cons];omega
      | nil =>
          dsimp only [move] at actual;cases Option.some.inj actual
          have same := congrArg List.length (by simpa using conserved : cached = observations prepared)
          simp only [observations,List.length_map] at same
          simp only [State.rank,snapshotFrom,List.length_nil];omega
  | validating snapshot remaining embed coherent =>
      cases remaining with
      | nil =>
          dsimp only [move] at actual;cases Option.some.inj actual
          simpa only [State.rank,List.length_nil,Nat.zero_add] using finishValidation_rank snapshot _ _
      | cons head tail =>
          dsimp only [move] at actual;split at actual
          · cases Option.some.inj actual;simp only [State.rank,List.length_cons];omega
          · cases Option.some.inj actual
            apply lt_of_lt_of_le (b := 2*snapshot.cached.length+4)
            · exact finishValidation_rank snapshot _ _
            · simp only [State.rank,List.length_cons];omega
  | seeding | reducing =>
      dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | folding source generated catalogue same remaining limit conserved =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,List.length_cons,List.length_nil];omega
  | finished => cases actual

theorem no_move_iff_done (before : State prepared) : move before = none ↔ before.done = true := by
  cases before with
  | observing cached remaining conserved => cases remaining <;> simp [move,State.done]
  | validating snapshot remaining embed coherent => cases remaining <;> dsimp only [move,State.done] <;> first | (split <;> simp) | simp
  | seeding | reducing => simp [move,State.done]
  | folding source generated catalogue same remaining limit conserved => cases remaining <;> simp [move,State.done]
  | finished => simp [move,State.done]

inductive Trace : State prepared → State prepared → List (Event prepared) → Prop
  | nil (before) : Trace before before []
  | step {before middle after event work} (actual : move before = some (middle,event))
      (later : Trace middle after work) : Trace before after (event::work)
structure Calculation (before : State prepared) (capacity : Nat) where
  private mk ::
  endpoint : State prepared
  work : List (Event prepared)
  history : Trace before endpoint work
  fits : work.length ≤ capacity

def execute : (capacity : Nat) → (before : State prepared) → Calculation before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match actual : move before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) => let later := execute capacity after
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩
theorem sufficient_source_rank_finishes (capacity : Nat) (before : State prepared) (enough : before.rank ≤ capacity) :
    (execute capacity before).endpoint.done = true := by
  induction capacity generalizing before with
  | zero => cases before <;> simp_all [State.rank,State.done,execute]
  | succ capacity ih =>
      unfold execute;split
      · rename_i stopped;exact (no_move_iff_done before).mp stopped
      · rename_i after event actual;exact ih after (by have := each_actual_step_decreases_source_rank actual;omega)
theorem unfinished_uses_all (capacity : Nat) (before : State prepared)
    (pending : (execute capacity before).endpoint.done = false) : (execute capacity before).work.length = capacity := by
  induction capacity generalizing before with
  | zero => rfl
  | succ capacity ih =>
      unfold execute at pending ⊢;split at pending
      · rename_i stopped;rw [(no_move_iff_done before).mp stopped] at pending;cases pending
      · rename_i after event actual;exact congrArg Nat.succ (ih after pending)
end Acquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota
