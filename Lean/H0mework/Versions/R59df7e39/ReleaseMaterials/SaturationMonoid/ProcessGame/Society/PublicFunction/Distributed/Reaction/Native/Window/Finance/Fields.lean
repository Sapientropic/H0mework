import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance.Origin
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance.Fields
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)} {start span : Nat}
  (native : Origin.Completed bound start span)
abbrev Slot := ObligationSlot (Financial.vocabulary bound.source.input)
abbrev Record := LifecycleEvent (Financial.vocabulary bound.source.input)
def records := native.atEnd.current.history.drop native.atStart.current.history.length
private theorem ending : start+1+span = Window.finish start span := by unfold Window.finish;omega

theorem records_exact : records native =
    (Financial.BalanceConservation.fromActualCut bound.source.input (start+1) span).events := by
  unfold records
  rw [native.start_exact,native.end_exact]
  have history := (Financial.BalanceConservation.fromActualCut bound.source.input (start+1) span).history_eq
  conv_lhs at history => rw [ending]
  change (Window.last bound start span).current.history = (Window.first bound start).current.history ++ _ at history
  rw [history,List.drop_left]

theorem slot_count : native.atStart.current.slots.length ≤ native.atEnd.current.slots.length := by
  have retained :=  Financial.BalanceConservation.cut_preserves_all_original_claims bound.source.input (start+1) span
  have size := retained.length_le
  simp only [List.length_map] at size
  rw [ending] at size
  simpa only [native.start_exact,native.end_exact] using size

def finalSlot (index : Fin native.atStart.current.slots.length) : Slot (bound := bound) :=
  native.atEnd.current.slots.get ⟨index.val,index.isLt.trans_le (slot_count native)⟩
noncomputable def reference (index : Fin native.atStart.current.slots.length) :=
  Window.migration bound start span ⟨index.val,by simpa only [native.start_exact] using index.isLt⟩
theorem finalSlot_exact (index : Fin native.atStart.current.slots.length) :
    finalSlot native index = (reference native index).slot := by
  have present := (reference native index).present
  change (Financial.accountAt bound.source.input (start+1+span)).current.slots[index.val]? = some _ at present
  conv_lhs at present => rw [ending]
  have actual : native.atEnd.current.slots[index.val]? = some (reference native index).slot := by
    simpa only [native.end_exact] using present
  have lookup := List.getElem?_eq_getElem (index.isLt.trans_le (slot_count native))
  exact Option.some.inj (lookup.symm.trans actual)

private theorem filtered_sum {A : Type} (test : A → Bool) (value : A → ℚ) (data : List A) :
    ((data.filter test).map value).sum = (data.map fun item => if test item then value item else 0).sum := by
  induction data with
  | nil => rfl
  | cons head tail ih =>
      by_cases yes : test head = true
      · simp only [List.filter_cons,yes,↓reduceIte,List.map_cons,List.sum_cons,ih]
      · have no : test head = false := Bool.eq_false_iff.mpr yes
        simp only [List.filter_cons,no,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons,zero_add,ih]

def receivedTerm (index : Fin native.atStart.current.slots.length) (holder : P) (record : Record (bound := bound)) : ℚ :=
  if record.slot == index.val then Financial.Migration.received bound.source.input
    (Financial.Migration.sourceEvent bound.source.input record) holder else 0

theorem received_exact (index : Fin native.atStart.current.slots.length) (holder : P) :
    ((records native).map (receivedTerm native index holder)).sum =
      (reference native index).path.receivedBy bound.source.input holder := by
  unfold Financial.Migration.Path.receivedBy
  rw [←(reference native index).path.records_sources bound.source.input index.val,
    (reference native index).recorded,List.map_map]
  rw [records_exact]
  exact (filtered_sum _ _ _).symm
namespace Mapping
variable {A B : Type} (f : A → B) (data : List A)
structure State where
  private mk ::
  remaining : List A
  cached : List B
  meaning : cached++remaining.map f = data.map f
def initial : State f data := ⟨data,[],rfl⟩
variable {f data}
def State.rank (state : State f data) := state.remaining.length
def State.move (state : State f data) : Option (A × State f data) := match actual : state.remaining with
  | [] => none
  | head::tail => some (head,⟨tail,state.cached++[f head],by
      have known := state.meaning;rw [actual] at known
      simpa only [List.map_cons,List.append_assoc,List.singleton_append] using known⟩)
def State.completed (state : State f data) : Option {values : List B // values = data.map f} := match actual : state.remaining with
  | [] => some ⟨state.cached,by simpa only [actual,List.map_nil,List.append_nil] using state.meaning⟩
  | _::_ => none
theorem State.move_decreases {before after : State f data} {event : A} (actual : before.move = some (event,after)) :
    after.rank+1 = before.rank := by
  rcases before with ⟨remaining,cached,meaning⟩;cases remaining with
  | nil => cases actual
  | cons head tail => dsimp only [State.move] at actual;cases actual;rfl
theorem State.completed_iff_stopped (state : State f data) : state.completed.isSome = true ↔ state.move = none := by
  rcases state with ⟨remaining,cached,meaning⟩;cases remaining <;> simp [State.completed,State.move]
theorem State.stopped_iff_zero (state : State f data) : state.move = none ↔ state.rank = 0 := by
  rcases state with ⟨remaining,cached,meaning⟩;cases remaining <;> simp [State.move,State.rank]
end Mapping

namespace Rows
variable {K A B : Type} (keys : List K) (source : K → List A) (term : K → A → ℚ) (emit : K → ℚ → B)
structure Cell (key : K) where
  private mk ::
  remaining : List A
  amount : ℚ
  balance : amount+(remaining.map (term key)).sum = ((source key).map (term key)).sum
def Cell.initial (key : K) : Cell source term key := ⟨source key,0,by simp⟩
structure Row (key : K) where
  private mk ::
  value : B
  exact_value : value = emit key (((source key).map (term key)).sum)
structure Job where
  key : K
  state : Cell source term key
abbrev Entry := (key : K) × Row source term emit key
def Job.initial (key : K) : Job source term := ⟨key,Cell.initial source term key⟩
def Job.rank (job : Job source term) := job.state.remaining.length+1
structure Completed where
  private mk ::
  items : List (Entry source term emit)
  exact_keys : items.map Sigma.fst = keys
structure Cursor where
  private mk ::
  remaining : List (Job source term)
  cached : List (Entry source term emit)
  coherent : cached.map Sigma.fst++remaining.map Job.key = keys

def initial : Cursor keys source term emit := ⟨keys.map (Job.initial source term),[],by simp [Function.comp_def,Job.initial]⟩
variable {keys source term emit}
def Cursor.rank (cursor : Cursor keys source term emit) := (cursor.remaining.map (Job.rank source term)).sum
inductive Event (K A : Type) where
  | read (key : K) (item : A)
  | emit (key : K)
def Cursor.move (cursor : Cursor keys source term emit) : Option (Event K A × Cursor keys source term emit) :=
  match actual : cursor.remaining with
  | [] => none
  | job::rest => match contents : job.state.remaining with
    | [] =>
        have value : job.state.amount = ((source job.key).map (term job.key)).sum := by
          simpa only [contents,List.map_nil,List.sum_nil,add_zero] using job.state.balance
        let row : Row source term emit job.key := ⟨emit job.key job.state.amount,congrArg (emit job.key) value⟩
        some (.emit job.key,⟨rest,cursor.cached++[⟨job.key,row⟩],by
          have known := cursor.coherent;rw [actual] at known
          simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using known⟩)
    | head::tail =>
        let next : Cell source term job.key := ⟨tail,job.state.amount+term job.key head,by
          have known := job.state.balance;rw [contents] at known
          simp only [List.map_cons,List.sum_cons] at known
          linarith⟩
        some (.read job.key head,⟨⟨job.key,next⟩::rest,cursor.cached,by
          have known := cursor.coherent;rw [actual] at known;simpa only [List.map_cons] using known⟩)
def Cursor.completed (cursor : Cursor keys source term emit) : Option (Completed keys source term emit) := match actual : cursor.remaining with
  | [] => some ⟨cursor.cached,by simpa only [actual,List.map_nil,List.append_nil] using cursor.coherent⟩
  | _::_ => none

theorem initial_rank : (initial keys source term emit).rank = (keys.map fun key => (source key).length+1).sum := by
  simp [initial,Cursor.rank,Job.rank,Job.initial,Cell.initial,Function.comp_def]
theorem Cursor.move_decreases {before after : Cursor keys source term emit} {event : Event K A}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  rcases before with ⟨remaining,cached,coherent⟩;cases remaining with
  | nil => cases actual
  | cons job rest =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i contents;cases actual
      simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank,contents,List.length_nil];omega
    · rename_i head tail contents;cases actual
      simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank,contents,List.length_cons];omega
theorem Cursor.completed_iff_stopped (cursor : Cursor keys source term emit) : cursor.completed.isSome = true ↔ cursor.move = none := by
  rcases cursor with ⟨remaining,cached,coherent⟩;cases remaining with
  | nil => simp [Cursor.completed,Cursor.move]
  | cons job rest =>
      simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
      dsimp only [Cursor.move];split <;> simp
theorem Cursor.stopped_iff_zero (cursor : Cursor keys source term emit) : cursor.move = none ↔ cursor.rank = 0 := by
  have finished := cursor.completed_iff_stopped
  rcases cursor with ⟨remaining,cached,coherent⟩;cases remaining with
  | nil => simp [Cursor.move,Cursor.rank]
  | cons job rest =>
      have active : (⟨job::rest,cached,coherent⟩ : Cursor keys source term emit).move ≠ none := by
        intro stopped;have impossible := finished.mpr stopped;simp [Cursor.completed] at impossible
      simp only [active,false_iff,Cursor.rank,List.map_cons,List.sum_cons,Job.rank];omega

variable [DecidableEq K]
def lookup (key : K) : (items : List (Entry source term emit)) → key ∈ items.map Sigma.fst → Row source term emit key
  | [],inside => False.elim (List.not_mem_nil inside)
  | head::tail,inside => if same : head.1 = key then same ▸ head.2 else lookup key tail (by
      simpa only [List.map_cons,List.mem_cons,eq_comm (a := key) (b := head.1),same,false_or] using inside)
def Completed.at (cache : Completed keys source term emit) (key : K) (inside : key ∈ keys) : Row source term emit key :=
  lookup key cache.items (by rw [cache.exact_keys];exact inside)
def Completed.values (cache : Completed keys source term emit) := cache.items.map fun entry => entry.2.value

omit [DecidableEq K] in
theorem Completed.values_exact (cache : Completed keys source term emit) : cache.values = keys.map (fun key => emit key (((source key).map (term key)).sum)) := by
  unfold Completed.values
  conv_rhs => rw [←cache.exact_keys,List.map_map]
  apply List.map_congr_left
  intro entry inside
  exact entry.2.exact_value
end Rows

def debt (slot : Slot (bound := bound)) := Identity.debtImage bound.source.code bound.source.input slot
abbrev Old := {values : List (Identity.DebtImage P G O (Mandate.State P T) I) // values = native.atStart.current.slots.map debt}
abbrev New := {values : List (Identity.DebtImage P G O (Mandate.State P T) I) // values = (native.atEnd.current.slots.drop native.atStart.current.slots.length).map debt}
abbrev ClaimKey := I × P × P
def claimKeys : List (ClaimKey (P := P) (I := I)) := bound.source.code.instruments.flatMap fun instrument =>
  bound.source.code.parties.flatMap fun debtor => bound.source.code.parties.map fun creditor => (instrument,debtor,creditor)
def claimSource (_key : ClaimKey (P := P) (I := I)) := native.atEnd.current.slots
def claimTerm (key : ClaimKey (P := P) (I := I)) (slot : Slot (bound := bound)) :=
  Financial.BalanceConservation.slotClaims bound.source.input slot key.1 key.2.1 key.2.2
def claimEmit (key : ClaimKey (P := P) (I := I)) (amount : ℚ) :=
  (Window.terminal bound start span).claims key.1 key.2.1 key.2.2-amount
abbrev Claims := Rows.Completed (claimKeys (bound := bound)) (claimSource native) (claimTerm (bound := bound)) (claimEmit (bound := bound) (start := start) (span := span))
abbrev ClaimCursor := Rows.Cursor (claimKeys (bound := bound)) (claimSource native) (claimTerm (bound := bound)) (claimEmit (bound := bound) (start := start) (span := span))

theorem claim_values_exact (cache : Claims native) : cache.values = native.unmatchedClaims := by
  rw [Rows.Completed.values_exact]
  simp only [claimKeys,List.map_flatMap,List.map_map,Function.comp_def,claimEmit,claimSource,
    Origin.Completed.unmatchedClaims,Financial.BalanceConservation.ledgerClaims]
  rfl

abbrev HoldingKey := Fin native.atStart.current.slots.length × P
def holderKeys (count : Nat) : List (Fin count × P) := (List.finRange count).flatMap fun index => bound.source.code.parties.map fun holder => (index,holder)
def holdingKeys : List (HoldingKey native) := holderKeys (bound := bound) native.atStart.current.slots.length
structure HoldingValue where
  owed : ℚ
  received : ℚ
  right : ℚ

def holdingSource (_key : HoldingKey native) := records native
def holdingTerm (key : HoldingKey native) := receivedTerm native key.1 key.2
def holdingEmit (key : HoldingKey native) (amount : ℚ) : HoldingValue :=
  let owed := Financial.slotBalance bound.source.input (finalSlot native key.1) key.2
  ⟨owed,amount,owed+amount⟩
abbrev Holdings := Rows.Completed (holdingKeys native) (holdingSource native) (holdingTerm native) (holdingEmit native)
abbrev HoldingCursor := Rows.Cursor (holdingKeys native) (holdingSource native) (holdingTerm native) (holdingEmit native)
theorem every_holder (index : Fin native.atStart.current.slots.length) (holder : P) : (index,holder) ∈ holdingKeys native := by
  exact List.mem_flatMap.mpr ⟨index,List.mem_finRange _,List.mem_map.mpr ⟨holder,bound.source.code.parties_cover holder,rfl⟩⟩
def holdingAt (cache : Holdings native) (index : Fin native.atStart.current.slots.length) (holder : P) : HoldingValue :=
  (cache.at (index,holder) (every_holder native index holder)).value

theorem holding_exact (cache : Holdings native) (index : Fin native.atStart.current.slots.length) (holder : P) :
    ((holdingAt native cache index holder).owed,(holdingAt native cache index holder).received) =
      (Financial.slotBalance bound.source.input (reference native index).slot holder,
        (reference native index).path.receivedBy bound.source.input holder) := by
  unfold holdingAt
  rw [(cache.at (index,holder) (every_holder native index holder)).exact_value]
  dsimp only [holdingEmit,holdingSource,holdingTerm]
  rw [finalSlot_exact,received_exact]
theorem right_exact (cache : Holdings native) (index : Fin native.atStart.current.slots.length) (holder : P) :
    (holdingAt native cache index holder).right =
      Financial.slotBalance bound.source.input (reference native index).slot holder+
        (reference native index).path.receivedBy bound.source.input holder := by
  unfold holdingAt
  rw [(cache.at (index,holder) (every_holder native index holder)).exact_value]
  dsimp only [holdingEmit,holdingSource,holdingTerm]
  rw [finalSlot_exact,received_exact]

def rights (cache : Holdings native) : List (List ℚ) := List.ofFn fun index : Fin native.atStart.current.slots.length =>
  bound.source.code.parties.map fun holder => (holdingAt native cache index holder).right

theorem rights_exact (cache : Holdings native) : rights native cache = Settlement.rights (Window.holdings bound start span) := by
  apply List.ext_getElem
  · simp only [rights,List.length_ofFn,Settlement.rights,Window.holdings,List.length_map]
    rw [native.start_exact]
  · intro index leftBound rightBound
    simp only [rights,List.getElem_ofFn,Settlement.rights,List.getElem_map,Window.holdings,List.getElem_ofFn,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro holder inside
    have bounded : index < native.atStart.current.slots.length := by simpa only [rights,List.length_ofFn] using leftBound
    exact right_exact native cache ⟨index,bounded⟩ holder

def unpaid (cache : Holdings native) (index : Nat) (holder : P) : ℚ :=
  if inside : index < native.atStart.current.slots.length then (holdingAt native cache ⟨index,inside⟩ holder).owed else 0

theorem unpaid_exact (cache : Holdings native) (index : Nat) (holder : P) :
    unpaid native cache index holder = Window.value bound start span (.unpaid index holder) := by
  change unpaid native cache index holder = (Settlement.holdingAt (Window.holdings bound start span) index (bound.source.code.parties.idxOf holder)).1
  unfold unpaid
  by_cases inside : index < native.atStart.current.slots.length
  · rw [dif_pos inside]
    have original : index < (Window.first bound start).current.slots.length := by simpa only [native.start_exact] using inside
    rw [Window.holding_is_the_actual_slot_and_receipt bound start span ⟨index,original⟩ holder]
    exact congrArg Prod.fst (holding_exact native cache ⟨index,inside⟩ holder)
  · rw [dif_neg inside]
    have absent : (Window.holdings bound start span)[index]? = none := by
      apply List.getElem?_eq_none
      simpa only [Window.holdings,List.length_ofFn,native.start_exact] using Nat.le_of_not_gt inside
    unfold Settlement.holdingAt
    rw [absent]
    rfl

def newCost := (native.atEnd.current.slots.drop native.atStart.current.slots.length).length
def claimCost := ((claimKeys (bound := bound)).map fun _ => native.atEnd.current.slots.length+1).sum
def holdingCost := ((holdingKeys native).map fun _ => (records native).length+1).sum

def footprint (first last : Ledger bound) := first.current.slots.length+
  (last.current.slots.drop first.current.slots.length).length+
  ((claimKeys (bound := bound)).map fun _ => last.current.slots.length+1).sum+
  ((holderKeys (bound := bound) first.current.slots.length).map fun _ => (last.current.history.drop first.current.history.length).length+1).sum+3
noncomputable def capacity (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) :=
  footprint (bound := bound) (Window.first bound start) (Window.last bound start span)

def initialClaims : ClaimCursor native := Rows.initial _ _ _ _
def initialHoldings : HoldingCursor native := Rows.initial _ _ _ _
theorem initialClaims_rank : (initialClaims native).rank = claimCost native := by rw [initialClaims,Rows.initial_rank];rfl
theorem initialHoldings_rank : (initialHoldings native).rank = holdingCost native := by rw [initialHoldings,Rows.initial_rank];rfl
structure Completed where
  private mk ::
  original : Old native
  newborn : New native
  claims : Claims native
  holdings : Holdings native
inductive Cursor where
  | original (state : Mapping.State (debt (bound := bound)) native.atStart.current.slots)
  | newborn (old : Old native) (state : Mapping.State (debt (bound := bound)) (native.atEnd.current.slots.drop native.atStart.current.slots.length))
  | claims (old : Old native) (fresh : New native) (state : ClaimCursor native)
  | holdings (old : Old native) (fresh : New native) (claims : Claims native) (state : HoldingCursor native)
def initial : Cursor native := .original (Mapping.initial _ _)
variable {native}
def Cursor.rank : Cursor native → Nat
  | .original state => state.rank+newCost native+claimCost native+holdingCost native+3
  | .newborn _ state => state.rank+claimCost native+holdingCost native+2
  | .claims _ _ state => state.rank+holdingCost native+1
  | .holdings _ _ _ state => state.rank
inductive Event (native : Origin.Completed bound start span) where
  | original (slot : Slot (bound := bound))
  | beginNewborn
  | newborn (slot : Slot (bound := bound))
  | beginClaims
  | claim (event : Rows.Event (ClaimKey (P := P) (I := I)) (Slot (bound := bound)))
  | beginHoldings
  | holding (event : Rows.Event (HoldingKey native) (Record (bound := bound)))

def Cursor.move : Cursor native → Option (Event native × Cursor native)
  | .original state => match state.completed with
    | some old => some (.beginNewborn,.newborn old (Mapping.initial _ _))
    | none => state.move.map fun (event,next) => (.original event,.original next)
  | .newborn old state => match state.completed with
    | some fresh => some (.beginClaims,.claims old fresh (initialClaims native))
    | none => state.move.map fun (event,next) => (.newborn event,.newborn old next)
  | .claims old fresh state => match state.completed with
    | some collected => some (.beginHoldings,.holdings old fresh collected (initialHoldings native))
    | none => state.move.map fun (event,next) => (.claim event,.claims old fresh next)
  | .holdings old fresh collected state => state.move.map fun (event,next) => (.holding event,.holdings old fresh collected next)
def Cursor.completed : Cursor native → Option (Completed native)
  | .original _ | .newborn _ _ | .claims _ _ _ => none
  | .holdings old fresh collected state => state.completed.map fun held => ⟨old,fresh,collected,held⟩

theorem initial_rank : (initial native).rank = capacity bound start span := by
  change footprint native.atStart native.atEnd = footprint (Window.first bound start) (Window.last bound start span)
  rw [native.start_exact,native.end_exact]

theorem Cursor.move_decreases {before after : Cursor native} {event : Event native}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | original state =>
    dsimp only [Cursor.move] at actual;split at actual
    · rename_i old done;cases actual
      have zero := (Mapping.State.stopped_iff_zero state).mp ((Mapping.State.completed_iff_stopped _).mp (by rw [done];rfl))
      change (newCost native+claimCost native+holdingCost native+2)+1 = state.rank+newCost native+claimCost native+holdingCost native+3
      rw [zero];omega
    · rename_i pending
      cases moved : state.move with
      | none => simp only [moved,Option.map_none,reduceCtorEq] at actual
      | some pair =>
        rcases pair with ⟨event,next⟩;rw [moved] at actual;cases actual
        have := Mapping.State.move_decreases moved;dsimp only [Cursor.rank];omega
  | newborn old state =>
    dsimp only [Cursor.move] at actual;split at actual
    · rename_i fresh done;cases actual
      have zero := (Mapping.State.stopped_iff_zero state).mp ((Mapping.State.completed_iff_stopped _).mp (by rw [done];rfl))
      simp only [Cursor.rank,initialClaims_rank,zero];omega
    · rename_i pending
      cases moved : state.move with
      | none => simp only [moved,Option.map_none,reduceCtorEq] at actual
      | some pair =>
        rcases pair with ⟨event,next⟩;rw [moved] at actual;cases actual
        have := Mapping.State.move_decreases moved;dsimp only [Cursor.rank];omega
  | claims old fresh state =>
    dsimp only [Cursor.move] at actual;split at actual
    · rename_i collected done;cases actual
      have zero := (Rows.Cursor.stopped_iff_zero state).mp ((Rows.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
      simp only [Cursor.rank,initialHoldings_rank,zero];omega
    · rename_i pending
      cases moved : state.move with
      | none => simp only [moved,Option.map_none,reduceCtorEq] at actual
      | some pair =>
        rcases pair with ⟨event,next⟩;rw [moved] at actual;cases actual
        have := Rows.Cursor.move_decreases moved;dsimp only [Cursor.rank];omega
  | holdings old fresh collected state =>
    dsimp only [Cursor.move] at actual
    cases moved : state.move with
    | none => simp only [moved,Option.map_none,reduceCtorEq] at actual
    | some pair =>
        rcases pair with ⟨event,next⟩;rw [moved] at actual;cases actual
        exact Rows.Cursor.move_decreases moved

theorem Cursor.completed_iff_stopped (cursor : Cursor native) : cursor.completed.isSome = true ↔ cursor.move = none := by
  cases cursor with
  | original state =>
      have same := Mapping.State.completed_iff_stopped state
      cases done : state.completed <;> cases moved : state.move <;> simp [Cursor.completed,Cursor.move,done,moved] at *
  | newborn old state =>
      have same := Mapping.State.completed_iff_stopped state
      cases done : state.completed <;> cases moved : state.move <;> simp [Cursor.completed,Cursor.move,done,moved] at *
  | claims old fresh state =>
      have same := Rows.Cursor.completed_iff_stopped state
      cases done : state.completed <;> cases moved : state.move <;> simp [Cursor.completed,Cursor.move,done,moved] at *
  | holdings old fresh collected state =>
      have same := Rows.Cursor.completed_iff_stopped state
      cases done : state.completed <;> cases moved : state.move <;> simp [Cursor.completed,Cursor.move,done,moved] at *
theorem Cursor.stopped_iff_zero (cursor : Cursor native) : cursor.move = none ↔ cursor.rank = 0 := by
  cases cursor with
  | original state =>
    have active : (Cursor.original state).move ≠ none := by intro stopped;have impossible := (Cursor.completed_iff_stopped _).mpr stopped;cases impossible
    simp only [active,false_iff,Cursor.rank];omega
  | newborn old state =>
    have active : (Cursor.newborn old state).move ≠ none := by intro stopped;have impossible := (Cursor.completed_iff_stopped _).mpr stopped;cases impossible
    simp only [active,false_iff,Cursor.rank];omega
  | claims old fresh state =>
    have active : (Cursor.claims old fresh state).move ≠ none := by intro stopped;have impossible := (Cursor.completed_iff_stopped _).mpr stopped;cases impossible
    simp only [active,false_iff,Cursor.rank];omega
  | holdings old fresh collected state =>
    have same : (Cursor.holdings old fresh collected state).move = none ↔ state.move = none := by cases actual : state.move <;> simp [Cursor.move,actual]
    rw [same];exact Rows.Cursor.stopped_iff_zero state

inductive History : Cursor native → Cursor native → List (Event native) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor native) (capacity : Nat) where
  private mk ::
  endpoint : Cursor native
  work : List (Event native)
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank

def run : (capacity : Nat) → (before : Cursor native) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩
theorem run_sufficient (before : Cursor native) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega

theorem run_work_exact (before : Cursor native) (available : Nat) :
    (run available before).work.length = min available before.rank := by
  have covered := (run available before).covered
  have conserved := (run available before).conservation
  rcases (run available before).exhausted with stopped | full
  · have zero := (Cursor.stopped_iff_zero _).mp stopped
    rw [zero] at conserved
    have same : (run available before).work.length = before.rank := by omega
    rw [same,Nat.min_eq_right (by omega)]
  · rw [full,Nat.min_eq_left (by omega)]


def Completed.originalDebts (cache : Completed native) := cache.original.val
def Completed.admittedDebts (cache : Completed native) := cache.newborn.val
def Completed.unmatchedClaims (cache : Completed native) := cache.claims.values
def Completed.rights (cache : Completed native) := Fields.rights native cache.holdings
def Completed.unpaid (cache : Completed native) := Fields.unpaid native cache.holdings

theorem Completed.originalDebts_exact (cache : Completed native) : cache.originalDebts =
    Identity.financeImage bound.source.code bound.source.input (Window.first bound start) := by
  have same : cache.originalDebts = native.originalDebts := cache.original.property
  exact same.trans native.originalDebts_exact
theorem Completed.admittedDebts_exact (cache : Completed native) : cache.admittedDebts =
    (Identity.financeImage bound.source.code bound.source.input (Window.last bound start span)).drop (Window.first bound start).current.slots.length := by
  have same : cache.admittedDebts = native.admittedDebts := by
    change cache.newborn.val = (native.atEnd.current.slots.map (debt (bound := bound))).drop native.atStart.current.slots.length
    rw [←List.map_drop]
    exact cache.newborn.property
  exact same.trans native.admittedDebts_exact
theorem Completed.unmatchedClaims_exact (cache : Completed native) : cache.unmatchedClaims =
    bound.source.code.instruments.flatMap (fun instrument => bound.source.code.parties.flatMap fun debtor =>
      bound.source.code.parties.map fun creditor => (Window.terminal bound start span).claims instrument debtor creditor-
        Financial.BalanceConservation.ledgerClaims bound.source.input (Window.last bound start span).current instrument debtor creditor) :=
  (claim_values_exact native cache.claims).trans native.unmatchedClaims_exact
theorem Completed.rights_exact (cache : Completed native) : cache.rights = Settlement.rights (Window.holdings bound start span) := Fields.rights_exact native cache.holdings
theorem Completed.unpaid_exact (cache : Completed native) (index : Nat) (holder : P) : cache.unpaid index holder = Window.value bound start span (.unpaid index holder) := Fields.unpaid_exact native cache.holdings index holder

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance.Fields
