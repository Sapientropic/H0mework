import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Arithmetic
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {point : NativePoint input}

abbrev Scope := PaidBudgetArithmetic.OriginalScope (input := input)
abbrev feePoint (scope : Scope point) := Prefix.pointFor (Whole.paidPoint scope) scope.continuation.words

private theorem registered_is_public (scope : Scope point) (fee : Future.Recovery.Action (feePoint scope).model)
    (registered : feeAt (feePoint scope) input.actor input.position = some fee) :
    IsWorkFee (feePoint scope) input.actor fee := by
  unfold feeAt at registered
  split at registered
  · cases registered
  · split at registered
    · rename_i lawful
      cases registered
      exact lawful
    · cases registered

structure Fee (scope : Scope point) where
  private mk ::
  request : Future.Recovery.Action (feePoint scope).model
  registered : feeAt (feePoint scope) input.actor input.position = some request
  bearer : P
  bundle : Bundle G
  operation : request.operation = .use bearer bundle .external
  personal : bearer = input.actor
  nonnegative : NonnegativeBundle G bundle
  positive : ∃ good ∈ (feePoint scope).source.val.code.goods,0 < amount G bundle good

inductive Reading (scope : Scope point) where
  | absent (why : feeAt (feePoint scope) input.actor input.position = none)
  | found (fee : Fee scope)

def read (scope : Scope point) : Reading scope :=
  match registered : feeAt (feePoint scope) input.actor input.position with
  | none => .absent registered
  | some fee =>
      have lawful := registered_is_public scope fee registered
      match operation : fee.operation with
      | .use bearer bundle purpose =>
          match purpose with
          | .external =>
              have shape : bearer = input.actor ∧ NonnegativeBundle G bundle ∧
                  ∃ good ∈ (feePoint scope).source.val.code.goods,0 < amount G bundle good := by
                unfold IsWorkFee at lawful
                rw [operation] at lawful
                exact lawful.2.2.2
              .found ⟨fee,registered,bearer,bundle,operation,shape.1,shape.2.1,shape.2.2⟩
          | .necessity | .maintenance | .investment | .contribution => False.elim (by
              unfold IsWorkFee at lawful
              rw [operation] at lawful
              exact lawful.2.2.2)
      | .produce _ | .transfer _ _ _ | .issue _ _ _ _ | .assign _ _ _ _ _ | .settle _ _ _ _ | .revise _ _ | .present =>
          False.elim (by unfold IsWorkFee at lawful;rw [operation] at lawful;exact lawful.2.2.2)

namespace Fee
variable {scope : Scope point} (fee : Fee scope)
def keys : List G := fee.bundle.map Prod.fst
def unit (good : G) : ℚ := amount G fee.bundle good
def stock (good : G) : ℚ := (feePoint scope).state.current.stock fee.bearer good

theorem unit_nonnegative (good : G) : 0 ≤ fee.unit good := amount_nonnegative fee.bundle fee.nonnegative good

theorem positive_keys_exist : ∃ good ∈ fee.keys,0 < fee.unit good := by
  obtain ⟨good,_,positive⟩ := fee.positive
  refine ⟨good,?_,positive⟩
  by_contra absent
  have zero := amount_zero_of_absent fee.bundle good (by
    intro entry inside same
    exact absent (List.mem_map.mpr ⟨entry,inside,same⟩))
  change 0 < amount G fee.bundle good at positive
  rw [zero] at positive
  exact (lt_irrefl _ positive)

structure Entry where
  private mk ::
  good : G
  listed : good ∈ fee.keys
  positive : 0 < fee.unit good

def Entry.item {fee : Fee scope} (entry : Entry fee) : Item := ⟨fee.stock entry.good,fee.unit entry.good,entry.positive⟩

def entries : List (Entry fee) :=
  fee.keys.attach.filterMap fun key =>
    if positive : 0 < fee.unit key.val then some ⟨key.val,key.property,positive⟩ else none

theorem each_positive_key_is_represented (good : G) (inside : good ∈ fee.keys) (positive : 0 < fee.unit good) :
    ∃ entry ∈ fee.entries,entry.good = good := by
  refine ⟨⟨good,inside,positive⟩,?_,rfl⟩
  exact List.mem_filterMap.mpr ⟨⟨good,inside⟩,List.mem_attach _ _,by simp only [dif_pos positive]⟩

theorem entries_nonempty : fee.entries ≠ [] := by
  obtain ⟨good,inside,positive⟩ := fee.positive_keys_exist
  obtain ⟨entry,member,_⟩ := fee.each_positive_key_is_represented good inside positive
  intro empty
  rw [empty] at member
  cases member

def Fits (count : Nat) : Prop := ∀ good ∈ fee.keys,(count:ℚ)*fee.unit good ≤ fee.stock good

theorem scaled_fee_keeps_its_actual_replay_request (count : Nat) :
    Mandate.Replay.rebase (feePoint scope).model.scope (feePoint scope).state.current
      (Prepaid.scaled (feePoint scope) fee.request count) = Prepaid.scaled (feePoint scope) fee.request count := by
  simp only [Prepaid.scaled,fee.operation,Mandate.Replay.rebase]

def debit (count : Nat) :=
  (Mandate.law (feePoint scope).model.base (feePoint scope).model.scope).debit (feePoint scope).state.current
    (Prepaid.scaled (feePoint scope) fee.request count)

theorem actual_debit (count : Nat) : fee.debit count =
    locate fee.bearer (fee.bundle.map fun entry => (entry.1,(count:ℚ)*entry.2)) := by
  simp only [debit,Prepaid.scaled,fee.operation,RawLaw.debit]

def MaterialGate (count : Nat) : Prop :=
  ∀ entry ∈ fee.debit count,flowAt (fee.debit count) entry.1.1 entry.1.2 ≤
    (feePoint scope).state.current.stock entry.1.1 entry.1.2

theorem fits_is_the_original_material_gate (count : Nat) : fee.Fits count ↔ fee.MaterialGate count := by
  have charge (good : G) : flowAt (fee.debit count) fee.bearer good = (count:ℚ)*fee.unit good := by
    rw [fee.actual_debit,located_amount,scaled_amount]
    rfl
  constructor
  · intro fits entry inside
    rw [fee.actual_debit] at inside
    obtain ⟨scaled,scaledIn,same⟩ := List.mem_map.mp inside
    obtain ⟨original,originalIn,scaledExact⟩ := List.mem_map.mp scaledIn
    subst scaled
    subst entry
    rw [charge]
    exact fits original.1 (List.mem_map.mpr ⟨original,originalIn,rfl⟩)
  · intro gate good inside
    obtain ⟨original,originalIn,same⟩ := List.mem_map.mp inside
    subst good
    have member : ((fee.bearer,original.1),(count:ℚ)*original.2) ∈ fee.debit count := by
      rw [fee.actual_debit]
      exact List.mem_map.mpr ⟨(original.1,(count:ℚ)*original.2),List.mem_map.mpr ⟨original,originalIn,rfl⟩,rfl⟩
    have paid := gate _ member
    rw [charge] at paid
    exact paid

def Legal (count : Nat) : Prop :=
  (Mandate.law (feePoint scope).model.base (feePoint scope).model.scope).Valid
    (feePoint scope).state.current (Prepaid.scaled (feePoint scope) fee.request count)

theorem legal_has_original_material_gate (count : Nat) (legal : fee.Legal count) : fee.MaterialGate count :=
  legal.2.2.2.2.2

structure Available where
  private mk ::
  first : Entry fee
  rest : List (Entry fee)
  generated : fee.entries = first::rest
  nonnegative : ∀ good ∈ fee.keys,0 ≤ fee.stock good

namespace Available
variable {fee : Fee scope} (made : Available fee)
def units : Nat := capacity made.first.item (made.rest.map Entry.item)

theorem exact_capacity (count : Nat) : count ≤ made.units ↔ fee.Fits count := by
  have sane : ∀ item ∈ made.first.item::made.rest.map Entry.item,0 ≤ item.stock := by
    intro item inside
    rcases List.mem_cons.mp inside with same | later
    · subst item;exact made.nonnegative made.first.good made.first.listed
    · obtain ⟨entry,_,same⟩ := List.mem_map.mp later
      subst item;exact made.nonnegative entry.good entry.listed
  have exact := capacity_exact made.first.item (made.rest.map Entry.item) sane count
  constructor
  · intro bounded good inside
    have all := exact.mp bounded
    by_cases positive : 0 < fee.unit good
    · obtain ⟨entry,member,key⟩ := fee.each_positive_key_is_represented good inside positive
      rw [made.generated] at member
      have represented : entry.item ∈ made.first.item::made.rest.map Entry.item := by
        rcases List.mem_cons.mp member with same | later
        · subst entry;exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry,later,rfl⟩)
      simpa only [Entry.item,key] using all entry.item represented
    · have zero : fee.unit good = 0 := le_antisymm (le_of_not_gt positive) (fee.unit_nonnegative good)
      rw [zero,mul_zero]
      exact made.nonnegative good inside
  · intro all
    apply exact.mpr
    intro item inside
    rcases List.mem_cons.mp inside with same | later
    · subst item;exact all made.first.good made.first.listed
    · obtain ⟨entry,_,same⟩ := List.mem_map.mp later
      subst item;exact all entry.good entry.listed

theorem exact_source_debit_capacity (count : Nat) : count ≤ made.units ↔ fee.MaterialGate count :=
  (made.exact_capacity count).trans (fee.fits_is_the_original_material_gate count)

theorem every_legal_scaled_fee_is_in_the_generated_capacity (count : Nat)
    (accepted : (Mandate.law (feePoint scope).model.base (feePoint scope).model.scope).Valid
      (feePoint scope).state.current (Prepaid.scaled (feePoint scope) fee.request count)) : count ≤ made.units :=
  (made.exact_source_debit_capacity count).mpr accepted.2.2.2.2.2

theorem next_unit_has_a_named_stock_shortage :
    ∃ good ∈ fee.keys,fee.stock good < ((made.units+1:Nat):ℚ)*fee.unit good := by
  obtain ⟨item,inside,short⟩ := next_unit_exposes_a_real_stock_shortage made.first.item (made.rest.map Entry.item)
  rcases List.mem_cons.mp inside with same | later
  · subst item;exact ⟨made.first.good,made.first.listed,short⟩
  · obtain ⟨entry,_,same⟩ := List.mem_map.mp later
    subst item;exact ⟨entry.good,entry.listed,short⟩
end Available

inductive Analysis where
  | negative (good : G) (listed : good ∈ fee.keys) (broken : fee.stock good < 0)
  | available (made : Available fee)

def analyse : Analysis fee :=
  match Distributed.inspect (fun good => 0 ≤ fee.stock good) fee.keys with
  | .rejected good listed broken => .negative good listed (lt_of_not_ge broken)
  | .accepted nonnegative =>
      match generated : fee.entries with
      | [] => False.elim (fee.entries_nonempty generated)
      | first::rest => .available ⟨first,rest,generated,nonnegative⟩

theorem negative_stock_prevents_every_payment (good : G) (listed : good ∈ fee.keys)
    (broken : fee.stock good < 0) (count : Nat) : ¬ fee.Fits count := by
  intro fits
  have nonnegative := mul_nonneg (Nat.cast_nonneg (α := ℚ) count) (fee.unit_nonnegative good)
  have affordable := fits good listed
  linarith
end Fee
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota
