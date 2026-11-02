import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Work.Core
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Bound
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue)
abbrev CellScope (index : Index prepared) := Policy.Budget.CellScope prepared index

inductive Event where
  | parent (event : Policy.Budget.Event prepared)
  | literal (value : Nat)
  | add (left right value : Nat)
  | multiply (left right value : Nat)
  | maximum (left right value : Nat)
  | queryInputs (query : Work.Query pool)
  | nativeEmission (index : Index prepared) (event : NativeTensor.Event P G O T I)
  | futureInputs (index : Index prepared) (scope : CellScope index) (intent : Whole.Intent scope)
      (rival : Opponent (initial input prepared.saved[index].point).source.val.code)
      (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model))
  | domain (queries : List (Work.Query pool))
  | branch
  | reuse (slot value : Nat)

def Event.Valid : Event pool → Prop
  | .parent event => event.Valid prepared
  | .add left right value => value = left+right
  | .multiply left right value => value = left*right
  | .maximum left right value => value = max left right
  | _ => True
structure Run (expected : Nat) where
  private mk ::
  value : Nat
  exact : value = expected
  work : List (Event pool)
  sound : ∀ event ∈ work,event.Valid pool
variable {pool}
def lift {n : Nat} (made : Policy.Budget.Run prepared n) : Run pool n :=
  ⟨made.value,made.exact,made.work.map Event.parent,by
    intro event inside
    obtain ⟨original,listed,same⟩ := List.mem_map.mp inside
    subst event;exact made.sound original listed⟩
def lit (n : Nat) : Run pool n := ⟨n,rfl,[.literal n],by simp [Event.Valid]⟩
private def combine {a b c : Nat} (left : Run pool a) (right : Run pool b)
    (result : Nat) (exact : result = c) (event : Event pool) (valid : event.Valid pool) : Run pool c :=
  ⟨result,exact,left.work ++ right.work ++ [event],by
    intro item inside
    rcases List.mem_append.mp inside with earlier | last
    · rcases List.mem_append.mp earlier with first | second
      · exact left.sound item first
      · exact right.sound item second
    · have same := List.mem_singleton.mp last
      subst item;exact valid⟩
def plus {a b : Nat} (left : Run pool a) (right : Run pool b) : Run pool (a+b) :=
  combine left right (left.value+right.value) (by rw [left.exact,right.exact]) (.add left.value right.value (left.value+right.value)) rfl
def times {a b : Nat} (left : Run pool a) (right : Run pool b) : Run pool (a*b) :=
  combine left right (left.value*right.value) (by rw [left.exact,right.exact]) (.multiply left.value right.value (left.value*right.value)) rfl
def largest {a b : Nat} (left : Run pool a) (right : Run pool b) : Run pool (max a b) :=
  combine left right (max left.value right.value) (by rw [left.exact,right.exact]) (.maximum left.value right.value (max left.value right.value)) rfl
def borrow {n : Nat} (slot : Nat) (made : Run pool n) : Run pool n :=
  ⟨made.value,made.exact,[.reuse slot made.value],by simp [Event.Valid]⟩
def retain {a b : Nat} (earlier : Run pool a) (later : Run pool b) : Run pool b :=
  ⟨later.value,later.exact,earlier.work ++ later.work,by
    intro event inside
    rcases List.mem_append.mp inside with first | second
    · exact earlier.sound event first
    · exact later.sound event second⟩
def annotate {n : Nat} (event : Event pool) (valid : event.Valid pool) (made : Run pool n) : Run pool n :=
  ⟨made.value,made.exact,event::made.work,by
    intro item inside
    rcases List.mem_cons.mp inside with same | rest
    · subst item;exact valid
    · exact made.sound item rest⟩
def emissions {n : Nat} (index : Index prepared) (work : List (NativeTensor.Event P G O T I)) (made : Run pool n) : Run pool n :=
  ⟨made.value,made.exact,work.map (.nativeEmission index) ++ made.work,by
    intro event inside
    rcases List.mem_append.mp inside with native | later
    · obtain ⟨_,_,same⟩ := List.mem_map.mp native;subst event;trivial
    · exact made.sound event later⟩
local infixl:65 " ⊞ " => plus
local infixl:70 " ⊠ " => times

variable (pool)
def ceiling {α : Type} (cost : α → Nat) (run : (item : α) → Run pool (cost item)) :
    (items : List α) → Run pool (Policy.Work.ceiling cost items)
  | [] => annotate .branch (by trivial) (lit 0)
  | head::tail => annotate .branch (by trivial) (largest (run head) (ceiling cost run tail))

def presentSource (index : Index prepared) (scope : CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code) :
    Run pool (Whole.Materialization.presentBudget scope input.span intent rival) :=
  lift (Policy.Budget.NativeSourceShape.evaluation prepared (Whole.Materialization.bound scope input.span intent rival)
    (initial input prepared.saved[index].point).depth (Whole.extent scope input.span intent))

structure FutureEmission (index : Index prepared) (scope : CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code)
    (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model)) where
  private mk ::
  value : Option (Future.Recovery.Assessment.Report (initial input prepared.saved[index].point).model)
  work : List (NativeTensor.Event P G O T I)
  budget : Run pool (Whole.Materialization.futureBudget scope input.span intent rival word)
  value_exact : value = (Whole.Materialization.future scope input.span intent rival word).value
  work_exact : work = (Whole.Materialization.future scope input.span intent rival word).work

def futureSource (index : Index prepared) (scope : CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code)
    (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model)) :
    FutureEmission pool index scope intent rival word :=
  let source := Whole.target scope input.span intent rival
  match actual : Future.produce (initial input prepared.saved[index].point).model
      (initial input prepared.saved[index].point).depth source.indexed (Whole.count scope input.span intent) word with
  | .inl _ => by
    dsimp only [source] at actual
    have cost : Run pool (Whole.Materialization.futureBudget scope input.span intent rival word) := by
      simpa only [Whole.Materialization.futureBudget,actual] using (lit 0 : Run pool 0)
    exact ⟨none,[],annotate (.futureInputs index scope intent rival word) (by trivial) cost,
      by simp only [Whole.Materialization.future,actual],by simp only [Whole.Materialization.future,actual]⟩
  | .inr receipt => by
    dsimp only [source] at actual
    let restored := Future.Recovery.produceWith (old := (initial input prepared.saved[index].point).model) input.pricing receipt
    let emitted := NativeTensor.report restored (initial input prepared.saved[index].point).depth source.property
    let calculated := lift (pool := pool) (Policy.Budget.NativeSourceShape.evaluation prepared restored.bound
      (initial input prepared.saved[index].point).depth (restored.walk.finish.depth-(initial input prepared.saved[index].point).depth))
    have cost : Run pool (Whole.Materialization.futureBudget scope input.span intent rival word) := by
      simpa only [Whole.Materialization.futureBudget,actual,NativeTensor.reportBudget] using calculated
    exact ⟨some emitted.value,emitted.work,annotate (.futureInputs index scope intent rival word) (by trivial) cost,
      by simp only [Whole.Materialization.future,actual];rfl,by simp only [Whole.Materialization.future,actual];rfl⟩

def atom (query : Work.Query pool) : Run pool (Work.atomBudget pool query) :=
  annotate (.queryInputs query) (by trivial) (match query with
  | .admission policy row => match row with
    | .coherence first second => lit 1 ⊞ lift (Policy.Budget.signature
        (Policy.Work.cachedShape (.ready (read pool policy first).scope) (read pool policy first).intent)
        (Policy.Work.cachedShape (.ready (read pool policy second).scope) (read pool policy second).intent))
    | .native index coordinate => match coordinate with
      | .present table =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := Whole.Materialization.present branch.scope input.span branch.intent rival
        let original := Whole.Materialization.present branch.scope input.span .keep rival
        emissions index (current.work++original.work)
          (lit 1 ⊞ presentSource pool index branch.scope branch.intent rival ⊞ presentSource pool index branch.scope .keep rival ⊞
            lift (Policy.Budget.PresentShape.present prepared (initial input prepared.saved[index].point) current.value original.value))
      | .future table word =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := futureSource pool index branch.scope branch.intent rival word
        let original := futureSource pool index branch.scope .keep rival word
        let made := lit 1 ⊞ current.budget ⊞ original.budget ⊞
          lift (Policy.Budget.NativeFutureShape.comparison prepared (initial input prepared.saved[index].point) current.value original.value)
        ⟨made.value,by simpa only [Work.atomBudget,current.value_exact,original.value_exact] using made.exact,
          (emissions index (current.work++original.work) made).work,(emissions index (current.work++original.work) made).sound⟩
      | .funding .. => lit 4
      | .release | .coverage | .deployment => lit 1
    | .informed | .uniform .. => lit 1
  | .present new previous index table =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := Whole.Materialization.present left.scope input.span left.intent rival
    let original := Whole.Materialization.present right.scope input.span right.intent rival
    emissions index (current.work++original.work)
      (lit 1 ⊞ presentSource pool index left.scope left.intent rival ⊞ presentSource pool index right.scope right.intent rival ⊞
        lift (Policy.Budget.NativeBenefitShape.present prepared (initial input prepared.saved[index].point) current.value original.value))
  | .future new previous index table word =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := futureSource pool index left.scope left.intent rival word
    let original := futureSource pool index right.scope right.intent rival word
    let made := lit 1 ⊞ current.budget ⊞ original.budget ⊞
      lift (Policy.Budget.NativeBenefitShape.future prepared (initial input prepared.saved[index].point) current.value original.value)
    ⟨made.value,by simpa only [Work.atomBudget,current.value_exact,original.value_exact] using made.exact,
      (emissions index (current.work++original.work) made).work,(emissions index (current.work++original.work) made).sound⟩
  | .funding .. => lit 4)

def generate : Run pool (Work.workBudget pool) :=
  let count : Run pool (sections pool).length := lift (Policy.Budget.length (sections pool))
  let atoms := annotate (.domain (Work.queries pool)) (by trivial)
    (ceiling pool (Work.atomBudget pool) (atom pool) (Work.queries pool))
  let tables := ceiling pool (fun index : Index prepared => (Comparison.tables pool index).length)
    (fun index => lift (Policy.Budget.length (Comparison.tables pool index))) (keys prepared)
  let words := ceiling pool (fun index : Index prepared => (Work.capabilityWords index).length)
    (fun index => lift (Policy.Budget.length (Work.capabilityWords index))) (keys prepared)
  let admission := lift (Policy.Budget.length (rows pool)) ⊠ (borrow 0 atoms ⊞ lit 1)
  let benefit := lift (Policy.Budget.length (keys prepared)) ⊠
    (borrow 1 tables ⊠ (borrow 0 atoms ⊞ lit 3 ⊞ lit 2 ⊠ borrow 2 words ⊠ (borrow 0 atoms ⊞ lit 1)) ⊞ lit 1)
  let strict := lit 2 ⊠ borrow 4 benefit ⊞ lit 2
  let verification := borrow 3 admission ⊞ lit 1 ⊞ (borrow 5 count ⊠ (borrow 3 admission ⊞ borrow 6 strict ⊞ lit 3))
  let result := borrow 5 count ⊠ (borrow 3 admission ⊞ lit 1) ⊞
    borrow 5 count ⊠ (borrow 6 strict ⊞ lit 1) ⊞ borrow 7 verification ⊞ borrow 5 count ⊠ borrow 3 admission ⊞ lit 1
  retain count (retain atoms (retain tables (retain words (retain admission (retain benefit (retain strict (retain verification result)))))))

theorem generated_budget_is_original_and_all_operations_are_valid :
    (generate pool).value = Work.workBudget pool ∧ ∀ event ∈ (generate pool).work,event.Valid pool :=
  ⟨(generate pool).exact,(generate pool).sound⟩
theorem generated_budget_covers_every_complete_planner_and_replay
    (order : List (Section pool)) (complete : order.Perm (sections pool))
    (receipt : Work.Receipt pool (Work.compileOrdered pool order complete)) :
    receipt.work.length ≤ (generate pool).value := by
  rw [(generate pool).exact]
  exact Work.receipt_work_fits_the_source_budget pool order complete receipt

inductive Debt where
  | prior (debt : Comparison.Pool.Debt pool)
  | budgetEvent (event : Event pool)
  | enumeration
  | primitiveInternals
  | quoteAndPrepayment
  | storage
  | announcement

def pending : List (Debt pool) := pool.pending.map Debt.prior ++ (generate pool).work.map Debt.budgetEvent ++
  [.enumeration,.primitiveInternals,.quoteAndPrepayment,.storage,.announcement]

theorem every_budget_event_retains_its_full_payload (event : Event pool) (inside : event ∈ (generate pool).work) :
    Debt.budgetEvent event ∈ pending pool :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨event,inside,rfl⟩))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Bound
