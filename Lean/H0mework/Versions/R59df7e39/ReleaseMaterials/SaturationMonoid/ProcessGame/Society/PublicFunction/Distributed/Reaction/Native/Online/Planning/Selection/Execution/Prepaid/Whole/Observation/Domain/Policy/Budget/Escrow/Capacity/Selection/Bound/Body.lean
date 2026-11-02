import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Bound.Body.Native
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Work
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Body
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue)
local infixl:65 " ⊞ " => fun a b : Nat => a+b+1
local infixl:70 " ⊠ " => fun a b : Nat => a+b+1

variable {pool}
theorem lift_units {n : Nat} (made : Budget.Run prepared n) : (Bound.lift (pool := pool) made).work.length = made.work.length := by
  change (made.work.map Bound.Event.parent).length = _
  exact List.length_map _
theorem literal_units (n : Nat) : (Bound.lit (pool := pool) n).work.length = 1 := rfl
theorem plus_units {a b : Nat} (left : Bound.Run pool a) (right : Bound.Run pool b) :
    (Bound.plus left right).work.length = left.work.length+right.work.length+1 := by
  change (left.work++right.work++[_]).length = _
  simp only [List.length_append,List.length_singleton]
theorem times_units {a b : Nat} (left : Bound.Run pool a) (right : Bound.Run pool b) :
    (Bound.times left right).work.length = left.work.length+right.work.length+1 := by
  change (left.work++right.work++[_]).length = _
  simp only [List.length_append,List.length_singleton]
theorem largest_units {a b : Nat} (left : Bound.Run pool a) (right : Bound.Run pool b) :
    (Bound.largest left right).work.length = left.work.length+right.work.length+1 := by
  change (left.work++right.work++[_]).length = _
  simp only [List.length_append,List.length_singleton]
theorem annotate_units {n : Nat} (event : Bound.Event pool) (valid : event.Valid pool) (made : Bound.Run pool n) :
    (Bound.annotate event valid made).work.length = made.work.length+1 := by
  change (event::made.work).length = _
  simp only [List.length_cons]
theorem emissions_units {n : Nat} (index : Index prepared) (work : List (NativeTensor.Event P G O T I)) (made : Bound.Run pool n) :
    (Bound.emissions index work made).work.length = work.length+made.work.length := by
  change (work.map _ ++ made.work).length = _
  simp only [List.length_append,List.length_map]

def ceiling {α : Type} (cost : α → Nat) : List α → Nat
  | [] => 2
  | head::tail => cost head + ceiling cost tail + 2

theorem ceiling_bound {α : Type} (cost : α → Nat) (run : (item : α) → Bound.Run pool (cost item))
    (units : α → Nat) (covered : ∀ item,(run item).work.length ≤ units item) (items : List α) :
    (Bound.ceiling pool cost run items).work.length ≤ ceiling units items := by
  induction items with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    rw [Bound.ceiling,annotate_units,largest_units]
    simp only [ceiling]
    have bounded := covered head
    omega

def present (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code) :=
  BodySource.Source.evaluation (Whole.Materialization.bound scope input.span intent rival)
    (initial input prepared.saved[index].point).depth (Whole.extent scope input.span intent)

theorem present_exact (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code) :
    (Bound.presentSource pool index scope intent rival).work.length = present index scope intent rival := by
  unfold Bound.presentSource present
  rw [lift_units,BodySource.Source.evaluation_exact prepared]

theorem cast_units {a b : Nat} (same : a = b) (made : Bound.Run pool b) :
    ((congrArg (Bound.Run pool) same).mpr made).work.length = made.work.length := by
  cases same
  rfl

def future (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code)
    (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model)) :=
  let target := Whole.target scope input.span intent rival
  match Future.produce (initial input prepared.saved[index].point).model
      (initial input prepared.saved[index].point).depth target.indexed (Whole.count scope input.span intent) word with
  | .inl _ => 2
  | .inr receipt =>
    let restored := Future.Recovery.produceWith (old := (initial input prepared.saved[index].point).model) input.pricing receipt
    BodySource.Source.evaluation restored.bound (initial input prepared.saved[index].point).depth
      (restored.walk.finish.depth-(initial input prepared.saved[index].point).depth)+1

theorem future_exact (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code)
    (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model)) :
    (Bound.futureSource pool index scope intent rival word).budget.work.length = future index scope intent rival word := by
  unfold Bound.futureSource future
  dsimp only
  split
  · rename_i failed actual
    simp only [actual]
    have size : Whole.Materialization.futureBudget scope input.span intent rival word = 0 := by
      simp only [Whole.Materialization.futureBudget,actual]
    rw [annotate_units]
    change ((congrArg (Bound.Run pool) size).mpr (Bound.lit 0)).work.length+1 = 2
    rw [cast_units size]
    rfl
  · rename_i receipt actual
    simp only [actual]
    let restored := Future.Recovery.produceWith (old := (initial input prepared.saved[index].point).model) input.pricing receipt
    have size : Whole.Materialization.futureBudget scope input.span intent rival word =
        NativeTensor.evaluationBudget restored.bound (initial input prepared.saved[index].point).depth
          (restored.walk.finish.depth-(initial input prepared.saved[index].point).depth) := by
      simp only [Whole.Materialization.futureBudget,actual,NativeTensor.reportBudget]
      rfl
    rw [annotate_units]
    change ((congrArg (Bound.Run pool) size).mpr (Bound.lift
      (Budget.NativeSourceShape.evaluation prepared restored.bound (initial input prepared.saved[index].point).depth
        (restored.walk.finish.depth-(initial input prepared.saved[index].point).depth)))).work.length+1 = _
    rw [cast_units size,lift_units,BodySource.Source.evaluation_exact prepared]

def atom (query : Work.Query pool) : Nat := 1 + (match query with
  | .admission policy row => match row with
    | .coherence first second => 1 ⊞ BodySource.signature
        (Policy.Work.cachedShape (.ready (read pool policy first).scope) (read pool policy first).intent)
        (Policy.Work.cachedShape (.ready (read pool policy second).scope) (read pool policy second).intent)
    | .native index coordinate => match coordinate with
      | .present table =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := Whole.Materialization.present branch.scope input.span branch.intent rival
        let original := Whole.Materialization.present branch.scope input.span .keep rival
        Whole.Materialization.presentBudget branch.scope input.span branch.intent rival +
        Whole.Materialization.presentBudget branch.scope input.span .keep rival +
        (1 ⊞ present index branch.scope branch.intent rival ⊞ present index branch.scope .keep rival ⊞
          BodySource.Present.present (initial input prepared.saved[index].point) current.value original.value)
      | .future table word =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := Whole.Materialization.future branch.scope input.span branch.intent rival word
        let original := Whole.Materialization.future branch.scope input.span .keep rival word
        Whole.Materialization.futureBudget branch.scope input.span branch.intent rival word +
        Whole.Materialization.futureBudget branch.scope input.span .keep rival word +
        (1 ⊞ future index branch.scope branch.intent rival word ⊞ future index branch.scope .keep rival word ⊞
          BodySource.FutureShape.comparison (initial input prepared.saved[index].point) current.value original.value)
      | .funding .. | .release | .coverage | .deployment => 1
    | .informed | .uniform .. => 1
  | .present new previous index table =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := Whole.Materialization.present left.scope input.span left.intent rival
    let original := Whole.Materialization.present right.scope input.span right.intent rival
    Whole.Materialization.presentBudget left.scope input.span left.intent rival +
    Whole.Materialization.presentBudget right.scope input.span right.intent rival +
    (1 ⊞ present index left.scope left.intent rival ⊞ present index right.scope right.intent rival ⊞
      BodySource.BenefitShape.present (initial input prepared.saved[index].point) current.value original.value)
  | .future new previous index table word =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := Whole.Materialization.future left.scope input.span left.intent rival word
    let original := Whole.Materialization.future right.scope input.span right.intent rival word
    Whole.Materialization.futureBudget left.scope input.span left.intent rival word +
    Whole.Materialization.futureBudget right.scope input.span right.intent rival word +
    (1 ⊞ future index left.scope left.intent rival word ⊞ future index right.scope right.intent rival word ⊞
      BodySource.BenefitShape.future (initial input prepared.saved[index].point) current.value original.value)
  | .funding .. => 1)

theorem atom_bound (query : Work.Query pool) : (Bound.atom pool query).work.length ≤ atom query := by
  cases query with
  | admission policy row =>
    cases row with
    | informed | uniform => exact Nat.le_refl _
    | coherence first second =>
      unfold Bound.atom atom
      dsimp only
      rw [annotate_units,plus_units,literal_units,lift_units,BodySource.signature_exact prepared]
      omega
    | native index coordinate =>
      cases coordinate with
      | release | coverage | deployment | funding => exact Nat.le_refl _
      | present table =>
        have left := Whole.Materialization.present_work_bound (read pool policy index).scope input.span
          (read pool policy index).intent (Comparison.rival pool index table)
        have right := Whole.Materialization.present_work_bound (read pool policy index).scope input.span
          .keep (Comparison.rival pool index table)
        unfold Bound.atom atom
        dsimp only
        rw [annotate_units,emissions_units,List.length_append]
        repeat' first | rw [plus_units] | rw [literal_units] | rw [lift_units] |
          rw [present_exact] | rw [BodySource.Present.present_exact prepared]
        omega
      | future table word =>
        have left := Whole.Materialization.future_work_bound (read pool policy index).scope input.span
          (read pool policy index).intent (Comparison.rival pool index table) word
        have right := Whole.Materialization.future_work_bound (read pool policy index).scope input.span
          .keep (Comparison.rival pool index table) word
        unfold Bound.atom atom
        dsimp only
        rw [annotate_units]
        change (Bound.emissions index
          ((Bound.futureSource pool index (read pool policy index).scope (read pool policy index).intent (Comparison.rival pool index table) word).work ++
           (Bound.futureSource pool index (read pool policy index).scope .keep (Comparison.rival pool index table) word).work) _).work.length+1 ≤ _
        rw [emissions_units,List.length_append]
        repeat' first | rw [plus_units] | rw [literal_units] | rw [lift_units] | rw [future_exact] |
          rw [BodySource.FutureShape.comparison_exact prepared]
        simp only [Bound.FutureEmission.work_exact,Bound.FutureEmission.value_exact]
        omega
  | present new previous index table =>
    have left := Whole.Materialization.present_work_bound (read pool new index).scope input.span
      (read pool new index).intent (Comparison.rival pool index table)
    have right := Whole.Materialization.present_work_bound (read pool previous index).scope input.span
      (read pool previous index).intent (Comparison.rival pool index table)
    unfold Bound.atom atom
    dsimp only
    rw [annotate_units,emissions_units,List.length_append]
    repeat' first | rw [plus_units] | rw [literal_units] | rw [lift_units] |
      rw [present_exact] | rw [BodySource.BenefitShape.present_exact prepared]
    omega
  | future new previous index table word =>
    have left := Whole.Materialization.future_work_bound (read pool new index).scope input.span
      (read pool new index).intent (Comparison.rival pool index table) word
    have right := Whole.Materialization.future_work_bound (read pool previous index).scope input.span
      (read pool previous index).intent (Comparison.rival pool index table) word
    unfold Bound.atom atom
    dsimp only
    rw [annotate_units]
    change (Bound.emissions index
      ((Bound.futureSource pool index (read pool new index).scope (read pool new index).intent (Comparison.rival pool index table) word).work ++
       (Bound.futureSource pool index (read pool previous index).scope (read pool previous index).intent (Comparison.rival pool index table) word).work) _).work.length+1 ≤ _
    rw [emissions_units,List.length_append]
    repeat' first | rw [plus_units] | rw [literal_units] | rw [lift_units] | rw [future_exact] |
      rw [BodySource.BenefitShape.future_exact prepared]
    simp only [Bound.FutureEmission.work_exact,Bound.FutureEmission.value_exact]
    omega
  | funding => exact Nat.le_refl _

variable (pool)
def units : Nat :=
  let count := BodySource.length (sections pool)
  let atoms := 1+ceiling atom (Work.queries pool)
  let tables := ceiling (fun index : Index prepared => BodySource.length (Comparison.tables pool index)) (keys prepared)
  let words := ceiling (fun index : Index prepared => BodySource.length (Work.capabilityWords index)) (keys prepared)
  let admission := BodySource.length (rows pool) ⊠ (1 ⊞ 1)
  let benefit := BodySource.length (keys prepared) ⊠ (1 ⊠ (1 ⊞ 1 ⊞ 1 ⊠ 1 ⊠ (1 ⊞ 1)) ⊞ 1)
  let strict := 1 ⊠ 1 ⊞ 1
  let verification := 1 ⊞ 1 ⊞ (1 ⊠ (1 ⊞ 1 ⊞ 1))
  let result := 1 ⊠ (1 ⊞ 1) ⊞ 1 ⊠ (1 ⊞ 1) ⊞ 1 ⊞ 1 ⊠ 1 ⊞ 1
  count+atoms+tables+words+admission+benefit+strict+verification+result

theorem generated_body_fits_the_source_units : (Bound.generate pool).work.length ≤ units pool := by
  have atoms := ceiling_bound (pool := pool) (Work.atomBudget pool) (Bound.atom pool) atom (atom_bound (pool := pool)) (Work.queries pool)
  have tables := ceiling_bound (pool := pool) (fun index : Index prepared => (Comparison.tables pool index).length)
    (fun index => Bound.lift (Budget.length (Comparison.tables pool index)))
    (fun index => BodySource.length (Comparison.tables pool index))
    (fun index => by rw [lift_units,BodySource.length_exact prepared]) (keys prepared)
  have words := ceiling_bound (pool := pool) (fun index : Index prepared => (Work.capabilityWords index).length)
    (fun index => Bound.lift (Budget.length (Work.capabilityWords index)))
    (fun index => BodySource.length (Work.capabilityWords index))
    (fun index => by rw [lift_units,BodySource.length_exact prepared]) (keys prepared)
  unfold Bound.generate units
  simp only [Bound.retain,List.length_append]
  repeat' first | rw [plus_units] | rw [times_units] | rw [literal_units] | rw [annotate_units] |
    rw [lift_units] | rw [BodySource.length_exact prepared]
  simp only [Bound.borrow,List.length_singleton]
  omega

structure Generated where
  private mk ::
  allowance : Nat
  source_generated : allowance = units pool
  budget : Bound.Run pool (Work.workBudget pool)
  budget_generated : budget = Bound.generate pool
  covered : budget.work.length ≤ allowance

def generate : Generated pool := ⟨units pool,rfl,Bound.generate pool,rfl,generated_body_fits_the_source_units pool⟩

theorem every_original_budget_event_fits_without_a_completed_trace_input :
    (generate pool).budget.work.length ≤ (generate pool).allowance := (generate pool).covered

theorem source_body_and_full_selection_fit_the_joint_source_allowance :
    (generate pool).budget.work.length + (Work.generate pool).work.length ≤ (generate pool).allowance + (generate pool).budget.value := by
  have body := (generate pool).covered
  have choice := Bound.generated_budget_covers_every_complete_planner_and_replay pool (sections pool) (List.Perm.refl _)
    (Work.generate pool).receipt
  change _ ≤ (generate pool).allowance + (Bound.generate pool).value
  have works : (Work.generate pool).work.length = (Work.generate pool).receipt.work.length := rfl
  rw [works]
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Body
