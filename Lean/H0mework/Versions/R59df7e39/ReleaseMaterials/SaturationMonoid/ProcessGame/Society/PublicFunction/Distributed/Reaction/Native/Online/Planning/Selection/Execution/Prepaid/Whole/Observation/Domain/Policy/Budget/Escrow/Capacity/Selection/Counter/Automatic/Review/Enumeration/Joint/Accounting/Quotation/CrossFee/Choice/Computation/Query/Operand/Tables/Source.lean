import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Tables.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Tables
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}
variable {pool : List (Offer (prepared := prepared) (position := position))}

structure Completed (pool : List (Offer (prepared := prepared) (position := position))) where
  private mk ::
  items : List (Probe pool)
  exact_source : items = probes pool
structure Cursor (pool : List (Offer (prepared := prepared) (position := position))) where
  private mk ::
  remaining : Queue (pool := pool)
  cached : List (Probe pool)
  coherent : cached++denote remaining = probes pool

def initial (pool : List (Offer (prepared := prepared) (position := position))) : Cursor pool := ⟨start,[],initial_denote⟩
def Cursor.rank (cursor : Cursor pool) := Tables.rank cursor.remaining
def Cursor.move (cursor : Cursor pool) : Option (Event (pool := pool) × Cursor pool) :=
  match actual : step cursor.remaining with
  | none => none
  | some (after,yielded,event) => some (event,⟨after,cursor.cached++yielded.toList,by
      rw [List.append_assoc,←one_step_conserves actual];exact cursor.coherent⟩)
def Cursor.completed (cursor : Cursor pool) : Option (Completed pool) :=
  match actual : cursor.remaining with
  | [] => some ⟨cursor.cached,by simpa only [actual,denote,List.flatMap_nil,List.append_nil] using cursor.coherent⟩
  | _::_ => none

theorem rank_zero_iff (queue : Queue (pool := pool)) : Tables.rank queue = 0 ↔ queue = [] := by
  cases queue with
  | nil => simp [Tables.rank]
  | cons task rest => cases task <;> simp [Tables.rank,Task.rank,Nat.add_assoc]

theorem Cursor.completed_iff_stopped (cursor : Cursor pool) : cursor.completed.isSome = true ↔ cursor.move = none := by
  rcases cursor with ⟨remaining,cached,coherent⟩
  cases remaining with
  | nil => simp [Cursor.completed,Cursor.move,step]
  | cons task rest =>
      have active := (stopped_iff_empty (pool := pool) (task::rest)).not.mpr (by simp)
      simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
      unfold Cursor.move
      split
      · contradiction
      · simp

theorem Cursor.move_decreases {before after : Cursor pool} {event : Event (pool := pool)}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  unfold Cursor.move at actual
  split at actual
  · cases actual
  · rename_i next yielded ev observed
    cases actual
    exact step_decreases_rank observed

theorem Cursor.stopped_iff_zero (cursor : Cursor pool) : cursor.move = none ↔ cursor.rank = 0 := by
  unfold Cursor.move Cursor.rank
  split
  · rename_i actual
    have empty := (stopped_iff_empty _).mp actual
    simp only [empty,Tables.rank,List.map_nil,List.sum_nil]
  · rename_i next yielded event actual
    have active : cursor.remaining ≠ [] := fun empty => by simp only [empty,step] at actual;cases actual
    simp only [reduceCtorEq,false_iff]
    exact fun zero => active ((rank_zero_iff _).mp zero)

inductive History : Cursor pool → Cursor pool → List (Event (pool := pool)) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor pool) (capacity : Nat) where
  private mk ::
  endpoint : Cursor pool
  work : List (Event (pool := pool))
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank

def run : (capacity : Nat) → (before : Cursor pool) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩

theorem run_sufficient (before : Cursor pool) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega

def extract (wanted : Index prepared) : List (Probe pool) → List (Table pool wanted)
  | [] => []
  | ⟨index,table⟩::tail => if same : index = wanted then (same ▸ table)::extract wanted tail else extract wanted tail

theorem extract_append (wanted : Index prepared) (left right : List (Probe pool)) :
    extract wanted (left++right) = extract wanted left++extract wanted right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨index,table⟩
      by_cases same : index = wanted
      · simp only [List.cons_append,extract,dif_pos same,ih]
      · simp only [List.cons_append,extract,dif_neg same,ih]

theorem extract_same (index : Index prepared) (items : List (Table pool index)) :
    extract index (items.map fun table => (⟨index,table⟩ : Probe pool)) = items := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [extract,ih]

theorem extract_other (wanted index : Index prepared) (different : index ≠ wanted) (items : List (Table pool index)) :
    extract wanted (items.map fun table => (⟨index,table⟩ : Probe pool)) = [] := by
  induction items with
  | nil => rfl
  | cons head tail ih => simpa only [List.map_cons,extract,dif_neg different] using ih

theorem extract_indices (wanted : Index prepared) (indices : List (Index prepared)) (unique : indices.Nodup) :
    extract (pool := pool) wanted (indices.flatMap (indexProbes pool)) = if wanted ∈ indices then Choice.tables pool wanted else [] := by
  induction indices with
  | nil => simp [extract]
  | cons head tail ih =>
      have distinct := List.nodup_cons.mp unique
      simp only [List.flatMap_cons,extract_append]
      by_cases same : head = wanted
      · subst head
        rw [indexProbes,extract_same,ih distinct.2,if_neg distinct.1]
        simp
      · rw [indexProbes,extract_other wanted head same,ih distinct.2]
        simp only [List.nil_append,List.mem_cons,eq_comm (a := wanted) (b := head)]
        simp only [same,false_or]

theorem Completed.at_exact (cached : Completed pool) (index : Index prepared) :
    extract index cached.items = Choice.tables pool index := by
  rw [cached.exact_source]
  exact (extract_indices index (keys prepared) (by simpa only [keys] using List.nodup_finRange prepared.saved.length)).trans (if_pos (by simp [keys]))
def Completed.at (cached : Completed pool) (index : Index prepared) := extract index cached.items

namespace Cached
variable (cached : Completed pool)
local notation "Program" => Code (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I))
private def relationFrom (lookup : (index : Index prepared) → List (Table pool index)) (same : lookup = Choice.tables pool)
    (new previous : Offer (prepared := prepared) (position := position)) : Program (.truth (ResponsibilityLe pool new previous)) :=
  let tensors := Query.Source.Generic.rows (fun index => ∀ table ∈ lookup index,
      Full.TensorLe (Policy.initial input prepared.saved[index].point) ((new.view index).tensor (Choice.rival pool index table))
        ((previous.view index).tensor (Choice.rival pool index table)))
    (fun index => Query.Source.Generic.rows _ (fun table => Query.Source.tensor (Policy.initial input prepared.saved[index].point)
      ((new.view index).tensor (Choice.rival pool index table)) ((previous.view index).tensor (Choice.rival pool index table))) (lookup index)) (keys prepared)
  let costs := Query.Source.Generic.rows (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I))
    (fun index : Index prepared => new.work index ≤ previous.work index ∧ previous.credit index ≤ new.credit index)
    (fun index => Code.conjunction (.atom (.natural (new.work index) (previous.work index))) (fun _ => .atom (.natural (previous.credit index) (new.credit index)))) (keys prepared)
  let invoices := Code.conjunction (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I))
    (.atom (.natural new.branch.alternative.1 previous.branch.alternative.1)) (fun _ =>
      Code.conjunction (.atom (.natural new.invoiceWork previous.invoiceWork)) (fun _ => .atom (.natural previous.invoiceCredit new.invoiceCredit)))
  Code.transport (by unfold ResponsibilityLe;rw [←same];simp only [keys,List.mem_finRange,forall_const])
    (Code.conjunction tensors (fun _ => Code.conjunction costs (fun _ => invoices)))

private theorem relationFrom_eq (lookup : (index : Index prepared) → List (Table pool index)) (same : lookup = Choice.tables pool)
    (new previous : Offer (prepared := prepared) (position := position)) : relationFrom lookup same new previous = Query.Source.responsibility pool new previous := by
  cases same
  rfl

def responsibility (new previous : Offer (prepared := prepared) (position := position)) :=
  relationFrom cached.at (funext cached.at_exact) new previous

theorem responsibility_eq (new previous : Offer (prepared := prepared) (position := position)) :
    responsibility cached new previous = Query.Source.responsibility pool new previous := relationFrom_eq _ _ _ _

def strict (previous new : Offer (prepared := prepared) (position := position)) :=
  Code.conjunction (responsibility cached new previous) (fun _ => Code.negative (responsibility cached previous new))
theorem strict_eq (previous new : Offer (prepared := prepared) (position := position)) :
    strict cached previous new = Query.Source.strict pool previous new := by
  simp only [strict,Query.Source.strict,responsibility_eq]
def program (ordinal : Nat) : Code (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (.number (Query.Refiner.Claim pool ordinal)) :=
  .bind (.atom (.natural (ordinal+1) pool.length)) fun available => match available with
  | .isFalse absent => .pure ⟨0,by dsimp only [Query.Refiner.Claim];omega⟩
  | .isTrue enough =>
      let current : Fin pool.length := ⟨ordinal,by omega⟩
      .bind (Query.Refiner.Generic.scan (ResponsibilityLe pool) pool (responsibility_refl pool)
        (fun {a b c} => responsibility_trans pool (first := a) (middle := b) (last := c))
        (strict cached) current (List.finRange pool.length)) fun selected =>
          .bind (.atom (.increment selected.val)) fun encoded =>
            .pure ⟨encoded.val,by rw [encoded.property];exact ⟨current.isLt,selected.property⟩⟩

theorem program_eq (ordinal : Nat) : program cached ordinal = Query.Refiner.program pool ordinal := by
  have same : strict cached = Query.Source.strict pool := funext fun previous => funext fun new => strict_eq cached previous new
  unfold program;rw [same];rfl

def responsibilityShape (new previous : Offer (prepared := prepared) (position := position)) :=
  let tensors := CapacityBound.rows (fun index => CapacityBound.rows (fun table =>
    CapacityBound.Shapes.tensor (Policy.initial input prepared.saved[index].point) ((new.view index).tensor (Choice.rival pool index table))
      ((previous.view index).tensor (Choice.rival pool index table))) (cached.at index)) (keys prepared)
  let costs := CapacityBound.rows (fun _ : Index prepared => CapacityBound.pair 2 2) (keys prepared)
  CapacityBound.lift (CapacityBound.pair tensors (CapacityBound.pair costs (CapacityBound.pair 2 (CapacityBound.pair 2 2))))

def responsibilityBudget (new previous : Offer (prepared := prepared) (position := position)) : Meter.Number
    (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (responsibilityShape cached new previous) := by
  unfold responsibilityShape
  apply Meter.lift
  apply Meter.pair
  · apply Meter.rows;intro index
    apply Meter.rows;intro table
    exact Meter.Compiler.tensor (Policy.initial input prepared.saved[index].point) ((new.view index).tensor (Choice.rival pool index table))
      ((previous.view index).tensor (Choice.rival pool index table))
  intro _;apply Meter.pair
  · exact Meter.rows (fun _ : Index prepared => Meter.pair (Meter.literal 2) (fun _ => Meter.literal 2)) (keys prepared)
  intro _;exact Meter.pair (Meter.literal 2) (fun _ => Meter.pair (Meter.literal 2) (fun _ => Meter.literal 2))

def strictShape (previous new : Offer (prepared := prepared) (position := position)) :=
  CapacityBound.pair (responsibilityShape cached new previous) (CapacityBound.lift (responsibilityShape cached previous new))
def strictBudget (previous new : Offer (prepared := prepared) (position := position)) : Meter.Number
    (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (strictShape cached previous new) :=
  Meter.pair (responsibilityBudget cached new previous) (fun _ => Meter.lift (responsibilityBudget cached previous new))

theorem strict_shape_eq (previous new : Offer (prepared := prepared) (position := position)) :
    strictShape cached previous new = CapacityBound.Shapes.strict pool previous new := by
  have same : cached.at = Choice.tables pool := funext cached.at_exact
  unfold strictShape responsibilityShape
  rw [same]
  rfl

def quote : Meter.Number (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (CapacityBound.budget pool) :=
  .bind (Meter.length pool) fun count => .bind (Meter.maxPairs (budget := strictShape cached) (strictBudget cached) pool pool) fun largest =>
    .bind (Meter.add largest.val 3) fun padded => .bind (Meter.multiply count.val padded.val) fun product =>
      .bind (Meter.add product.val 9) fun answer => .pure ⟨answer.val,by
        rw [answer.property,product.property,padded.property,count.property,largest.property]
        have same : strictShape cached = CapacityBound.Shapes.strict pool :=
          funext fun previous => funext fun new => strict_shape_eq cached previous new
        change _ = 9+pool.length*(CapacityBound.maximum pool+3)
        rw [same]
        exact Nat.add_comm _ _⟩
end Cached

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Tables
