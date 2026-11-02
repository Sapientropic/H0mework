import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Payment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Collection
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}

def pack (branch : CrossFee.Branch prepared position) (items : List (Pool.PolicyFor branch.alternative.2.payment))
    (within : ∀ item ∈ items,item ∈ Pool.casePool branch.alternative.2.payment) : List (Pool.Pick prepared position) :=
  items.attach.map fun entry => Pool.Pick.fromListed branch entry.val (within entry.val entry.property)

theorem pack_cons (branch : CrossFee.Branch prepared position) (head : Pool.PolicyFor branch.alternative.2.payment)
    (tail : List (Pool.PolicyFor branch.alternative.2.payment)) (within : ∀ item ∈ head::tail,item ∈ Pool.casePool branch.alternative.2.payment) :
    pack branch (head::tail) within = Pool.Pick.fromListed branch head (within head List.mem_cons_self)::
      pack branch tail (fun item inside => within item (List.mem_cons_of_mem _ inside)) := by
  simp [pack,List.attach_cons,List.map_map]

theorem pack_source (branch : CrossFee.Branch prepared position) :
    pack branch (Pool.casePool branch.alternative.2.payment) (fun _ inside => inside) = Pool.picksFor branch := rfl

def count (branches : List (CrossFee.Branch prepared position)) :=
  (branches.map fun branch => (Pool.casePool branch.alternative.2.payment).length).sum

inductive Stage where
  | branches (todo : List (CrossFee.Branch prepared position)) (reversed : List (Pool.Pick prepared position))
  | entries (branch : CrossFee.Branch prepared position) (todo : List (Pool.PolicyFor branch.alternative.2.payment))
      (within : ∀ item ∈ todo,item ∈ Pool.casePool branch.alternative.2.payment)
      (later : List (CrossFee.Branch prepared position)) (reversed : List (Pool.Pick prepared position))
  | reversing (todo result : List (Pool.Pick prepared position))
  | done (result : List (Pool.Pick prepared position))

def Stage.meaning : Stage (prepared := prepared) (position := position) → List (Pool.Pick prepared position)
  | .branches todo reversed => reversed.reverse++todo.flatMap Pool.picksFor
  | .entries branch todo within later reversed => reversed.reverse++pack branch todo within++later.flatMap Pool.picksFor
  | .reversing todo result => todo.reverse++result
  | .done result => result

def Stage.rank : Stage (prepared := prepared) (position := position) → Nat
  | .branches todo reversed => 2*todo.length+2*count todo+reversed.length+2
  | .entries _ todo _ later reversed => 2*todo.length+2*later.length+2*count later+reversed.length+3
  | .reversing todo _ => todo.length+1
  | .done _ => 0

inductive Event where
  | branch (source : CrossFee.Branch prepared position)
  | candidate (source : Pool.Pick prepared position)
  | closeBranch
  | beginReverse
  | reverse (source : Pool.Pick prepared position)
  | finish

def Stage.move : Stage (prepared := prepared) (position := position) → Option (Event (prepared := prepared) (position := position) × Stage (prepared := prepared) (position := position))
  | .branches [] reversed => some (.beginReverse,.reversing reversed [])
  | .branches (branch::later) reversed => some (.branch branch,.entries branch (Pool.casePool branch.alternative.2.payment) (fun _ inside => inside) later reversed)
  | .entries _ [] _ later reversed => some (.closeBranch,.branches later reversed)
  | .entries branch (head::tail) within later reversed =>
      let candidate := Pool.Pick.fromListed branch head (within head List.mem_cons_self)
      some (.candidate candidate,.entries branch tail (fun item inside => within item (List.mem_cons_of_mem _ inside)) later (candidate::reversed))
  | .reversing [] result => some (.finish,.done result)
  | .reversing (head::tail) result => some (.reverse head,.reversing tail (head::result))
  | .done _ => none

theorem Stage.move_preserves (stage next : Stage (prepared := prepared) (position := position))
    (event : Event (prepared := prepared) (position := position)) (actual : stage.move = some (event,next)) :
    next.meaning = stage.meaning ∧ next.rank+1 = stage.rank := by
  cases stage with
  | branches todo reversed =>
      cases todo with
      | nil => cases actual;constructor <;> simp [Stage.meaning,Stage.rank,count]
      | cons branch later =>
          cases actual
          constructor
          · simp only [Stage.meaning,List.flatMap_cons,pack_source,List.append_assoc]
          · simp only [Stage.rank,count,List.map_cons,List.sum_cons,List.length_cons];omega
  | entries branch todo within later reversed =>
      cases todo with
      | nil => cases actual;constructor <;> simp [Stage.meaning,Stage.rank,pack]
      | cons head tail =>
          cases actual
          constructor
          · simp only [Stage.meaning,List.reverse_cons,pack_cons,List.append_assoc,List.singleton_append]
          · simp only [Stage.rank,List.length_cons];omega
  | reversing todo result =>
      cases todo with
      | nil => cases actual;constructor <;> simp [Stage.meaning,Stage.rank]
      | cons head tail => cases actual;constructor <;> simp [Stage.meaning,Stage.rank,List.reverse_cons,List.append_assoc]
  | done _ => cases actual

theorem Stage.stopped_iff_zero (stage : Stage (prepared := prepared) (position := position)) : stage.move = none ↔ stage.rank = 0 := by
  cases stage with
  | branches todo reversed => cases todo <;> simp [Stage.move,Stage.rank]
  | entries branch todo within later reversed => cases todo <;> simp [Stage.move,Stage.rank]
  | reversing todo result => cases todo <;> simp [Stage.move,Stage.rank]
  | done result => simp [Stage.move,Stage.rank]

structure Cursor (audit : CrossFee.Result prepared position) where
  private mk ::
  stage : Stage (prepared := prepared) (position := position)
  exact : stage.meaning = Pool.collect audit

def initial (audit : CrossFee.Result prepared position) : Cursor audit := ⟨.branches audit.branches [],rfl⟩
def Cursor.rank {audit : CrossFee.Result prepared position} (cursor : Cursor audit) := cursor.stage.rank

def Cursor.move {audit : CrossFee.Result prepared position} (cursor : Cursor audit) :
    Option (Event (prepared := prepared) (position := position) × Cursor audit) :=
  match actual : cursor.stage.move with
  | none => none
  | some (event,next) => some (event,⟨next,(Stage.move_preserves _ _ _ actual).1.trans cursor.exact⟩)

theorem Cursor.move_rank {audit : CrossFee.Result prepared position} (cursor next : Cursor audit)
    (event : Event (prepared := prepared) (position := position)) (actual : cursor.move = some (event,next)) : next.rank+1 = cursor.rank := by
  unfold Cursor.move at actual
  split at actual
  · cases actual
  · rename_i ev stage moved
    simp only [Option.some.injEq,Prod.mk.injEq] at actual
    obtain ⟨rfl,rfl⟩ := actual
    exact (Stage.move_preserves _ _ _ moved).2

theorem Cursor.stopped_iff_zero {audit : CrossFee.Result prepared position} (cursor : Cursor audit) : cursor.move = none ↔ cursor.rank = 0 := by
  unfold Cursor.move
  split
  · rename_i stopped
    exact iff_of_true rfl ((Stage.stopped_iff_zero cursor.stage).mp stopped)
  · rename_i value moved
    have positive : cursor.rank ≠ 0 := by
      intro zero
      have absent := (Stage.stopped_iff_zero cursor.stage).mpr zero
      rw [absent] at moved;cases moved
    simp only [reduceCtorEq,false_iff];exact positive

structure Run {audit : CrossFee.Result prepared position} (start : Cursor audit) (capacity : Nat) where
  private mk ::
  endpoint : Cursor audit
  work : List (Event (prepared := prepared) (position := position))
  covered : work.length ≤ capacity
  conservation : endpoint.rank+work.length = start.rank
  exhausted : endpoint.move = none ∨ work.length = capacity

def run {audit : CrossFee.Result prepared position} : (capacity : Nat) → (start : Cursor audit) → Run start capacity
  | 0,start => ⟨start,[],Nat.le_refl _,by simp,Or.inr rfl⟩
  | capacity+1,start =>
      match actual : start.move with
      | none => ⟨start,[],by simp,by simp,Or.inl actual⟩
      | some (event,next) =>
          let later := run capacity next
          ⟨later.endpoint,event::later.work,by have := later.covered;simp only [List.length_cons];omega,
            by have := later.conservation;have := Cursor.move_rank start next event actual;simp only [List.length_cons];omega,
            later.exhausted.imp_right (fun exact => by simp only [List.length_cons,exact])⟩

theorem run_sufficient {audit : CrossFee.Result prepared position} (start : Cursor audit) (capacity : Nat) (enough : start.rank ≤ capacity) :
    (run capacity start).endpoint.move = none := by
  let result := run capacity start
  rcases result.exhausted with stopped | exhausted
  · exact stopped
  · apply result.endpoint.stopped_iff_zero.mpr
    have := result.conservation;omega

structure Completed (audit : CrossFee.Result prepared position) where
  private mk ::
  items : List (Pool.Pick prepared position)
  exact : items = Pool.collect audit

def Cursor.completed {audit : CrossFee.Result prepared position} (cursor : Cursor audit) : Option (Completed audit) :=
  match actual : cursor.stage with
  | .done items => some ⟨items,by have := cursor.exact;rw [actual] at this;exact this⟩
  | _ => none

theorem Cursor.completed_iff_stopped {audit : CrossFee.Result prepared position} (cursor : Cursor audit) :
    cursor.completed.isSome = true ↔ cursor.move = none := by
  rcases cursor with ⟨stage,coherent⟩
  cases stage with
  | branches todo reversed => cases todo <;> simp [completed,Cursor.move,Stage.move]
  | entries branch todo within later reversed => cases todo <;> simp [completed,Cursor.move,Stage.move]
  | reversing todo result => cases todo <;> simp [completed,Cursor.move,Stage.move]
  | done result => simp [completed,Cursor.move,Stage.move]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Collection
