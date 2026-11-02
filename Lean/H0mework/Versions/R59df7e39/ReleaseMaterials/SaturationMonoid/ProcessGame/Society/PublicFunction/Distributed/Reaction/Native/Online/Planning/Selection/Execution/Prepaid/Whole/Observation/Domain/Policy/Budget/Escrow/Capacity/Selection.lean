import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Choice
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue)

inductive LocalRow (index : Index prepared) where
  | release
  | coverage
  | deployment
  | present (table : Comparison.Table pool index)
  | future (table : Comparison.Table pool index) (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model))
  | funding (table : Comparison.Table pool index) (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model))
inductive Row where
  | informed
  | uniform (first second : Index prepared)
  | coherence (first second : Index prepared)
  | native (index : Index prepared) (coordinate : LocalRow pool index)

def localRows (index : Index prepared) : List (LocalRow pool index) := [.release,.coverage,.deployment] ++
  (Comparison.tables pool index).flatMap fun table => [.present table] ++
    (Future.Recovery.capabilities (initial input prepared.saved[index].point).model (initial input prepared.saved[index].point).depth).map (.future table) ++
    (Future.Recovery.capabilities (initial input prepared.saved[index].point).model (initial input prepared.saved[index].point).depth).map (.funding table)
def rows : List (Row pool) := [.informed] ++
  (keys prepared).flatMap (fun first => (keys prepared).map (.uniform first)) ++
  (keys prepared).flatMap (fun first => (keys prepared).map (.coherence first)) ++
  (keys prepared).flatMap (fun index => (localRows pool index).map (.native index))

def LocalHolds (policy : Section pool) (index : Index prepared) : LocalRow pool index → Prop
  | .release => released (read pool policy index).entry.2 = true
  | .coverage => Comparison.OldCovered index ∧ (read pool policy index).Covered
  | .deployment => (read pool policy index).Deployable
  | .present table => Synthesis.accepts (initial input prepared.saved[index].point).source.val.code
      (Window.axes (initial input prepared.saved[index].point).model (initial input prepared.saved[index].point).depth)
      ((read pool policy index).tensor (Comparison.rival pool index table)).present (oldTensor index (Comparison.rival pool index table)).present
  | .future table word => futureNoWorse (initial input prepared.saved[index].point)
      (((read pool policy index).tensor (Comparison.rival pool index table)).future _ word)
      ((oldTensor index (Comparison.rival pool index table)).future _ word)
  | .funding table word => ((oldTensor index (Comparison.rival pool index table)).funding _ word).isNone = true →
      (((read pool policy index).tensor (Comparison.rival pool index table)).funding _ word).isNone = true
instance (policy : Section pool) (index : Index prepared) (row : LocalRow pool index) : Decidable (LocalHolds pool policy index row) := by
  cases row <;> unfold LocalHolds <;> infer_instance

def Holds (policy : Section pool) : Row pool → Prop
  | .informed => prepared.saved ≠ []
  | .uniform first second => (read pool policy first).entry.1 = (read pool policy second).entry.1
  | .coherence first second =>
      Policy.shape (.ready (read pool policy first).scope) (read pool policy first).intent =
        Policy.shape (.ready (read pool policy second).scope) (read pool policy second).intent
  | .native index coordinate => LocalHolds pool policy index coordinate
instance (policy : Section pool) (row : Row pool) : Decidable (Holds pool policy row) := by
  cases row <;> unfold Holds <;> infer_instance

theorem local_rows_iff (policy : Section pool) (index : Index prepared) :
    (∀ row ∈ localRows pool index,LocalHolds pool policy index row) ↔
    released (read pool policy index).entry.2 = true ∧ Comparison.OldCovered index ∧
      (read pool policy index).Covered ∧ (read pool policy index).Deployable ∧
      ∀ table ∈ Comparison.tables pool index,accepts (initial input prepared.saved[index].point)
        ((read pool policy index).tensor (Comparison.rival pool index table)) (oldTensor index (Comparison.rival pool index table)) := by
  constructor
  · intro all
    have covered := all .coverage (by simp [localRows])
    refine ⟨all .release (by simp [localRows]),covered.1,covered.2,all .deployment (by simp [localRows]),?_⟩
    intro table member
    refine ⟨all (.present table) ?_,?_,?_⟩
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨table,member,List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)⟩)
    · intro word inside
      exact all (.future table word) (List.mem_append_right _ (List.mem_flatMap.mpr ⟨table,member,
        List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨word,inside,rfl⟩))⟩))
    · intro word inside
      exact all (.funding table word) (List.mem_append_right _ (List.mem_flatMap.mpr ⟨table,member,
        List.mem_append_right _ (List.mem_map.mpr ⟨word,inside,rfl⟩)⟩))
  · rintro ⟨paid,oldBound,newBound,deployable,all⟩ row inside
    rcases List.mem_append.mp inside with gate | economic
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at gate
      rcases gate with same | same | same <;> subst row
      · exact paid
      · exact ⟨oldBound,newBound⟩
      · exact deployable
    · obtain ⟨table,member,generated⟩ := List.mem_flatMap.mp economic
      have valid := all table member
      simp only [List.mem_append,List.mem_singleton,List.mem_map] at generated
      rcases generated with (same | ⟨word,registered,same⟩) | ⟨word,registered,same⟩
      · subst row;exact valid.1
      · subst row;exact valid.2.1 word registered
      · subst row;exact valid.2.2 word registered

theorem rows_iff (policy : Section pool) : (∀ row ∈ rows pool,Holds pool policy row) ↔ Accepted pool policy := by
  constructor
  · intro all
    have native (index : Index prepared) := (local_rows_iff pool policy index).mp (fun row member =>
      all (.native index row) (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨index,List.mem_finRange _,List.mem_map.mpr ⟨row,member,rfl⟩⟩)))
    refine ⟨⟨all .informed (by simp [rows]),?_,?_,?_⟩,?_⟩
    · intro first second;exact all (.uniform first second) (by simp [rows])
    · intro first second;exact all (.coherence first second) (by simp [rows])
    · intro index;exact ⟨(native index).1,(native index).2.1,(native index).2.2.1,(native index).2.2.2.1⟩
    · intro index;exact (native index).2.2.2.2
  · rintro ⟨⟨nonempty,uniform,coherent,native⟩,economic⟩ row inside
    cases row with
    | informed => exact nonempty
    | uniform first second => exact uniform first second
    | coherence first second => exact coherent first second
    | native index coordinate =>
        simp only [rows,List.mem_append,List.mem_singleton,List.mem_flatMap,List.mem_map] at inside
        rcases inside with ((bad | ⟨first,_,second,_,bad⟩) | ⟨first,_,second,_,bad⟩) | ⟨other,_,coordinate,member,same⟩
        · cases bad
        · cases bad
        · cases bad
        · have known := (local_rows_iff pool policy other).mpr
            ⟨(native other).1,(native other).2.1,(native other).2.2.1,(native other).2.2.2,economic other⟩ coordinate member
          exact same ▸ known

structure Rejection (policy : Section pool) where
  row : Row pool
  listed : row ∈ rows pool
  broken : ¬ Holds pool policy row
inductive Outcome where
  | selected (choice : Choice pool)
  | blocked (rejected : ∀ policy : Section pool,Rejection pool policy)

def compile : Outcome pool :=
  match result : select pool with
  | some choice => .selected choice
  | none => .blocked (fun policy => match Distributed.inspect (Holds pool policy) (rows pool) with
      | .rejected row listed broken => ⟨row,listed,broken⟩
      | .accepted all => False.elim (by
          have empty := (Distributed.choose_none_iff_empty _ _ _).mp result
          obtain ⟨candidate,listed,_⟩ := every_accepted_section_is_generated pool policy ((rows_iff pool policy).mp all)
          rw [empty] at listed
          exact List.not_mem_nil listed))

structure Protocol where
  private mk ::
  outcome : Outcome pool
  generated : outcome = compile pool

def invoke : Protocol pool := ⟨compile pool,rfl⟩

inductive Debt (protocol : Protocol pool) where
  | prior (debt : Comparison.Pool.Debt pool)
  | matrix (index : Index prepared) (debt : Comparison.Matrix.Debt (Comparison.generateMatrix pool index))
  | policyGeneration
  | uniformity
  | sourceRelease
  | fullTensorComparison
  | verification
  | storage

def Protocol.pending (protocol : Protocol pool) : List (Debt pool protocol) :=
  pool.pending.map Debt.prior ++ (keys prepared).flatMap (fun index =>
    (Comparison.generateMatrix pool index).pending.map (Debt.matrix index)) ++
    [.policyGeneration,.uniformity,.sourceRelease,.fullTensorComparison,.verification,.storage]

structure Generated (catalogue : Catalogue snapshot) where
  private mk ::
  pool : Comparison.Pool catalogue
  generated : pool = Comparison.generate catalogue
  protocol : Protocol pool
  protocol_generated : protocol = invoke pool

def generate (catalogue : Catalogue snapshot) : Generated catalogue :=
  let pool := Comparison.generate catalogue
  ⟨pool,rfl,invoke pool,rfl⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy
