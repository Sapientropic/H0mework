import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Law

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}

def Personal (actor : Party) (word : List (Request Party Good Port (State Party Technology) Instrument)) : Prop :=
  ∀ request ∈ word, request.signer = actor ∧ ∀ consent ∈ request.consents, consent = actor

def Legal (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (before : (RawCurrent Party Good (State Party Technology) Instrument)) (word : List (Request Party Good Port (State Party Technology) Instrument)) : Prop :=
  ∀ item ∈ (Mandate.law base scope).rawItems before word, (Mandate.law base scope).Valid item.before item.request
instance (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (before : (RawCurrent Party Good (State Party Technology) Instrument)) (word : List (Request Party Good Port (State Party Technology) Instrument)) : Decidable (Legal (base := base) scope before word) := by
  unfold Legal; infer_instance

/-- The command value is retained; its authority target is generated from
this scope and this intermediate current, including its new version. -/
def rebase (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (before : (RawCurrent Party Good (State Party Technology) Instrument)) (original : (Request Party Good Port (State Party Technology) Instrument)) : (Request Party Good Port (State Party Technology) Instrument) :=
  match original.operation with
  | .revise _ target => match target.last with
    | some command => Mandate.request scope before original.signer command
    | none => original
  | _ => original

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem physical_request_is_retained (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (before : (RawCurrent Party Good (State Party Technology) Instrument)) (original : (Request Party Good Port (State Party Technology) Instrument))
    (physical : ∀ operator target, original.operation ≠ .revise operator target) : rebase scope before original = original := by
  unfold rebase
  split
  · rename_i operator target operation; exact (physical operator target operation).elim
  · rfl

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem rebase_keeps_the_signer (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (before : (RawCurrent Party Good (State Party Technology) Instrument)) (original : (Request Party Good Port (State Party Technology) Instrument)) :
    (rebase scope before original).signer = original.signer := by
  unfold rebase
  split
  · split <;> rfl
  · rfl

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem rebase_adds_no_consent (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (before : (RawCurrent Party Good (State Party Technology) Instrument)) (original : (Request Party Good Port (State Party Technology) Instrument)) (actor : Party)
    (member : actor ∈ (rebase scope before original).consents) : actor ∈ original.consents := by
  unfold rebase at member
  split at member
  · split at member
    · cases member
    · exact member
  · exact member

omit [DecidableEq Instrument] in
theorem a_legal_request_is_unchanged_at_its_own_cut (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (before : (RawCurrent Party Good (State Party Technology) Instrument))
    (original : (Request Party Good Port (State Party Technology) Instrument)) (valid : (Mandate.law base scope).Valid before original) :
    rebase scope before original = original := by
  rcases original with ⟨signer,consents,purpose,gates,operation⟩
  cases operation <;> try rfl
  rename_i operator target
  have policy := valid.1.2
  simp only [Mandate.law,RawLaw.operationAllowed,RawPolicy.eval] at policy
  cases marked : target.last with
  | none => simp only [marked,Bool.false_eq_true] at policy
  | some command =>
      simp only [marked,decide_eq_true_eq] at policy
      rcases policy with ⟨rfl,rfl,rfl,rfl,rfl,_⟩
      simp only [rebase,Mandate.advance_last,Mandate.request]

inductive Path (base : RawLaw Party Good Port Technology Instrument) (scope : Scope (Party := Party) (Good := Good) (Port := Port)) : (RawCurrent Party Good (State Party Technology) Instrument) → List (Request Party Good Port (State Party Technology) Instrument) → Type where
  | private complete (before : (RawCurrent Party Good (State Party Technology) Instrument)) : Path (base := base) scope before []
  | private refused (before : (RawCurrent Party Good (State Party Technology) Instrument)) (head : (Request Party Good Port (State Party Technology) Instrument)) (tail : List (Request Party Good Port (State Party Technology) Instrument))
      (failure : ¬ (Mandate.law base scope).Valid before (rebase scope before head)) : Path (base := base) scope before (head :: tail)
  | private accepted (before : (RawCurrent Party Good (State Party Technology) Instrument)) (head : (Request Party Good Port (State Party Technology) Instrument)) (tail : List (Request Party Good Port (State Party Technology) Instrument))
      (valid : (Mandate.law base scope).Valid before (rebase scope before head))
      (rest : Path (base := base) scope ((Mandate.law base scope).step before (rebase scope before head)) tail) : Path (base := base) scope before (head :: tail)

def compile (base : RawLaw Party Good Port Technology Instrument) (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (before : (RawCurrent Party Good (State Party Technology) Instrument)) : (word : List (Request Party Good Port (State Party Technology) Instrument)) → Path (base := base) scope before word
  | [] => .complete before
  | head :: tail =>
      if valid : (Mandate.law base scope).Valid before (rebase scope before head) then
        .accepted before head tail valid (compile (base := base) scope ((Mandate.law base scope).step before (rebase scope before head)) tail)
      else .refused before head tail valid

namespace Path
variable {scope : Scope (Party := Party) (Good := Good) (Port := Port)} {before : (RawCurrent Party Good (State Party Technology) Instrument)} {word : List (Request Party Good Port (State Party Technology) Instrument)}
def output : {before : (RawCurrent Party Good (State Party Technology) Instrument)} → {word : List (Request Party Good Port (State Party Technology) Instrument)} → Path (base := base) scope before word → List (Request Party Good Port (State Party Technology) Instrument)
  | _,_,.complete _ => []
  | _,_,.refused before head _ _ => [rebase scope before head]
  | _,_,.accepted before head _ _ rest => rebase scope before head :: output rest

def consumed : {before : (RawCurrent Party Good (State Party Technology) Instrument)} → {word : List (Request Party Good Port (State Party Technology) Instrument)} → Path (base := base) scope before word → List (Request Party Good Port (State Party Technology) Instrument)
  | _,_,.complete _ => []
  | _,_,.refused _ _ _ _ => []
  | _,_,.accepted _ head _ _ rest => head :: consumed rest

def residual : {before : (RawCurrent Party Good (State Party Technology) Instrument)} → {word : List (Request Party Good Port (State Party Technology) Instrument)} → Path (base := base) scope before word → List (Request Party Good Port (State Party Technology) Instrument)
  | _,_,.complete _ => []
  | _,_,.refused _ head tail _ => head :: tail
  | _,_,.accepted _ _ _ _ rest => residual rest

def succeeded : {before : (RawCurrent Party Good (State Party Technology) Instrument)} → {word : List (Request Party Good Port (State Party Technology) Instrument)} → Path (base := base) scope before word → Bool
  | _,_,.complete _ => true
  | _,_,.refused .. => false
  | _,_,.accepted _ _ _ _ rest => succeeded rest

theorem original_split (path : Path (base := base) scope before word) : path.consumed ++ path.residual = word := by
  induction path
  next before => rfl
  next before head tail failure => rfl
  next before head tail valid rest ih => exact congrArg (List.cons head) ih

theorem output_is_bounded_by_the_original_word (path : Path (base := base) scope before word) : path.output.length ≤ word.length := by
  induction path
  next before => exact le_refl _
  next before head tail failure => simp only [output,List.length_cons,List.length_nil]; omega
  next before head tail valid rest ih => simpa only [output,List.length_cons] using Nat.succ_le_succ ih

private theorem execute_final_independent (word : List (Request Party Good Port (State Party Technology) Instrument)) (initial : (RawCurrent Party Good (State Party Technology) Instrument)) (left right : Nat) :
    ((Mandate.law base scope).execute initial left word).final =
      ((Mandate.law base scope).execute initial right word).final := by
  induction word generalizing initial left right with
  | nil => rfl
  | cons head tail ih => exact ih _ _ _

private theorem legal_at_any_index (word : List (Request Party Good Port (State Party Technology) Instrument)) (initial : (RawCurrent Party Good (State Party Technology) Instrument)) (index : Nat) :
    (∀ item ∈ ((Mandate.law base scope).execute initial index word).items,
      (Mandate.law base scope).Valid item.before item.request) ↔ Legal (base := base) scope initial word := by
  induction word generalizing initial index with
  | nil => simp [Legal,RawLaw.rawItems,RawLaw.execute]
  | cons head tail ih =>
      simp only [Legal,RawLaw.rawItems,RawLaw.execute,List.mem_cons,forall_eq_or_imp]
      exact and_congr_right fun _ => (ih _ (index+1)).trans (ih _ 1).symm

theorem legal_cons (initial : (RawCurrent Party Good (State Party Technology) Instrument)) (head : (Request Party Good Port (State Party Technology) Instrument)) (tail : List (Request Party Good Port (State Party Technology) Instrument)) :
    Legal (base := base) scope initial (head :: tail) ↔
      (Mandate.law base scope).Valid initial head ∧ Legal (base := base) scope ((Mandate.law base scope).step initial head) tail := by
  change (∀ item ∈ ((Mandate.law base scope).execute initial 0 (head :: tail)).items, _) ↔ _
  simp only [RawLaw.execute,List.mem_cons,forall_eq_or_imp]
  rw [legal_at_any_index tail _ 1]

theorem successful_output_is_all_legal (path : Path (base := base) scope before word) (success : path.succeeded = true) :
    Legal (base := base) scope before path.output := by
  induction path
  next before => simp [Legal,output,RawLaw.rawItems,RawLaw.execute]
  next before head tail failure => cases success
  next before head tail valid rest ih =>
      change ∀ item ∈ ((Mandate.law base scope).execute before 0 (_ :: _)).items, _
      simp only [RawLaw.execute,List.mem_cons,forall_eq_or_imp]
      exact ⟨valid,(legal_at_any_index _ _ 1).mpr (ih success)⟩

theorem failed_output_ends_at_its_actual_first_refusal (path : Path (base := base) scope before word) (failure : path.succeeded = false) :
    ∃ paidPrefix original tail,
      word = path.consumed ++ original :: tail ∧ path.residual = original :: tail ∧
      paidPrefix.length = path.consumed.length ∧
      Legal (base := base) scope before paidPrefix ∧
      path.output = paidPrefix ++ [rebase scope ((Mandate.law base scope).execute before 0 paidPrefix).final original] ∧
      ¬ (Mandate.law base scope).Valid ((Mandate.law base scope).execute before 0 paidPrefix).final
        (rebase scope ((Mandate.law base scope).execute before 0 paidPrefix).final original) := by
  induction path
  next before => cases failure
  next before head tail denied =>
      exact ⟨[],head,tail,rfl,rfl,rfl,by simp [Legal,RawLaw.rawItems,RawLaw.execute],rfl,denied⟩
  next before head tail valid rest ih =>
      obtain ⟨paidPrefix,original,remaining,split,residual,length,legal,output,denied⟩ := ih failure
      let first := rebase scope before head
      have final := execute_final_independent (base := base) (scope := scope) paidPrefix ((Mandate.law base scope).step before first) 1 0
      refine ⟨first :: paidPrefix,original,remaining,congrArg (List.cons head) split,residual,congrArg Nat.succ length,?_,?_,?_⟩
      · change ∀ item ∈ ((Mandate.law base scope).execute before 0 (first :: paidPrefix)).items, _
        simp only [RawLaw.execute,List.mem_cons,forall_eq_or_imp]
        exact ⟨valid,(legal_at_any_index _ _ 1).mpr legal⟩
      · simp only [Path.output,output,List.cons_append,RawLaw.execute,final,first]
      · simpa only [RawLaw.execute,final] using denied
/-- This is an index-preserving prefix relation. It does not equate histories. -/
def Aligned (scope : Scope (Party := Party) (Good := Good) (Port := Port)) : Nat → List (Request Party Good Port (State Party Technology) Instrument) → List (ExecutionItem Party Good Port (State Party Technology) Instrument) → Prop
  | _,_,[] => True
  | _,[],_ :: _ => False
  | index,old :: tail,item :: items => item.index = index ∧ item.request = rebase scope item.before old ∧ Aligned scope (index+1) tail items

theorem output_preserves_original_positions_and_rebuilds_current_targets (path : Path (base := base) scope before word) (index : Nat) :
    Aligned scope index word ((Mandate.law base scope).execute before index path.output).items := by
  induction path generalizing index
  next before => trivial
  next before head tail failure => exact ⟨rfl,rfl,by cases tail <;> trivial⟩
  next before head tail valid rest ih => exact ⟨rfl,rfl,ih (index+1)⟩

theorem failure_is_an_actual_raw_item (path : Path (base := base) scope before word) (failure : path.succeeded = false) :
    ∃ item ∈ (Mandate.law base scope).rawItems before path.output,
      item.index = path.consumed.length ∧ ¬ (Mandate.law base scope).Valid item.before item.request := by
  obtain ⟨paidPrefix,original,tail,split,residual,length,legal,output,denied⟩ := failed_output_ends_at_its_actual_first_refusal path failure
  refine ⟨⟨paidPrefix.length,((Mandate.law base scope).execute before 0 paidPrefix).final,
    rebase scope ((Mandate.law base scope).execute before 0 paidPrefix).final original⟩,?_,length,denied⟩
  rw [output,RawLaw.rawItems,(Mandate.law base scope).execute_append]
  simp only [RawLaw.execute,Nat.zero_add]
  exact List.mem_append_right _ List.mem_cons_self

theorem output_preserves_personal_signature_control (path : Path (base := base) scope before word) (actor : Party)
    (controlled : Personal actor word) : Personal actor path.output := by
  have headControl (initial : (RawCurrent Party Good (State Party Technology) Instrument)) (original : (Request Party Good Port (State Party Technology) Instrument))
      (own : original.signer = actor ∧ ∀ consent ∈ original.consents, consent = actor) :
      (rebase scope initial original).signer = actor ∧ ∀ consent ∈ (rebase scope initial original).consents, consent = actor :=
    ⟨(rebase_keeps_the_signer _ _ _).trans own.1,fun consent inside => own.2 consent (rebase_adds_no_consent _ _ _ _ inside)⟩
  induction path
  next before => intro request impossible; cases impossible
  next before head tail failure =>
    intro request member
    have same := List.mem_singleton.mp member
    rw [same]
    exact headControl before head (controlled head List.mem_cons_self)
  next before head tail valid rest ih =>
    intro request member
    rcases List.mem_cons.mp member with rfl | later
    · exact headControl before head (controlled head List.mem_cons_self)
    · exact ih (fun request inside => controlled request (List.mem_cons_of_mem _ inside)) request later

end Path
/-- At its original source cut every checked finite word is replayed in full. -/
theorem every_old_legal_word_is_fully_replayed_at_its_own_cut
    (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (before : (RawCurrent Party Good (State Party Technology) Instrument)) (word : List (Request Party Good Port (State Party Technology) Instrument)) (legal : Legal (base := base) scope before word) :
    (compile (base := base) scope before word).output = word ∧ (compile (base := base) scope before word).succeeded = true := by
  induction word generalizing before with
  | nil => exact ⟨rfl,rfl⟩
  | cons head tail ih =>
      obtain ⟨valid,rest⟩ := (Path.legal_cons before head tail).mp legal
      have same := a_legal_request_is_unchanged_at_its_own_cut scope before head valid
      simp only [compile,same,dif_pos valid,Path.output,Path.succeeded]
      rw [same]
      exact ⟨congrArg (List.cons head) (ih _ rest).1,(ih _ rest).2⟩


namespace Path
variable {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {before : RawCurrent Party Good (State Party Technology) Instrument}
  {word : List (Request Party Good Port (State Party Technology) Instrument)}
theorem exact_compile (path : Path (base := base) scope before word) : path = compile base scope before word := by
  induction path
  next before => rfl
  next before head tail failure => simp only [compile,dif_neg failure]
  next before head tail valid rest ih => simp only [compile,dif_pos valid,ih]
end Path

structure Materialized (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (before : RawCurrent Party Good (State Party Technology) Instrument)
    (word : List (Request Party Good Port (State Party Technology) Instrument)) where
  private mk ::
  path : Path base scope before word
  output : List (Request Party Good Port (State Party Technology) Instrument)
  consumed : List (Request Party Good Port (State Party Technology) Instrument)
  residual : List (Request Party Good Port (State Party Technology) Instrument)
  succeeded : Bool
  output_exact : output = path.output
  consumed_exact : consumed = path.consumed
  residual_exact : residual = path.residual
  succeeded_exact : succeeded = path.succeeded
namespace Materialized
variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (before : RawCurrent Party Good (State Party Technology) Instrument)
  (head : Request Party Good Port (State Party Technology) Instrument)
  (tail : List (Request Party Good Port (State Party Technology) Instrument))
def empty : Materialized base scope before [] := ⟨.complete before,[],[],[],true,rfl,rfl,rfl,rfl⟩
def refused (emitted : Request Party Good Port (State Party Technology) Instrument)
    (rebased : emitted = rebase scope before head)
    (failure : ¬ (Mandate.law base scope).Valid before emitted) : Materialized base scope before (head::tail) :=
  ⟨.refused before head tail (rebased ▸ failure),[emitted],[],head::tail,false,
    by cases rebased;rfl,rfl,rfl,rfl⟩
def accepted (emitted : Request Party Good Port (State Party Technology) Instrument)
    (rebased : emitted = rebase scope before head)
    (valid : (Mandate.law base scope).Valid before emitted)
    (rest : Materialized base scope ((Mandate.law base scope).step before emitted) tail) :
    Materialized base scope before (head::tail) :=
  ⟨.accepted before head tail (rebased ▸ valid) (rebased ▸ rest.path),
    emitted::rest.output,head::rest.consumed,rest.residual,rest.succeeded,
    by cases rebased;simpa only [Path.output] using congrArg (List.cons _) rest.output_exact,
    by cases rebased;simpa only [Path.consumed] using congrArg (List.cons _) rest.consumed_exact,
    by cases rebased;exact rest.residual_exact,
    by cases rebased;exact rest.succeeded_exact⟩
variable {base scope before}
theorem path_exact {word : List (Request Party Good Port (State Party Technology) Instrument)}
    (made : Materialized base scope before word) : made.path = compile base scope before word := made.path.exact_compile
end Materialized

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay
