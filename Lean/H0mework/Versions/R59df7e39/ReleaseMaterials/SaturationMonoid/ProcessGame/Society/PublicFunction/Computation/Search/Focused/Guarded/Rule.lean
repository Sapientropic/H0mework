import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Rule

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

def rowEqual (first second : Rule code) (key : code.Key) : Prop :=
  first.work.val key (code.key_mem key) = second.work.val key (code.key_mem key) ∧
    (first.events key (code.key_mem key)).val = (second.events key (code.key_mem key)).val

instance (first second : Rule code) (key : code.Key) : Decidable (rowEqual code first second key) := by
  unfold rowEqual
  infer_instance

omit [DecidableEq Port] [DecidableEq Technology] in
theorem rule_ext (first second : Rule code) (same : ∀ key,rowEqual code first second key) : first = second := by
  have work : first.work = second.work := Subtype.ext (funext fun key => funext fun _ => (same key).1)
  have events : first.events = second.events := funext fun key => funext fun _ => Subtype.ext (same key).2
  cases first;cases second;cases work;cases events;rfl

def ruleDecidableEq : DecidableEq (Rule code) := fun first second =>
  decidable_of_iff (∀ key : code.Key,rowEqual code first second key) (by
    constructor
    · exact rule_ext code first second
    · intro same;subst second;exact fun _ => ⟨rfl,rfl⟩)
local instance : DecidableEq (Rule code) := ruleDecidableEq code

def keep (active : List (Fin code.sites)) (pinned : List code.Key) (key : code.Key) : Prop :=
  key.1 ∈ active ∨ key ∈ pinned
instance (active : List (Fin code.sites)) (pinned : List code.Key) (key : code.Key) :
    Decidable (keep code active pinned key) := by unfold keep;infer_instance

def mask (active : List (Fin code.sites)) (pinned : List code.Key) (rule : Rule code) : Rule code where
  work := ⟨fun key listed => if keep code active pinned key then rule.work.val key listed else [],by
    apply code.every_local_policy_is_enumerated
    intro key listed
    split
    · exact (List.mem_pi _ _).mp rule.work.property key listed
    · exact (mem_words_iff _ _ _).mpr ⟨by simp,by simp⟩⟩
  events := fun key listed => if keep code active pinned key then rule.events key listed else ⟨none,List.mem_cons_self⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem mask_keeps_each_requested_row (active : List (Fin code.sites)) (pinned : List code.Key)
    (rule : Rule code) (key : code.Key) (retained : keep code active pinned key) :
    rowEqual code (mask code active pinned rule) rule key := by
  simp only [rowEqual,mask,if_pos retained,and_self]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem mask_preserves_the_original_owner_projection (active : List (Fin code.sites)) (pinned : List code.Key)
    (rule : Rule code) : focus code active (mask code active pinned rule) = focus code active rule := by
  apply rule_ext code
  intro key
  by_cases owned : key.1 ∈ active
  · simp only [rowEqual,focus,mask,if_pos owned,if_pos (show keep code active pinned key from .inl owned),and_self]
  · simp only [rowEqual,focus,if_neg owned,and_self]

def difference (first second : Rule code) : Option code.Key :=
  code.keys.find? (fun key => !decide (rowEqual code first second key))

theorem difference_none (first second : Rule code) (missing : difference code first second = none) : first = second := by
  apply rule_ext code
  intro key
  by_cases same : rowEqual code first second key
  · exact same
  · exact False.elim ((List.find?_eq_none.mp missing key (code.key_mem key)) (by simp only [decide_eq_false same,Bool.not_false]))

theorem difference_is_a_real_row (first second : Rule code) (key : code.Key)
    (found : difference code first second = some key) : ¬ rowEqual code first second key := by
  have different : (!decide (rowEqual code first second key)) = true :=
    List.find?_some (p := fun key : code.Key => !decide (rowEqual code first second key)) found
  intro same
  simp only [decide_eq_true same,Bool.not_true] at different
  cases different

/-- Preserve a literal fee identity, including its negation. Only an accidentally
    erased difference requires one additional source row. -/
def project (active : List (Fin code.sites)) (fee rule : Rule code) : Rule code :=
  if same : rule = fee then fee
  else if mask code active [] rule ≠ fee then mask code active [] rule
  else match found : difference code rule fee with
    | some key => mask code active [key] rule
    | none => False.elim (same (difference_none code rule fee found))

theorem projection_keeps_the_owner_rows (active : List (Fin code.sites)) (fee rule : Rule code) :
    focus code active (project code active fee rule) = focus code active rule := by
  unfold project
  split
  · rename_i same;rw [same]
  · split
    · exact mask_preserves_the_original_owner_projection code active [] rule
    · split
      · exact mask_preserves_the_original_owner_projection code active _ rule
      · contradiction

theorem projection_keeps_exact_fee_identity (active : List (Fin code.sites)) (fee rule : Rule code) :
    project code active fee rule = fee ↔ rule = fee := by
  unfold project
  split
  · simp_all
  · rename_i distinct
    split
    · simp_all
    · split
      · rename_i key found
        have different := difference_is_a_real_row code rule fee key found
        have kept := mask_keeps_each_requested_row code active [key] rule key (.inr (List.mem_singleton_self _))
        have notFee : mask code active [key] rule ≠ fee := by
          intro same
          rw [same] at kept
          exact different ⟨kept.1.symm,kept.2.symm⟩
        simp only [notFee,distinct,iff_self]
      · contradiction

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded
