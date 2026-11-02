import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Checks
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Scan
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}

inductive Operation where
  | query (event : NativeBenefit.Event (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)))
  | keep (current other : (Offer (prepared := prepared) (position := position)))
  | replace (current other : (Offer (prepared := prepared) (position := position)))
  | finish
  | skip (candidate : (Offer (prepared := prepared) (position := position)))
  | found (candidate : (Offer (prepared := prepared) (position := position)))
  | missing

variable (pool : List (Offer (prepared := prepared) (position := position)))
def Strict (previous new : (Offer (prepared := prepared) (position := position))) := ResponsibilityLe pool new previous ∧ ¬ResponsibilityLe pool previous new

def maxBudget := (pool.flatMap fun previous => pool.map (fun new => Checks.strictBudget pool previous new)).foldr Nat.max 0
private theorem member_le_max {value : Nat} {values : List Nat} (inside : value ∈ values) : value ≤ values.foldr Nat.max 0 := by
  induction values with
  | nil => cases inside
  | cons head tail ih =>
      rcases List.mem_cons.mp inside with same | later
      · subst value;exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)
theorem strict_budget_is_source_bounded (previous new : (Offer (prepared := prepared) (position := position))) (first : previous ∈ pool) (second : new ∈ pool) :
    Checks.strictBudget pool previous new ≤ maxBudget pool :=
  member_le_max (List.mem_flatMap.mpr ⟨previous,first,List.mem_map.mpr ⟨new,second,rfl⟩⟩)

structure Scanned (current : (Offer (prepared := prepared) (position := position))) (remaining : List (Offer (prepared := prepared) (position := position))) where
  private mk ::
  policy : (Offer (prepared := prepared) (position := position))
  original : policy = current ∨ policy ∈ remaining
  no_worse : ResponsibilityLe pool policy current
  maximal : ∀ other ∈ remaining,¬ Strict pool policy other
  work : List (Operation (prepared := prepared) (position := position))
  bound : work.length ≤ remaining.length*(maxBudget pool+1)+1

def scan (current : (Offer (prepared := prepared) (position := position))) (original : current ∈ pool) :
    (remaining : List (Offer (prepared := prepared) (position := position))) → (within : ∀ other ∈ remaining,other ∈ pool) → Scanned pool current remaining
  | [],_ => ⟨current,.inl rfl,responsibility_refl pool current,(by intro other inside;cases inside),[.finish],(by simp)⟩
  | head::tail,within =>
      let tested := Checks.strict pool current head
      match tested.check.decision with
      | .isTrue better =>
          let result := scan head (within head List.mem_cons_self) tail (fun other inside => within other (List.mem_cons_of_mem _ inside))
          ⟨result.policy,.inr (by
              rcases result.original with same | inside
              · rw [same];exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ inside),
            responsibility_trans pool result.no_worse better.1,
            (by intro other inside
                rcases List.mem_cons.mp inside with same | later
                · subst other;exact fun backwards => backwards.2 result.no_worse
                · exact result.maximal other later),
            tested.check.work.map Operation.query ++ [.replace current head] ++ result.work,
            (by have a := tested.bound
                have b := strict_budget_is_source_bounded pool current head original (within head List.mem_cons_self)
                have c := result.bound
                simp only [List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]
                omega)⟩
      | .isFalse notBetter =>
          let result := scan current original tail (fun other inside => within other (List.mem_cons_of_mem _ inside))
          ⟨result.policy,result.original.imp_right (List.mem_cons_of_mem _),result.no_worse,
            (by intro other inside
                rcases List.mem_cons.mp inside with same | later
                · subst other;intro backwards
                  exact notBetter ⟨responsibility_trans pool backwards.1 result.no_worse,
                    fun reverse => backwards.2 (responsibility_trans pool result.no_worse reverse)⟩
                · exact result.maximal other later),
            tested.check.work.map Operation.query ++ [.keep current head] ++ result.work,
            (by have a := tested.bound
                have b := strict_budget_is_source_bounded pool current head original (within head List.mem_cons_self)
                have c := result.bound
                simp only [List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]
                omega)⟩

structure Located (ordinal : Nat) where
  private mk ::
  value : Option (Offer (prepared := prepared) (position := position))
  exact : value = pool[ordinal]?
  work : List (Operation (prepared := prepared) (position := position))
  bound : work.length ≤ pool.length+1

def locate : (ordinal : Nat) → Located pool ordinal := by
  intro ordinal
  induction pool generalizing ordinal with
  | nil => exact ⟨none,rfl,[.missing],Nat.le_refl _⟩
  | cons head tail ih =>
      cases ordinal with
      | zero => exact ⟨some head,rfl,[.found head],by simp only [List.length_cons,List.length_nil];omega⟩
      | succ ordinal =>
          let later := ih ordinal
          exact ⟨later.value,later.exact,.skip head::later.work,by
            have := later.bound
            simp only [List.length_cons]
            omega⟩

structure Answer (reference : (Offer (prepared := prepared) (position := position))) where
  private mk ::
  policy : (Offer (prepared := prepared) (position := position))
  original : policy ∈ pool
  no_worse : ResponsibilityLe pool policy reference
  maximal : ∀ other ∈ pool,¬ Strict pool policy other
  work : List (Operation (prepared := prepared) (position := position))
  bound : work.length ≤ pool.length*(maxBudget pool+1)+1

def refine (reference : (Offer (prepared := prepared) (position := position))) (original : reference ∈ pool) : Answer pool reference :=
  let result := scan pool reference original pool (fun _ inside => inside)
  ⟨result.policy,(by
      rcases result.original with same | inside
      · rw [same];exact original
      · exact inside),result.no_worse,result.maximal,result.work,result.bound⟩

theorem every_available_strict_improvement_is_selected (reference : (Offer (prepared := prepared) (position := position))) (original : reference ∈ pool)
    (available : ∃ other ∈ pool,Strict pool reference other) : Strict pool reference (refine pool reference original).policy := by
  refine ⟨(refine pool reference original).no_worse,?_⟩
  intro backwards
  obtain ⟨other,inside,forward,strict⟩ := available
  exact (refine pool reference original).maximal other inside
    ⟨responsibility_trans pool forward backwards,fun reverse => strict (responsibility_trans pool backwards reverse)⟩

theorem independently_verified (reference : (Offer (prepared := prepared) (position := position))) (original : reference ∈ pool) :
    Choice.verify pool reference (refine pool reference original).policy = true :=
  decide_eq_true ⟨(refine pool reference original).no_worse,(refine pool reference original).maximal⟩

variable {pool}
inductive Resolution (audit : CrossFee.Result prepared position) (ordinal : Nat) where
  | noReference (looked : Located (Pool.collect audit) ordinal) (absent : looked.value = none)
  | selected (looked : Located (Pool.collect audit) ordinal) (reference : (Offer (prepared := prepared) (position := position)))
      (located : looked.value = some reference) (answer : Answer (Pool.collect audit) reference)

def compile (audit : CrossFee.Result prepared position) (ordinal : Nat) : Resolution audit ordinal :=
  let looked := locate (Pool.collect audit) ordinal
  match actual : looked.value with
  | none => .noReference looked actual
  | some reference => .selected looked reference actual (refine (Pool.collect audit) reference (List.mem_of_getElem? (looked.exact.symm.trans actual)))

def budget (audit : CrossFee.Result prepared position) :=
  (Pool.collect audit).length*((maxBudget (Pool.collect audit))+1)+(Pool.collect audit).length+2

def Resolution.work {audit : CrossFee.Result prepared position} {ordinal : Nat} : Resolution (prepared := prepared) (position := position) audit ordinal → List (Operation (prepared := prepared) (position := position))
  | .noReference looked _ => looked.work
  | .selected looked _ _ answer => looked.work++answer.work

theorem Resolution.fits {audit : CrossFee.Result prepared position} {ordinal : Nat} (result : Resolution audit ordinal) : result.work.length ≤ budget audit := by
  cases result with
  | noReference looked absent => have := looked.bound;dsimp only [work,budget];omega
  | selected looked reference located answer =>
      have a := looked.bound;have b := answer.bound
      dsimp only [work,budget]
      rw [List.length_append]
      omega

noncomputable def Resolution.next {audit : CrossFee.Result prepared position} {ordinal : Nat} {Payload : Type}
    (payload : Payload) (result : Resolution audit ordinal) (index : Index prepared) : AuthorityCurrent :=
  match result with
  | .noReference _ _ => Choice.retainedNext payload audit (Choice.afterIndex audit index)
  | .selected _ _ _ answer => answer.policy.next payload index

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Scan
