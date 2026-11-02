import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.CapacityBound.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.CapacityBound
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol

namespace Uniform
variable {Key α : Type} [DecidableEq Key] (R : α → α → Prop) (pool : List α)
  (reflexive : ∀ item,R item item) (transitive : ∀ {a b c},R a b → R b c → R a c)
  (test : (previous candidate : α) → Code Key (.truth (R candidate previous ∧ ¬R previous candidate)))
  (limit : Nat) (within : ∀ left right : Fin pool.length,(test pool[left] pool[right]).cost ≤ limit)

include within
theorem scan_bound (current : Fin pool.length) (remaining : List (Fin pool.length)) :
    (Query.Refiner.Generic.scan R pool reflexive transitive test current remaining).cost ≤ 1+remaining.length*(limit+3) := by
  induction remaining generalizing current with
  | nil => simp [Query.Refiner.Generic.scan,Code.cost]
  | cons head tail ih =>
      apply Nat.le_trans (bind_bound _ _ (within current head) (b := 1+tail.length*(limit+3)+2) ?_)
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega
      intro answer;cases answer with
      | isFalse notBetter =>
          apply Nat.le_trans (bind_bound _ _ (ih current) (b := 1) ?_)
          · omega
          intro later;exact Nat.le_refl 1
      | isTrue better =>
          apply Nat.le_trans (bind_bound _ _ (ih head) (b := 1) ?_)
          · omega
          intro later;exact Nat.le_refl 1
end Uniform

variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}
variable (pool : List (Offer (prepared := prepared) (position := position)))

-- Only the structural source bounds are folded; no query evaluator or comparison answer is read.
def maximum := (pool.flatMap fun previous => pool.map (fun new => Shapes.strict pool previous new)).foldr Nat.max 0
private theorem member_le_max {value : Nat} {values : List Nat} (inside : value ∈ values) : value ≤ values.foldr Nat.max 0 := by
  induction values with
  | nil => cases inside
  | cons head tail ih =>
      rcases List.mem_cons.mp inside with same | later
      · subst value;exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

theorem maximum_covers (left right : Fin pool.length) : (Query.Source.strict pool pool[left] pool[right]).cost ≤ maximum pool :=
  (Shapes.strict_bound pool pool[left] pool[right]).trans (member_le_max (List.mem_flatMap.mpr
    ⟨pool[left],List.getElem_mem _,List.mem_map.mpr ⟨pool[right],List.getElem_mem _,rfl⟩⟩))

def budget := 9+pool.length*(maximum pool+3)

theorem program_bound (ordinal : Nat) : (Query.Refiner.program pool ordinal).cost ≤ budget pool := by
  unfold Query.Refiner.program
  have first : (Code.atom (.natural (ordinal+1) pool.length) : Code
      (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (.truth (ordinal+1 ≤ pool.length))).cost ≤ 2 := Nat.le_refl 2
  apply Nat.le_trans (bind_bound _ _ first (b := 1+pool.length*(maximum pool+3)+5) ?_)
  · dsimp only [budget];omega
  intro answer;cases answer with
  | isFalse absent => change 1 ≤ _;omega
  | isTrue enough =>
      apply Nat.le_trans (bind_bound _ _
        (Uniform.scan_bound (ResponsibilityLe pool) pool (responsibility_refl pool)
          (fun {a b c} => responsibility_trans pool (first := a) (middle := b) (last := c))
          (Query.Source.strict pool) (maximum pool) (maximum_covers pool) _ (List.finRange pool.length)) (b := 4) ?_)
      · rw [List.length_finRange];omega
      intro selected
      refine bind_bound _ _ (a := 2) (b := 1) ?_ ?_
      · exact Nat.le_refl 2
      intro encoded;exact Nat.le_refl 1

theorem initial_rank_bound (ordinal : Nat) : (Query.initial (Query.Refiner.program pool ordinal)).rank ≤ budget pool := by
  simpa only [Query.initial,State.rank,Phase.rank,Kont.cost,Nat.add_zero] using program_bound pool ordinal

theorem source_capacity_completes (ordinal : Nat) :
    (Query.run (budget pool) (Query.initial (Query.Refiner.program pool ordinal))).endpoint.completed.isSome = true :=
  Query.run_sufficient _ _ (initial_rank_bound pool ordinal)

variable {pool}
theorem completed_work_is_source_bounded {ordinal : Nat} (state : Query.State (Query.Refiner.program pool ordinal))
    (capacity : Nat) (made : Query.Run (Query.initial (Query.Refiner.program pool ordinal)) capacity)
    (actual : made.endpoint = state) (finished : state.completed.isSome = true) : made.work.length ≤ budget pool := by
  have stopped := (State.completed_iff_stopped state).mp finished
  have zero := (State.stopped_iff_zero state).mp stopped
  have conservation := made.conservation
  rw [actual,zero] at conservation
  have := initial_rank_bound pool ordinal;omega

section PaidConsumer
variable {budgetChoice : CandidateRuntime.BudgetChoice prepared} {outer : Option Nat}
  {reading : Query.Payment.Refiner.Reading prepared budgetChoice outer position}
  {cache : Computation.Collection.Completed reading.opened.audit} {ordinal : Nat}

theorem actual_session_completes (session : Query.Payment.Refiner.Session reading cache ordinal)
    (funded : budget cache.items ≤ reading.remaining) : session.run.endpoint.completed.isSome = true :=
  session.sufficient_completes ((initial_rank_bound cache.items ordinal).trans funded)

-- A smaller upper-bound reservation is still executed by the original machine; only its actual endpoint decides pending.
theorem actual_pending_is_below_bound (session : Query.Payment.Refiner.Session reading cache ordinal)
    (pending : session.run.endpoint.completed = none) : reading.remaining < budget cache.items := by
  by_contra notSmall
  have done := actual_session_completes session (Nat.le_of_not_gt notSmall)
  rw [pending] at done;cases done
end PaidConsumer

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.CapacityBound
