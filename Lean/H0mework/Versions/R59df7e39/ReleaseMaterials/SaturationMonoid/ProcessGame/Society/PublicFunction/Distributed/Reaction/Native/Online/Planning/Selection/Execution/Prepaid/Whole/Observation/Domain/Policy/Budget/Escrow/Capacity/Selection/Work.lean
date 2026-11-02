import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Work.Core
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Work
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue)

/-- Only local Boolean control is expanded here. Every delegated native event keeps its complete payload. -/
def Operation.isControl : Operation pool → Bool
  | .branch .. | .negate .. | .retain .. | .select .. => true
  | _ => false
abbrev NativeDebt := { event : Operation pool // event.isControl pool = false }
def pending : List (Operation pool) → List (NativeDebt pool)
  | [] => []
  | head::tail => if h : head.isControl pool = false then ⟨head,h⟩::pending tail else pending tail
def controlSteps (work : List (Operation pool)) := (work.filter (Operation.isControl pool)).length

theorem every_native_payload_and_control_occurrence_is_retained (work : List (Operation pool)) :
    work.length = controlSteps pool work+(pending pool work).length := by
  induction work with
  | nil => rfl
  | cons head tail ih =>
    cases same : head.isControl pool <;> simp_all [pending,controlSteps] <;> omega

theorem each_pending_event_has_its_original_occurrence (work : List (Operation pool)) (debt : NativeDebt pool)
    (inside : debt ∈ pending pool work) : debt.val ∈ work := by
  induction work with
  | nil => simp [pending] at inside
  | cons head tail ih =>
    unfold pending at inside
    split at inside
    · rcases List.mem_cons.mp inside with same | rest
      · exact List.mem_cons.mpr (.inl (congrArg Subtype.val same))
      · exact List.mem_cons_of_mem _ (ih rest)
    · exact List.mem_cons_of_mem _ (ih inside)

structure Generated where
  private mk ::
  compilation : Compilation pool
  compiled : compilation = compile pool
  receipt : Receipt pool compilation
  reviewed : receipt = certify pool compilation

def generate : Generated pool :=
  let compilation := compile pool
  ⟨compilation,rfl,certify pool compilation,rfl⟩

namespace Generated
variable {pool} (made : Generated pool)
def work : List (Operation pool) := made.receipt.work
def outcome : Outcome pool := made.compilation.result.outcome pool

theorem independent_review_accepts : made.receipt.review.value = true :=
  made.receipt.review_accepts_its_generated_result

theorem selected_review_is_the_original_public_verifier :
    made.receipt.authorized = Outcome.checked pool made.outcome :=
  made.receipt.authorized_matches_the_original_independent_verifier

inductive Debt (made : Generated pool) where
  | prior (debt : Comparison.Pool.Debt pool)
  | native (debt : NativeDebt pool)
  | enumeration
  | jointFrames
  | primitiveInternals
  | budgetGeneration
  | prepayment
  | storage
  | announcement

def debts : List (Debt made) := pool.pending.map Debt.prior ++
  (pending pool made.work).map Debt.native ++
  [.enumeration,.jointFrames,.primitiveInternals,.budgetGeneration,.prepayment,.storage,.announcement]

theorem every_prior_debt_survives (debt : Comparison.Pool.Debt pool) (inside : debt ∈ pool.pending) :
    Debt.prior debt ∈ made.debts := by
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨debt,inside,rfl⟩))
theorem every_native_debt_survives (debt : NativeDebt pool) (inside : debt ∈ pending pool made.work) :
    Debt.native debt ∈ made.debts := by
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨debt,inside,rfl⟩))
theorem source_trace_conserves_all_occurrences :
    made.work.length = controlSteps pool made.work+(pending pool made.work).length :=
  every_native_payload_and_control_occurrence_is_retained pool made.work
end Generated

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Work
