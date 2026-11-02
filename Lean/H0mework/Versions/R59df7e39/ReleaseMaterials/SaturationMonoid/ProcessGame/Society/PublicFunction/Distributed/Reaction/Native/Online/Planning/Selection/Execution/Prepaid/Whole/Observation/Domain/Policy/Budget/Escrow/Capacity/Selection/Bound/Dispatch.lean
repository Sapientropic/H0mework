import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Bound
import Mathlib.Logic.Equiv.Fin.Basic
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.PaidDispatch
open Institutions.Capitalism.Universal.Source.Program
inductive Field where
  | sections | atoms | tables | words | rows | keys
  deriving DecidableEq
inductive Instruction where
  | source (field : Field)
  | literal (value : Nat)
  | cached (slot : Fin 8)
  | save (slot : Fin 8)
  | add | multiply
  deriving DecidableEq

def code : List Instruction :=
  [.source .sections,.save 5,.source .atoms,.save 0,.source .tables,.save 1,.source .words,.save 2,.source .rows,
   .cached 0,.literal 1,.add,.multiply,.save 3,.source .keys,.cached 1,.cached 0,.literal 3,
   .add,.literal 2,.cached 2,.multiply,.cached 0,.literal 1,.add,.multiply,.add,
   .multiply,.literal 1,.add,.multiply,.save 4,.literal 2,.cached 4,.multiply,.literal 2,
   .add,.save 6,.cached 3,.literal 1,.add,.cached 5,.cached 3,.cached 6,.add,
   .literal 3,.add,.multiply,.add,.save 7,.cached 5,.cached 3,.literal 1,.add,
   .multiply,.cached 5,.cached 6,.literal 1,.add,.multiply,.add,.cached 7,.add,
   .cached 5,.cached 3,.multiply,.add,.literal 1,.add]

inductive Phase where
  | initial | actual
  deriving DecidableEq
def Phase.index : Phase → Fin 2 | .initial => 0 | .actual => 1
abbrev Token := Phase × Fin code.length
def tokens (phase : Phase) : List Token := (List.finRange code.length).map (phase,·)
def allTokens := tokens .initial ++ tokens .actual
def units := 2*code.length
def ordinal (token : Token) : Fin units := finProdFinEquiv (token.1.index,token.2)
theorem phase_index_injective : Function.Injective Phase.index := by intro a b same;cases a <;> cases b <;> simp_all [Phase.index]
theorem ordinal_injective : Function.Injective ordinal := by
  intro a b same
  have pairs := finProdFinEquiv.injective same
  have phases : a.1.index = b.1.index := congrArg (fun x : Fin 2 × Fin code.length => x.1) pairs
  have slots : a.2 = b.2 := congrArg (fun x : Fin 2 × Fin code.length => x.2) pairs
  exact Prod.ext (phase_index_injective phases) slots
theorem both_phase_allocations_have_exactly_the_prepaid_size : allTokens.length = units := by
  simp only [allTokens,tokens,List.length_append,List.length_map,List.length_finRange,units];omega

variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue)

def Field.expected : Field → Nat
  | .sections => (PublicPolicy.sections pool).length
  | .atoms => Work.atomCeiling pool
  | .tables => Work.tableCeiling pool
  | .words => Work.wordCeiling pool
  | .rows => (PublicPolicy.rows pool).length
  | .keys => (Policy.keys prepared).length

def Field.calculate : (field : Field) → Bound.Run pool (field.expected pool)
  | .sections => Bound.lift (Policy.Budget.length (PublicPolicy.sections pool))
  | .atoms => Bound.annotate (.domain (Work.queries pool)) (by trivial)
      (Bound.ceiling pool (Work.atomBudget pool) (Bound.atom pool) (Work.queries pool))
  | .tables => Bound.ceiling pool (fun index : Index prepared => (Comparison.tables pool index).length)
      (fun index => Bound.lift (Policy.Budget.length (Comparison.tables pool index))) (Policy.keys prepared)
  | .words => Bound.ceiling pool (fun index : Index prepared => (Work.capabilityWords index).length)
      (fun index => Bound.lift (Policy.Budget.length (Work.capabilityWords index))) (Policy.keys prepared)
  | .rows => Bound.lift (Policy.Budget.length (PublicPolicy.rows pool))
  | .keys => Bound.lift (Policy.Budget.length (Policy.keys prepared))

structure Programme (expected : Nat) where
  private mk ::
  run : Bound.Run pool expected
  trace : List Instruction
variable {pool}
private def source (pool : Comparison.Pool catalogue) (field : Field) : Programme pool (field.expected pool) := ⟨field.calculate pool,[.source field]⟩
private def literal (value : Nat) : Programme pool value := ⟨Bound.lit value,[.literal value]⟩
private def save {n : Nat} (slot : Fin 8) (made : Programme pool n) : Programme pool n := ⟨made.run,made.trace ++ [.save slot]⟩
private def cached {n : Nat} (slot : Fin 8) (made : Programme pool n) : Programme pool n := ⟨Bound.borrow slot.val made.run,[.cached slot]⟩
private def add {a b : Nat} (left : Programme pool a) (right : Programme pool b) : Programme pool (a+b) :=
  ⟨Bound.plus left.run right.run,left.trace ++ right.trace ++ [.add]⟩
private def multiply {a b : Nat} (left : Programme pool a) (right : Programme pool b) : Programme pool (a*b) :=
  ⟨Bound.times left.run right.run,left.trace ++ right.trace ++ [.multiply]⟩
private def retain {a b : Nat} (prior : Programme pool a) (later : Programme pool b) : Programme pool b :=
  ⟨Bound.retain prior.run later.run,prior.trace ++ later.trace⟩

variable (pool)
def generate : Programme pool (Work.workBudget pool) :=
  let count := save 5 (source pool .sections)
  let atoms := save 0 (source pool .atoms)
  let tables := save 1 (source pool .tables)
  let words := save 2 (source pool .words)
  let admission := save 3 (multiply (source pool .rows) (add (cached 0 atoms) (literal 1)))
  let benefit := save 4 (multiply (source pool .keys)
    (add (multiply (cached 1 tables) (add (add (cached 0 atoms) (literal 3))
      (multiply (multiply (literal 2) (cached 2 words)) (add (cached 0 atoms) (literal 1))))) (literal 1)))
  let strict := save 6 (add (multiply (literal 2) (cached 4 benefit)) (literal 2))
  let verification := save 7 (add (add (cached 3 admission) (literal 1))
    (multiply (cached 5 count) (add (add (cached 3 admission) (cached 6 strict)) (literal 3))))
  let first := multiply (cached 5 count) (add (cached 3 admission) (literal 1))
  let second := multiply (cached 5 count) (add (cached 6 strict) (literal 1))
  let total := add (add first second) (cached 7 verification)
  let result := add (add total (multiply (cached 5 count) (cached 3 admission))) (literal 1)
  retain count (retain atoms (retain tables (retain words (retain admission (retain benefit (retain strict (retain verification result)))))))

theorem generated_run_is_the_original_cached_source_budget : (generate pool).run = Bound.generate pool := by rfl
theorem generated_dispatch_is_the_fixed_source_program : (generate pool).trace = code := by rfl
theorem all_body_events_have_their_original_validity : ∀ event ∈ (generate pool).run.work,event.Valid pool := (generate pool).run.sound

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.PaidDispatch
