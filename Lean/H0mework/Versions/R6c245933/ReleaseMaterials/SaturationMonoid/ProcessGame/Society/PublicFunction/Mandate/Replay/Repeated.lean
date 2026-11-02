import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Repeated
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (before : RawCurrent Party Good (State Party Technology) Instrument)
  (request : Request Party Good Port (State Party Technology) Instrument)

/-- The unvisited invoice suffix remains its original Nat-indexed word. -/
structure Result (count : Nat) where
  private mk ::
  output : List (Request Party Good Port (State Party Technology) Instrument)
  consumed : List (Request Party Good Port (State Party Technology) Instrument)
  succeeded : Bool
  output_exact : output = (compile base scope before (List.replicate count request)).output
  consumed_exact : consumed = (compile base scope before (List.replicate count request)).consumed
  succeeded_exact : succeeded = (compile base scope before (List.replicate count request)).succeeded

/-- Execute each original invoice unit at its actual cut; stop at its first refusal. -/
@[noinline, never_extract] def generate
    (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (before : RawCurrent Party Good (State Party Technology) Instrument)
    (request : Request Party Good Port (State Party Technology) Instrument) :
    (count : Nat) → Result base scope before request count
  | 0 => ⟨[],[],true,rfl,rfl,rfl⟩
  | count+1 =>
      if valid : (Mandate.law base scope).Valid before (rebase scope before request) then
        let rest := generate base scope
          ((Mandate.law base scope).step before (rebase scope before request)) request count
        ⟨rebase scope before request::rest.output,request::rest.consumed,rest.succeeded,
          by simp only [List.replicate_succ,compile,dif_pos valid,Path.output,rest.output_exact],
          by simp only [List.replicate_succ,compile,dif_pos valid,Path.consumed,rest.consumed_exact],
          by simp only [List.replicate_succ,compile,dif_pos valid,Path.succeeded,rest.succeeded_exact]⟩
      else ⟨[rebase scope before request],[],false,
        by simp only [List.replicate_succ,compile,dif_neg valid,Path.output],
        by simp only [List.replicate_succ,compile,dif_neg valid,Path.consumed],
        by simp only [List.replicate_succ,compile,dif_neg valid,Path.succeeded]⟩

namespace Result
variable {base scope before request} {count : Nat}

theorem failure_is_an_actual_raw_item (made : Result base scope before request count)
    (failure : made.succeeded = false) :
    ∃ item ∈ (Mandate.law base scope).rawItems before made.output,
      item.index = made.consumed.length ∧ ¬ (Mandate.law base scope).Valid item.before item.request := by
  have refused : (compile base scope before (List.replicate count request)).succeeded = false :=
    made.succeeded_exact.symm.trans failure
  simpa only [made.output_exact,made.consumed_exact] using
    (compile base scope before (List.replicate count request)).failure_is_an_actual_raw_item refused

theorem output_is_bounded_by_the_original_word (made : Result base scope before request count) :
    made.output.length ≤ count := by
  rw [made.output_exact]
  exact (compile base scope before (List.replicate count request)).output_is_bounded_by_the_original_word.trans_eq
    (List.length_replicate ..)

end Result
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Repeated
