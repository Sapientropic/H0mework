import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair.Focus

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

def alphabet (current : RawCurrent Party Good Technology Instrument) :=
  input.localAttempts current ++ ProgrammeSource.wordAt input current

/-- These are proposals, not grants of authority. Signatures, gates and
consents are never edited; the original `law.step` still decides them. -/
def Relevant (current : RawCurrent Party Good Technology Instrument)
    (focus : Focus (Party := Party) (Good := Good) (Port := Port))
    (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .produce _ | .transfer .. =>
      ∃ cell ∈ focus.cells, 0 < flowAt (input.law.credit current request) cell.1 cell.2
  | .revise _ technology =>
      (∃ cell ∈ focus.cells,
        amount Good (input.law.technique current.technology cell.1).outputs cell.2 <
          amount Good (input.law.technique technology cell.1).outputs cell.2 ∨
        amount Good (input.law.technique technology cell.1).inputs cell.2 <
          amount Good (input.law.technique current.technology cell.1).inputs cell.2) ∨
      (∃ port ∈ focus.ports, ∃ person ∈ Migration.cohort input depth count,
        input.law.allowed current.technology port person = false ∧ input.law.allowed technology port person = true)
  | _ => False

instance (current : RawCurrent Party Good Technology Instrument)
    (focus : Focus (Party := Party) (Good := Good) (Port := Port))
    (request : Request Party Good Port Technology Instrument) : Decidable (Relevant input depth count current focus request) := by
  unfold Relevant
  cases request.operation <;> infer_instance

theorem relevant_is_nonfinancial (current : RawCurrent Party Good Technology Instrument)
    (focus : Focus (Party := Party) (Good := Good) (Port := Port))
    (request : Request Party Good Port Technology Instrument) (relevant : Relevant input depth count current focus request) :
    Settlement.NonFinancialRequest request := by
  cases operation : request.operation <;> simp_all [Relevant, Settlement.NonFinancialRequest]

structure AttemptAt (current : RawCurrent Party Good Technology Instrument)
    (focus : Focus (Party := Party) (Good := Good) (Port := Port)) (remaining : List (Request Party Good Port Technology Instrument)) where
  private mk ::
  request : Request Party Good Port Technology Instrument
  original : request ∈ remaining
  relevant : Relevant input depth count current focus request
  tail : List (Request Party Good Port Technology Instrument)
  skipped : List (Request Party Good Port Technology Instrument)
  inventory : remaining = skipped ++ request :: tail
  noEarlier : ∀ earlier ∈ skipped, ¬ Relevant input depth count current focus earlier

inductive Choice (current : RawCurrent Party Good Technology Instrument)
    (focus : Focus (Party := Party) (Good := Good) (Port := Port)) (remaining : List (Request Party Good Port Technology Instrument)) : Type
  | attempt (selected : AttemptAt input depth count current focus remaining)
  | exhausted (rejected : ∀ request ∈ remaining, ¬ Relevant input depth count current focus request)

def choose (current : RawCurrent Party Good Technology Instrument)
    (focus : Focus (Party := Party) (Good := Good) (Port := Port)) :
    (remaining : List (Request Party Good Port Technology Instrument)) → Choice input depth count current focus remaining
  | [] => .exhausted (by simp)
  | request :: tail =>
      if relevant : Relevant input depth count current focus request then
        .attempt ⟨request, List.mem_cons_self, relevant, tail, [], rfl, by simp⟩
      else match choose current focus tail with
        | .exhausted rejected => .exhausted (by
            intro item present
            rcases List.mem_cons.mp present with same | later
            · cases same; exact relevant
            · exact rejected item later)
        | .attempt selected => .attempt ⟨selected.request, List.mem_cons_of_mem _ selected.original,
            selected.relevant, selected.tail, request :: selected.skipped,
            congrArg (List.cons request) selected.inventory,
            by
              intro item present
              rcases List.mem_cons.mp present with same | later
              · cases same; exact relevant
              · exact selected.noEarlier item later⟩

theorem attempted_inventory_strictly_decreases
    {current : RawCurrent Party Good Technology Instrument}
    {focus : Focus (Party := Party) (Good := Good) (Port := Port)}
    {remaining : List (Request Party Good Port Technology Instrument)}
    (attempt : AttemptAt input depth count current focus remaining) : attempt.tail.length < remaining.length := by
  have sizes := congrArg List.length attempt.inventory
  simp only [List.length_append, List.length_cons] at sizes
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair
