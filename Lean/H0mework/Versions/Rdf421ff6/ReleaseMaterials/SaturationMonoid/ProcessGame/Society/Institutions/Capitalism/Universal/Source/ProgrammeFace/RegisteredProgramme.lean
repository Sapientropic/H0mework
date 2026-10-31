import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.RootReader
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Lifecycle
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory

/-! Exact reads of the programme admitted by the original first write.
Its birth anchor is that write's generated first instruction occurrence.
All responsibility pointers below are the original source inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle.Universal Relations Power Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

def reader : OriginalProgrammeReader (Root.ProgrammeSource.ledgerSource input) input.law where
  current := Root.ProgrammeSource.rawCurrent input
  event := fun {current} _ => Root.ProgrammeSource.rawEvent input current
  next_exact := by
    intro current event
    have same := Root.ProgrammeSource.occurrence_eq_emitted input event.val
    rcases event with ⟨event, continues⟩
    dsimp at same
    cases same
    exact Root.ProgrammeSource.actual_raw_next input current

def genesis : OriginalOccurrence (Root.ProgrammeSource.ledgerSource input) :=
  ⟨Root.ProgrammeSource.next input .bootstrap, Root.ProgrammeSource.emitted input (Root.ProgrammeSource.next input .bootstrap)⟩

def actualOccurrence (index : Nat) : OriginalOccurrence (Root.ProgrammeSource.ledgerSource input) :=
  ⟨(Root.ProgrammeHistory.visitAt input index).current,
    Root.ProgrammeSource.emitted input (Root.ProgrammeHistory.visitAt input index).current⟩

omit [DecidableEq Port] in
theorem genesis_is_actual_first_instruction_visit :
    genesis input = actualOccurrence input 1 := rfl

omit [DecidableEq Port] in
theorem original_genesis_retained_by_every_later_visit (index : Nat) :
    Root.ProgrammeSource.rawCurrent input (genesis input).1 ∈
      Root.ProgrammeSource.pastAt (actualOccurrence input (index + 2)).1 :=
  Root.ProgrammeHistory.first_instruction_occurrence_retained input index

def bootstrapEvent : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) .bootstrap :=
  ⟨Root.ProgrammeSource.emitted input .bootstrap, rfl⟩

omit [DecidableEq Port] in
theorem genesis_is_original_first_write_target :
    (genesis input).1 = actualTarget (bootstrapEvent input) := rfl

def society : ExistingSocietyFace (Root.ProgrammeSource.ledgerSource input) :=
  Anchored.society input.law (Root.ProgrammeSource.ledgerSource input) (reader input).raw (genesis input)

abbrev BirthSeed := Anchored.BirthSeed input.law (reader input).raw (genesis input)

def lifecycle (occurrence : OriginalOccurrence (Root.ProgrammeSource.ledgerSource input)) :=
  Anchored.lifecycle input.law (reader input).raw (genesis input) occurrence

def actualIdentity (index : Nat) (seed : BirthSeed input)
    (present : seed.val ∈ parties input.law ((reader input).raw (actualOccurrence input (index + 1)))) :=
  Anchored.identityTransport input.law (reader input).raw (genesis input)
    (actualOccurrence input (index + 1)) seed present

theorem actual_successor_keeps_original_actor (index : Nat) (seed : BirthSeed input)
    (present : seed.val ∈ parties input.law ((reader input).raw (actualOccurrence input (index + 1))))
    (presentNext : seed.val ∈ parties input.law ((reader input).raw (actualOccurrence input (index + 2)))) :
    ((Anchored.identitySeed input.law (reader input).raw (genesis input)
      (actualOccurrence input (index + 1)) seed present).targetActor
        (lifecycle input (actualOccurrence input (index + 1)))).val =
      (Anchored.actor input.law (reader input).raw (genesis input)
        (actualOccurrence input (index + 2)) seed presentNext).val := rfl

theorem lifecycle_target_is_original {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current) :
    (lifecycle input (originalOccurrence event)).targetFace.state (originalOccurrence event) =
      Point.target (Root.ProgrammeSource.rawCurrent input (actualTarget event)) := by
  change Point.target (input.law.next (Root.ProgrammeSource.rawCurrent input current) (Root.ProgrammeSource.rawEvent input current)) = _
  exact congrArg Point.target ((reader input).next_exact event).symm

def instruction (current : RawCurrent Party Good Technology Instrument)
    (index : Fin input.instructions.length) : ExecutionItem Party Good Port Technology Instrument :=
  (input.law.rawItems current input.instructions).get
    ⟨index.val, by
      simpa only [RawLaw.rawItems, input.law.inventory_length] using index.isLt⟩

omit [DecidableEq Port] in
theorem instruction_mem (current : RawCurrent Party Good Technology Instrument)
    (index : Fin input.instructions.length) :
    instruction input current index ∈ input.law.rawItems current input.instructions :=
  List.get_mem _ _

def staticIndex (fixed : input.emission? = none)
    (index : Fin (Root.ProgrammeSource.registrationSize input)) : Fin input.instructions.length :=
  ⟨index.val, by
    simpa only [Root.ProgrammeSource.registrationSize, fixed] using index.isLt⟩

def originalInstruction {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : OriginalInventoryItem event) : Option (ExecutionItem Party Good Port Technology Instrument) := by
  rcases event with ⟨⟨support, native⟩, continues⟩
  cases native
  cases current with
  | bootstrap => exact none
  | running raw past =>
      exact match emission : input.emission? with
      | some _ => none
      | none => match item.1 with
        | .inherited | .obstruction => none
        | .instruction index => some (instruction input raw (staticIndex input emission index))

omit [DecidableEq Port] in
theorem originalInstruction_generated_none {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : OriginalInventoryItem event)
    (emit : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit) : originalInstruction input event item = none := by
  rcases event with ⟨⟨support, native⟩, continues⟩
  cases native
  cases current with
  | bootstrap => rfl
  | running state past =>
      dsimp only [originalInstruction]
      split
      · rfl
      · rename_i fixed
        cases fixed.symm.trans generated

omit [DecidableEq Port] in
theorem originalInstruction_running_fixed
    (state : RawCurrent Party Good Technology Instrument)
    (past : List (RawCurrent Party Good Technology Instrument))
    (row : Root.ProgrammeWorld.Row (Root.ProgrammeSource.registrationSize input))
    (fixed : input.emission? = none) :
    originalInstruction input
      ⟨Root.ProgrammeSource.emitted input (.running state past), rfl⟩
      (Root.ProgrammeSource.sourceEntry input (.running state past) row) =
      match row with
      | .inherited | .obstruction => none
      | .instruction index => some (instruction input state (staticIndex input fixed index)) := by
  dsimp only [originalInstruction, Root.ProgrammeSource.sourceEntry, Root.ProgrammeSource.emitted]
  split
  · rename_i emit generated
    cases fixed.symm.trans generated
  · rfl

omit [DecidableEq Port] in
theorem originalInstruction_mem {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : OriginalInventoryItem event) (raw : ExecutionItem Party Good Port Technology Instrument)
    (decoded : originalInstruction input event item = some raw) :
    raw ∈ input.law.rawItems (Root.ProgrammeSource.rawCurrent input current) (Root.ProgrammeSource.rawEvent input current) := by
  rcases event with ⟨⟨support, native⟩, continues⟩
  cases native
  cases current with
  | bootstrap => simp [originalInstruction] at decoded
  | running state past =>
      dsimp only [originalInstruction] at decoded
      split at decoded
      · cases decoded
      · rename_i fixed
        cases rowEq : item.1 with
        | inherited => simp only [rowEq] at decoded; cases decoded
        | obstruction => simp only [rowEq] at decoded; cases decoded
        | instruction index =>
            have same : instruction input state (staticIndex input fixed index) = raw := by
              simpa only [rowEq, Option.some.injEq] using decoded
            cases same
            simpa only [Root.ProgrammeSource.rawCurrent, Root.ProgrammeSource.rawEvent,
              Root.ProgrammeSource.wordAt, fixed] using
              instruction_mem input state (staticIndex input fixed index)

/-- A generated word is read from the actual interpreter trace.  Its
requests remain attached to the inherited interpreter responsibility;
the trace position distinguishes requests without allocating a second ledger. -/
def traceItems (current : (Root.ProgrammeSource.V input).Current) :
    List (ExecutionItem Party Good Port Technology Instrument) :=
  input.law.rawItems (Root.ProgrammeSource.rawCurrent input current)
    (Root.ProgrammeSource.rawEvent input current)

def traceRow (current : (Root.ProgrammeSource.V input).Current) :
    OpenResponsibilityAt (Root.ProgrammeSource.N input)
      (Root.ProgrammeSource.supportAt input current) :=
  Root.ProgrammeSource.sourceEntry input current .inherited

omit [DecidableEq Port] in
theorem traceRow_is_original_interpreter (current : (Root.ProgrammeSource.V input).Current) :
    (traceRow input current).1 = Root.ProgrammeWorld.Row.inherited := by
  cases current <;> rfl

def traceInstruction? (current : (Root.ProgrammeSource.V input).Current) (index : Nat) :
    Option (ExecutionItem Party Good Port Technology Instrument) :=
  (traceItems input current)[index]?

omit [DecidableEq Port] in
theorem traceInstruction_mem (current : (Root.ProgrammeSource.V input).Current)
    (index : Nat) (raw : ExecutionItem Party Good Port Technology Instrument)
    (decoded : traceInstruction? input current index = some raw) :
    raw ∈ input.law.rawItems (Root.ProgrammeSource.rawCurrent input current)
      (Root.ProgrammeSource.rawEvent input current) :=
  List.mem_of_getElem? decoded

#print axioms lifecycle_target_is_original
#print axioms originalInstruction_mem

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered
