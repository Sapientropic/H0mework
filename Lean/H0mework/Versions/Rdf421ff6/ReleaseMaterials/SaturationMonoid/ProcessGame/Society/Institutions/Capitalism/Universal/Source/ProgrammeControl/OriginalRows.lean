import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Word
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.RegisteredProgramme

/-! Every control or authorization obstruction returns the instruction's
original whole-ledger row.  The arithmetic index is read from the original
execution, not chosen as a new responsibility address.  The administrative
slot decoder below requires fixed emissions; dynamic words use the same
trace ordinal through AssetAuthority/Root/TraceOrigin. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl

open Program ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

omit [DecidableEq Port] in
theorem execution_get_index (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) (start : Nat)
    (word : RawEvent Party Good Port Technology Instrument)
    (index : Fin (law.execute current start word).items.length) :
    ((law.execute current start word).items.get index).index = start + index.val := by
  induction word generalizing current start with
  | nil => exact Fin.elim0 index
  | cons request tail ih =>
      cases index using Fin.cases with
      | zero => simp [RawLaw.execute]
      | succ index =>
          have later := ih (law.step current request) (start + 1) index
          change ((law.execute (law.step current request) (start + 1) tail).items.get index).index = _
          rw [later]
          change start + 1 + index.val = start + (index.val + 1)
          omega

variable (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev ItemAt {current : (Root.ProgrammeSource.V input).Current}
    (_event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current) :=
  OriginalItem input.law (Root.ProgrammeSource.rawCurrent input current)
    (Root.ProgrammeSource.rawEvent input current)

omit [DecidableEq Port] in
theorem original_index_bound {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : ItemAt input event) :
    item.val.index < (Root.ProgrammeSource.rawEvent input current).length := by
  obtain ⟨index, same⟩ := List.mem_iff_get.mp item.property
  have position := execution_get_index input.law (Root.ProgrammeSource.rawCurrent input current)
    0 (Root.ProgrammeSource.rawEvent input current) index
  change ((input.law.rawItems _ _).get index).index = _ at position
  rw [same, Nat.zero_add] at position
  rw [position]
  simpa only [RawLaw.rawItems, RawLaw.inventory_length] using index.isLt

omit [DecidableEq Port] in
theorem original_index_get {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : ItemAt input event) :
    (input.law.rawItems (Root.ProgrammeSource.rawCurrent input current)
      (Root.ProgrammeSource.rawEvent input current)).get
      ⟨item.val.index, by simpa only [RawLaw.rawItems, RawLaw.inventory_length]
        using original_index_bound input event item⟩ = item.val := by
  obtain ⟨index, same⟩ := List.mem_iff_get.mp item.property
  have position := execution_get_index input.law (Root.ProgrammeSource.rawCurrent input current)
    0 (Root.ProgrammeSource.rawEvent input current) index
  change ((input.law.rawItems _ _).get index).index = _ at position
  rw [same, Nat.zero_add] at position
  have bound : item.val.index < (input.law.rawItems (Root.ProgrammeSource.rawCurrent input current)
      (Root.ProgrammeSource.rawEvent input current)).length := by
    simpa only [RawLaw.rawItems, RawLaw.inventory_length] using original_index_bound input event item
  have indices : (⟨item.val.index, bound⟩ : Fin
      (input.law.rawItems (Root.ProgrammeSource.rawCurrent input current)
        (Root.ProgrammeSource.rawEvent input current)).length) = index := Fin.ext position
  rw [indices]
  exact same

def originalInstructionItem (fixed : input.emission? = none)
    {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : ItemAt input event) : OriginalInventoryItem event := by
  rcases event with ⟨⟨support, native⟩, continues⟩
  cases native
  cases current with
  | bootstrap => exact False.elim (List.not_mem_nil item.property)
  | running raw past =>
      exact ⟨.instruction ⟨item.val.index, by
        have bound := original_index_bound input _ item
        simpa only [Root.ProgrammeSource.rawEvent, Root.ProgrammeSource.wordAt,
          Root.ProgrammeSource.registrationSize, fixed] using bound⟩, ()⟩

omit [DecidableEq Port] in
theorem originalInstructionItem_decodes (fixed : input.emission? = none)
    {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : ItemAt input event) :
    ProgrammeFace.Registered.originalInstruction input event
      (originalInstructionItem input fixed event item) = some item.val := by
  rcases input with ⟨law, initial, instructions, emission, localAttempts⟩
  cases emission with
  | some emit => cases fixed
  | none =>
      rcases event with ⟨⟨support, native⟩, continues⟩
      cases native
      cases current with
      | bootstrap => exact False.elim (List.not_mem_nil item.property)
      | running raw past =>
          change some ((law.rawItems raw instructions).get _) = some item.val
          exact congrArg some (original_index_get _ _ item)

def originalInstructionRow (fixed : input.emission? = none)
    {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : ItemAt input event) := originalRow event (originalInstructionItem input fixed event item)

def originalInstructionDisposition (fixed : input.emission? = none)
    {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : ItemAt input event) :=
  ((Root.ProgrammeSource.ledgerSource input).ledgerCompiler.compile event.val).entryDisposition
    (originalInstructionRow input fixed event item)

omit [DecidableEq Port] in
theorem original_row_returns_exact_item (fixed : input.emission? = none)
    {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)
    (item : ItemAt input event) :
    ((Root.ProgrammeSource.source input).law.affectedInventoryPresentation event.val.2).backward
      (originalInstructionRow input fixed event item) = originalInstructionItem input fixed event item :=
  originalRow_recovers_item event (originalInstructionItem input fixed event item)

#print axioms originalInstructionItem_decodes
#print axioms original_row_returns_exact_item

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl
