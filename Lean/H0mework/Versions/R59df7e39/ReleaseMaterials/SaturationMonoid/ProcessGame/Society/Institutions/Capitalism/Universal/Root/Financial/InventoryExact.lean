import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Fold
import Mathlib.Data.List.OfFn

/-! Financial interpretation visits the literal original instruction word
in order.  The two administrative rows decode to none; no instruction is
duplicated, permuted, reconstructed or dropped. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
private theorem instructions_ofFn (current : RawCurrent Party Good Technology Instrument)
    (fixed : input.emission? = none) :
    List.ofFn (fun index => Registered.instruction input current (Registered.staticIndex input fixed index)) =
      input.law.rawItems current input.instructions := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, RawLaw.rawItems, RawLaw.inventory_length,
      ProgrammeSource.registrationSize_fixed input fixed]
  · intro index leftBound rightBound
    simp only [List.getElem_ofFn, Registered.instruction, Registered.staticIndex, List.get_eq_getElem]

omit [DecidableEq Port] in
private theorem decoded_rows_exact (current : (ProgrammeSource.V input).Current)
    (fixed : input.emission? = none) :
    (List.ofFn (fun index : Fin (ProgrammeSource.registrationSize input + 2) =>
      Registered.originalInstruction input ⟨ProgrammeSource.emitted input current, rfl⟩
        (ProgrammeSource.sourceEntry input current (ProgrammeSource.rowAt input index)))).filterMap id =
      input.law.rawItems (ProgrammeSource.rawCurrent input current) (ProgrammeSource.rawEvent input current) := by
  cases current with
  | bootstrap =>
      simp [Registered.originalInstruction, ProgrammeSource.emitted, ProgrammeSource.rawEvent,
        RawLaw.rawItems, RawLaw.execute, List.ofFn_const]
  | running raw past =>
      simp only [List.ofFn_succ, ProgrammeSource.rowAt, Fin.cases_zero, Fin.cases_succ,
        Registered.originalInstruction_running_fixed input raw past _ fixed,
        List.filterMap_cons, id_eq, ProgrammeSource.rawCurrent, ProgrammeSource.rawEvent,
        ProgrammeSource.wordAt, fixed]
      change (List.ofFn (some ∘ (fun index =>
        Registered.instruction input raw (Registered.staticIndex input fixed index)))).filterMap id = _
      rw [← List.map_ofFn, List.filterMap_map]
      simp only [Function.comp_def, id_eq, List.filterMap_some]
      exact instructions_ofFn input raw fixed

omit [DecidableEq Port] in
theorem traceInventoryAt_instructions_exact
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot) :
    (traceInventoryAt input visit).filterMap (InstructionOrigin.instruction? input) =
      Registered.traceItems input visit.current := by
  have mapped := List.map_ofFn (f := traceOriginAt input visit)
    (g := InstructionOrigin.instruction? input)
  have filtered := congrArg (List.filterMap id) mapped
  rw [List.filterMap_map] at filtered
  change (traceInventoryAt input visit).filterMap (InstructionOrigin.instruction? input) = _ at filtered
  rw [filtered]
  simp only [Function.comp_def, traceOriginAt_instruction]
  change (List.ofFn (some ∘ (Registered.traceItems input visit.current).get)).filterMap id = _
  rw [← List.map_ofFn, List.filterMap_map]
  simp only [Function.comp_def, id_eq, List.filterMap_some, List.ofFn_get]

omit [DecidableEq Port] in
private theorem generated_administrative_none
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (emit : Source.Program.RawCurrent Party Good Technology Instrument →
      Source.Program.RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit) :
    (administrativeInventoryAt input visit).filterMap (InstructionOrigin.instruction? input) = [] := by
  have mapped := List.map_ofFn (f := originAt input visit) (g := InstructionOrigin.instruction? input)
  have filtered := congrArg (List.filterMap id) mapped
  rw [List.filterMap_map] at filtered
  change (administrativeInventoryAt input visit).filterMap (InstructionOrigin.instruction? input) = _ at filtered
  rw [filtered]
  have each : (fun index : Fin (ProgrammeSource.registrationSize input + 2) =>
      (originAt input visit index).instruction? input) = fun _ => none := by
    funext index
    exact Registered.originalInstruction_generated_none input
      ((originAt input visit index).event input) (originAt input visit index).item emit generated
  simp only [Function.comp_def] at each ⊢
  rw [each]
  simp

omit [DecidableEq Port] in
theorem inventoryAt_instructions_exact
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot) :
    (inventoryAt input visit).filterMap (InstructionOrigin.instruction? input) =
      input.law.rawItems (ProgrammeSource.rawCurrent input visit.current)
        (ProgrammeSource.rawEvent input visit.current) := by
  cases emission : input.emission? with
  | none =>
      have exactRows := decoded_rows_exact input visit.current emission
      have mapped := List.map_ofFn (f := originAt input visit) (g := InstructionOrigin.instruction? input)
      have filtered := congrArg (List.filterMap id) mapped
      rw [List.filterMap_map] at filtered
      change (administrativeInventoryAt input visit).filterMap (InstructionOrigin.instruction? input) = _ at filtered
      simpa only [inventoryAt, emission, InstructionOrigin.instruction?, originAt,
        InstructionOrigin.event] using filtered.trans exactRows
  | some emit =>
      simp only [inventoryAt, emission, List.filterMap_append,
        generated_administrative_none input visit emit emission, List.nil_append]
      exact traceInventoryAt_instructions_exact input visit

#print axioms inventoryAt_instructions_exact

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
