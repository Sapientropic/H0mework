import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
private theorem every_resigned_request_is_without_external_consent
    (word : RawEvent Party Good Port Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (inside : request ∈ word.map (fun original => original.resign original.signer)) :
    request.consents = [] := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp inside
  rfl

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem every_source_selected_request_has_no_controller_consent
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : wordAt before raw = some word)
    (request : Request Party Good Port Technology Instrument) (inside : request ∈ word) :
    request.consents = [] := by
  cases raw with
  | advance =>
      cases phase : before.phase with
      | seeking =>
          simp only [wordAt, phase] at selected
          cases selected
      | renewal original =>
          simp only [wordAt, phase] at selected
          have same := Option.some.inj selected
          subst word
          exact every_resigned_request_is_without_external_consent original request inside
  | primitive original =>
      have same := Option.some.inj selected
      subst word
      have sameRequest := List.mem_singleton.mp inside
      subst request
      rfl
  | execute original =>
      have same := Option.some.inj selected
      subst word
      exact every_resigned_request_is_without_external_consent original request inside
  | migrate _ | code _ | review _ | stopReview => cases selected

theorem every_actual_public_instruction_has_no_controller_consent
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (inside : item ∈ (compile input before raw).execution.items) :
    item.request.consents = [] := by
  cases generated : compile input before raw with
  | accepted word selected checked =>
      rw [generated] at inside
      apply every_source_selected_request_has_no_controller_consent before raw word selected item.request
      rw [← RawLaw.inventory_requests_exact (interpreter input) before.raw 0 word]
      exact List.mem_map.mpr ⟨item, inside, rfl⟩
  | refused => rw [generated] at inside; cases inside
  | metadata _ => rw [generated] at inside; cases inside

#print axioms every_source_selected_request_has_no_controller_consent
#print axioms every_actual_public_instruction_has_no_controller_consent

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public
