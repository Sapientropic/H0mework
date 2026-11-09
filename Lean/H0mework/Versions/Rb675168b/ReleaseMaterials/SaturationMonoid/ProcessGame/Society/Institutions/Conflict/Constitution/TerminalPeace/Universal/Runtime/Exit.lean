import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material (ActualAndIndependent OriginalNeedFloor)
open Reparation.Actual (StateAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin : RawCurrent Party Good Technology Instrument} {roster : List Party}

def Attempt.personal (attempt : Attempt input origin roster) (person : Party) :
    Attempt input origin [person] :=
  ⟨attempt.before, attempt.offers⟩

variable (prior : StateAt seed community cut)
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)
  (menus : Menus Party Good Port Technology Instrument)

def ReadyAt (visit : Nat) : Prop :=
  Succeeds prior input origin roster menus visit ∧
    ∀ person ∈ roster, ((eventAt prior input origin roster menus visit).personal person).Succeeds

/-- Both refusal alternatives are read from the same actual current.
A joint period can be available while an individual exit is blocked. -/
def FaultAt (visit : Nat) : Prop :=
  Refused prior input origin roster menus visit ∨
    ∃ person ∈ roster, ((eventAt prior input origin roster menus visit).personal person).Refused

theorem ready_or_exact_fault (visit : Nat) :
    ReadyAt prior input origin roster menus visit ∨ FaultAt prior input origin roster menus visit := by
  classical
  let current := eventAt prior input origin roster menus visit
  rcases current.pays_or_refuses with paid | failed
  · by_cases missing : ∃ person ∈ roster, (current.personal person).Refused
    · exact Or.inr (Or.inr missing)
    · exact Or.inl ⟨paid, fun person listed => ((current.personal person).pays_or_refuses).resolve_right
        (fun refused => missing ⟨person, listed, refused⟩)⟩
  · exact Or.inr (Or.inl failed)

omit [DecidableEq Port] in
private theorem Attempt.success_refutes_refusal (attempt : Attempt input origin roster)
    (paid : attempt.Succeeds) : ¬ attempt.Refused := by
  rintro ⟨failed, absent⟩
  obtain ⟨position, certificate, earlier, approved⟩ := paid
  rw [approved] at absent
  cases absent

theorem ready_refutes_a_fault (visit : Nat) (ready : ReadyAt prior input origin roster menus visit) :
    ¬ FaultAt prior input origin roster menus visit := by
  rintro (collective | ⟨person, listed, solo⟩)
  · exact Attempt.success_refutes_refusal input origin roster (eventAt prior input origin roster menus visit) ready.1 collective
  · exact Attempt.success_refutes_refusal input origin [person]
      ((eventAt prior input origin roster menus visit).personal person) (ready.2 person listed) solo

theorem a_ready_cut_has_a_source_generated_personal_exit
    (visit : Nat) (ready : ReadyAt prior input origin roster menus visit)
    (person : Party) (listed : person ∈ roster) :
    let attempt := eventAt prior input origin roster menus visit
    ∃ word ∈ attempt.offers,
      ActualAndIndependent input attempt.before.raw word ∧
        OriginalNeedFloor input origin attempt.before.raw [person] word ∧
        OriginalNeedFloor input attempt.before.raw attempt.before.raw [person] word := by
  obtain ⟨position, paid, _, _⟩ := ready.2 person listed
  exact ⟨_, List.getElem_mem position.isLt, paid.toActualAndIndependent, paid.originalFloor, paid.currentFloor⟩

theorem the_missing_personal_exit_names_the_original_bearer
    (visit : Nat) (failed : FaultAt prior input origin roster menus visit) :
    let attempt := eventAt prior input origin roster menus visit
    (∀ word ∈ attempt.offers, ¬ Supply.Period input origin attempt.before.raw roster word) ∨
      ∃ person ∈ roster, ∀ word ∈ attempt.offers, ¬ Supply.Period input origin attempt.before.raw [person] word := by
  rcases failed with collective | ⟨person, listed, solo⟩
  · exact Or.inl ((eventAt prior input origin roster menus visit).fails_iff.mp collective)
  · exact Or.inr ⟨person, listed, ((eventAt prior input origin roster menus visit).personal person).fails_iff.mp solo⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime
