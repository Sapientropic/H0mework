import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot ProgrammeWorld

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def FreshBody (state : State input) : Prop :=
  state.phase = .entering ∨ state.position = 0 ∧ state.ahead = 0

instance (state : State input) : Decidable (FreshBody input state) :=
  inferInstanceAs (Decidable (state.phase = .entering ∨ state.position = 0 ∧ state.ahead = 0))

theorem physical_next_of_fresh (state : State input) (fresh : FreshBody input state) :
    (physicalVisit input (next input state)).current =
      ProgrammeSource.next input (physicalVisit input state).current := by
  unfold physicalVisit
  have advances : physicalVisitIndex input (next input state) = physicalVisitIndex input state + 1 := by
    rcases fresh with entry | fresh
    · exact entry_has_one_actual_body input state entry
    · exact physical_index_advances_once input state fresh.1 fresh.2
  rw [advances]
  rfl

theorem physical_next_of_bookkeeping (state : State input) (old : ¬ FreshBody input state) :
    physicalVisit input (next input state) = physicalVisit input state := by
  unfold physicalVisit
  apply congrArg (ProgrammeHistory.visitAt input)
  have accounting : state.phase = .accounting := by
    cases phase : state.phase with
    | entering => exact (old (Or.inl phase)).elim
    | accounting => rfl
  by_cases first : state.position = 0
  · have ahead : 0 < state.ahead := Nat.pos_of_ne_zero (fun zero => old (Or.inr ⟨first, zero⟩))
    exact pending_body_is_not_executed_again input state first ahead accounting
  · exact bookkeeping_keeps_physical_visit input state first accounting

theorem physical_index_monotone (state : State input) :
    physicalVisitIndex input state ≤ physicalVisitIndex input (next input state) := by
  by_cases fresh : FreshBody input state
  · have advances : physicalVisitIndex input (next input state) = physicalVisitIndex input state + 1 := by
      rcases fresh with entry | fresh
      · exact entry_has_one_actual_body input state entry
      · exact physical_index_advances_once input state fresh.1 fresh.2
    rw [advances]
    exact Nat.le_succ _
  · have same : physicalVisitIndex input (next input state) = physicalVisitIndex input state := by
      have accounting : state.phase = .accounting := by
        cases phase : state.phase with
        | entering => exact (fresh (Or.inl phase)).elim
        | accounting => rfl
      by_cases first : state.position = 0
      · exact pending_body_is_not_executed_again input state first
          (Nat.pos_of_ne_zero (fun zero => fresh (Or.inr ⟨first, zero⟩))) accounting
      · exact bookkeeping_keeps_physical_visit input state first accounting
    exact same.ge

def baseSupport (state : State input) : (ProgrammeSource.N input).Support :=
  ProgrammeSource.supportAt input (physicalVisit input state).current

def baseEntry (state : State input) (row : Row (ProgrammeSource.registrationSize input)) :
    OpenResponsibilityAt (ProgrammeSource.N input) (baseSupport input state) :=
  ProgrammeSource.sourceEntry input (physicalVisit input state).current row

omit [DecidableEq Port] in
theorem sourceEntry_self (current : (ProgrammeSource.V input).Current)
    (entry : OpenResponsibilityAt (ProgrammeSource.N input) (ProgrammeSource.supportAt input current)) :
    ProgrammeSource.sourceEntry input current entry.1 = entry := by
  rcases entry with ⟨row, opened⟩
  cases current with
  | bootstrap => cases row <;> cases opened <;> rfl
  | running _ _ => cases opened; rfl

def baseRowEvolution (state : State input) (row : Row (ProgrammeSource.registrationSize input)) :
    LedgerEntryEvolutionAt (ProgrammeSource.N input) (baseEntry input state row)
      (baseEntry input (next input state) row) := by
  by_cases fresh : FreshBody input state
  · dsimp only [baseEntry, baseSupport]
    rw [physical_next_of_fresh input state fresh]
    cases raw : (physicalVisit input state).current with
    | bootstrap => exact ProgrammeSource.transition input .bootstrap row
    | running current past => exact ProgrammeSource.transition input (.running current past) row
  · dsimp only [baseEntry, baseSupport]
    rw [physical_next_of_bookkeeping input state fresh]
    exact .carried rfl HEq.rfl

def baseEvolution (state : State input) :
    LedgerWriteEvolutionAt (ProgrammeSource.N input)
      ⟨baseSupport input state⟩ ⟨baseSupport input (next input state)⟩ where
  destination := by
    intro entry
    refine ⟨baseEntry input (next input state) entry.1, ?_⟩
    have evolution := baseRowEvolution input state entry.1
    have same : baseEntry input state entry.1 = entry :=
      sourceEntry_self input (physicalVisit input state).current entry
    rw [same] at evolution
    exact evolution
  origin := by
    intro entry
    refine ⟨baseEntry input state entry.1, ?_⟩
    have evolution := baseRowEvolution input state entry.1
    have same : baseEntry input (next input state) entry.1 = entry :=
      sourceEntry_self input (physicalVisit input (next input state)).current entry
    rw [same] at evolution
    exact evolution

def baseOwner (state : State input) : OpenResponsibilityAt (ProgrammeSource.N input) (baseSupport input state) :=
  baseEntry input state .inherited

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor
