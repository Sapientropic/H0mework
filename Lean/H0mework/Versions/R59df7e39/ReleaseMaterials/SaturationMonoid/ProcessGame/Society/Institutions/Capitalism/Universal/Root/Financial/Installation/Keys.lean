import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def KeepsKeys {N : WorldRelationNetwork} {before after : N.Support}
    (evolution : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩) : Prop :=
  (∀ entry, ((evolution.destination entry).1).1 = entry.1) ∧
  (∀ entry, ((evolution.origin entry).1).1 = entry.1)

theorem wholeTransport_keeps_keys {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {sourceSupport targetSupport : N.Support} {source target : law.DebtState}
    (base : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt N sourceSupport) (transport : law.TransportAt source target)
    (same : KeepsKeys base) : KeepsKeys (wholeTransport base owner transport) := by
  constructor
  · rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old => exact congrArg Sum.inl (same.1 ⟨old, opened⟩)
    | inr debt =>
        rcases opened with ⟨⟨sameId⟩⟩
        subst debt
        rfl
  · rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old => exact congrArg Sum.inl (same.2 ⟨old, opened⟩)
    | inr debt =>
        rcases opened with ⟨⟨sameId⟩⟩
        subst debt
        rfl

theorem transport_keeps_keys (base : WorldRelationNetwork) (sourceSupport targetSupport : base.Support)
    (baseEvolution : LedgerWriteEvolutionAt base ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt base sourceSupport) (same : KeepsKeys baseEvolution) :
    {current : ResponsibilityState (vocabulary input)} →
    (run : (process input).Run (.empty (vocabulary input)) current) →
    (before : (process input).GeneratedState) →
    (prior : Nonempty ((process input).Run current before.current)) →
    (action : Action input) →
    KeepsKeys (transport input base sourceSupport targetSupport baseEvolution owner run before prior action) := by
  intro current run
  induction run with
  | nil => intro before prior action; exact same
  | step priorRun edge ih =>
      intro before prior action
      cases edge with
      | admit claim =>
          exact wholeTransport_keeps_keys _ _ _
            (ih before (prependNative input (.admit claim) rfl prior) action)
      | cross slot obligation present boundary =>
          exact ih before (prependNative input (.cross slot obligation present boundary) rfl prior) action
      | reopen _ _ _ impossible => exact impossible.elim

theorem world_openAt_subsingleton :
    {current : ResponsibilityState (vocabulary input)} →
    (run : (process input).Run (.empty (vocabulary input)) current) →
    (state : (world input (ProgrammeSource.N input) run).Support) →
    (responsibility : (world input (ProgrammeSource.N input) run).Responsibility) →
    Subsingleton ((world input (ProgrammeSource.N input) run).OpenAt state responsibility) := by
  intro current run
  induction run with
  | nil =>
      intro state responsibility
      change Subsingleton (ProgrammeWorld.OpenAt state responsibility)
      cases state <;> cases responsibility <;> dsimp only [ProgrammeWorld.OpenAt] <;> infer_instance
  | step prior edge ih =>
      intro state responsibility
      cases edge with
      | admit claim =>
          rcases state with ⟨baseState, active⟩
          cases responsibility with
          | inl old => exact ih baseState old
          | inr debt =>
              cases active <;> dsimp only [world, ExtendedNetwork, extendedNetwork, DebtOpenAt] <;> infer_instance
      | cross _ _ _ _ => exact ih state responsibility
      | reopen _ _ _ impossible => exact impossible.elim

omit [DecidableEq Port] in
theorem visit_succ_running (index : Nat) :
    ∃ raw past, (ProgrammeHistory.visitAt input (index + 1)).current = .running raw past := by
  change ∃ raw past, ProgrammeSource.next input (ProgrammeHistory.visitAt input index).current = .running raw past
  cases (ProgrammeHistory.visitAt input index).current <;> exact ⟨_, _, rfl⟩

theorem physical_running (state : Cursor.State input) (positive : 0 < Cursor.physicalVisitIndex input state) :
    ∃ raw past, (Cursor.physicalVisit input state).current = .running raw past := by
  cases indexEq : Cursor.physicalVisitIndex input state with
  | zero => simp only [indexEq, Nat.lt_irrefl] at positive
  | succ index => simpa only [Cursor.physicalVisit, indexEq] using visit_succ_running input index

theorem baseEntry_key (state : Cursor.State input) (positive : 0 < Cursor.physicalVisitIndex input state)
    (row : ProgrammeWorld.Row (ProgrammeSource.registrationSize input)) : (Cursor.baseEntry input state row).1 = row := by
  rcases physical_running input state positive with ⟨raw, past, actual⟩
  exact congrArg (fun current => (ProgrammeSource.sourceEntry input current row).1) actual

theorem baseEvolution_keeps_keys (state : Cursor.State input) (positive : 0 < Cursor.physicalVisitIndex input state) :
    KeepsKeys (Cursor.baseEvolution input state) := by
  constructor
  · intro entry
    exact baseEntry_key input (Cursor.next input state)
      (positive.trans_le (Cursor.physical_index_monotone input state)) entry.1
  · intro entry
    exact baseEntry_key input state positive entry.1

theorem keys_imply_origin_injective {N : WorldRelationNetwork} {before after : N.Support}
    (evolution : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩) (same : KeepsKeys evolution)
    (fibres : ∀ support responsibility, Subsingleton (N.OpenAt support responsibility)) :
    Function.Injective (fun entry => (evolution.origin entry).1) := by
  intro left right equal
  have keys := congrArg Sigma.fst equal
  rw [same.2 left, same.2 right] at keys
  rcases left with ⟨left, openedLeft⟩
  rcases right with ⟨right, openedRight⟩
  dsimp at keys
  subst right
  exact Sigma.ext rfl (heq_of_eq ((fibres after left).elim _ _))

theorem keys_imply_destination_injective {N : WorldRelationNetwork} {before after : N.Support}
    (evolution : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩) (same : KeepsKeys evolution)
    (fibres : ∀ support responsibility, Subsingleton (N.OpenAt support responsibility)) :
    Function.Injective (fun entry => (evolution.destination entry).1) := by
  intro left right equal
  have keys := congrArg Sigma.fst equal
  rw [same.1 left, same.1 right] at keys
  rcases left with ⟨left, openedLeft⟩
  rcases right with ⟨right, openedRight⟩
  dsimp at keys
  subst right
  exact Sigma.ext rfl (heq_of_eq ((fibres before left).elim _ _))

namespace AccountSource

variable (start : Cursor.State input)

theorem wholeEvolution_keeps_keys (current : Current input start) : KeepsKeys (wholeEvolution input start current) :=
  transport_keeps_keys input (ProgrammeSource.N input) _ _ _ _
    (baseEvolution_keeps_keys input current.cursor current.positive) _ _ _ _

theorem whole_origin_injective (current : Current input start) :
    Function.Injective (fun entry => ((wholeEvolution input start current).origin entry).1) :=
  keys_imply_origin_injective _ (wholeEvolution_keeps_keys input start current)
    (world_openAt_subsingleton input start.account.generated)

theorem whole_destination_injective (current : Current input start) :
    Function.Injective (fun entry => ((wholeEvolution input start current).destination entry).1) :=
  keys_imply_destination_injective _ (wholeEvolution_keeps_keys input start current)
    (world_openAt_subsingleton input start.account.generated)

end AccountSource

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
