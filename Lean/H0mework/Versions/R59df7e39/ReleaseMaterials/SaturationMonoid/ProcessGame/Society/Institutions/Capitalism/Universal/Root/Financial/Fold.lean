import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Instruction

/-! The financial lifecycle is folded from the literal registered source
inventory in visit order.  It never accepts a caller's replacement history
or a reconstructed aggregate balance as an admission source. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def consumeOrigins : List (InstructionOrigin input) → (process input).GeneratedState →
    (process input).GeneratedState
  | [], state => state
  | origin :: tail, state =>
      consumeOrigins tail ((consume input origin state).next input)

def consumeOrigins_run (origins : List (InstructionOrigin input)) (state : (process input).GeneratedState) :
    (process input).Run state.current (consumeOrigins input origins state).current := by
  induction origins generalizing state with
  | nil => exact .nil
  | cons origin tail ih =>
      exact ((consume input origin state).transition input).concatRuns (process input)
        (ih ((consume input origin state).next input))

theorem consumeOrigins_preserves_original_claims (origins : List (InstructionOrigin input))
    (state : (process input).GeneratedState) :
    state.current.slots.map (slotClaim input) <+:
      (consumeOrigins input origins state).current.slots.map (slotClaim input) := by
  induction origins generalizing state with
  | nil => exact List.prefix_rfl
  | cons origin tail ih =>
      exact ((consume input origin state).original_claims_retained input).trans
        (ih ((consume input origin state).next input))

def originAt (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (index : Fin (ProgrammeSource.registrationSize input + 2)) : InstructionOrigin input :=
  { visit := visit
    item := ProgrammeSource.sourceEntry input visit.current (ProgrammeSource.rowAt input index) }

def administrativeInventoryAt
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot) :
    List (InstructionOrigin input) := List.ofFn (originAt input visit)

def traceOriginAt (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (index : Fin (Source.ProgrammeFace.Registered.traceItems input visit.current).length) :
    InstructionOrigin input where
  visit := visit
  item := Source.ProgrammeFace.Registered.traceRow input visit.current
  traceIndex? := some index.val

def traceInventoryAt (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot) :
    List (InstructionOrigin input) := List.ofFn (traceOriginAt input visit)

omit [DecidableEq Port] in
theorem traceOriginAt_instruction
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (index : Fin (Source.ProgrammeFace.Registered.traceItems input visit.current).length) :
    (traceOriginAt input visit index).instruction? input =
      some ((Source.ProgrammeFace.Registered.traceItems input visit.current).get index) := by
  simp only [InstructionOrigin.instruction?, traceOriginAt,
    Source.ProgrammeFace.Registered.traceRow_is_original_interpreter,
    Source.ProgrammeFace.Registered.traceInstruction?, List.getElem?_eq_getElem index.isLt,
    List.get_eq_getElem]

omit [DecidableEq Port] in
theorem traceOriginAt_uses_original_row
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (index : Fin (Source.ProgrammeFace.Registered.traceItems input visit.current).length) :
    (traceOriginAt input visit index).row input =
      Source.ProgrammeFace.Registered.traceRow input visit.current := rfl

def inventoryAt (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot) :
    List (InstructionOrigin input) :=
  match input.emission? with
  | none => administrativeInventoryAt input visit
  | some _ => administrativeInventoryAt input visit ++ traceInventoryAt input visit

def oneVisit (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (state : (process input).GeneratedState) : (process input).GeneratedState :=
  consumeOrigins input (inventoryAt input visit) state

def accountAt : Nat → (process input).GeneratedState
  | 0 => .initial (process input)
  | index + 1 => oneVisit input (ProgrammeHistory.visitAt input index) (accountAt index)

theorem accountAt_successor (index : Nat) :
    accountAt input (index + 1) =
      consumeOrigins input (inventoryAt input (ProgrammeHistory.visitAt input index))
        (accountAt input index) := rfl

theorem whole_native_history_is_retained (index : Nat) :
    (accountAt input index).current.history <+: (accountAt input (index + 1)).current.history := by
  have sourceRun := consumeOrigins_run input
    (inventoryAt input (ProgrammeHistory.visitAt input index)) (accountAt input index)
  rw [accountAt_successor, sourceRun.history_eq]
  exact List.prefix_append _ _

theorem every_original_debt_is_retained (index : Nat) :
    (accountAt input index).current.slots.map (slotClaim input) <+:
      (accountAt input (index + 1)).current.slots.map (slotClaim input) :=
  consumeOrigins_preserves_original_claims input _ _

theorem every_actual_live_share_is_nonnegative (index : Nat)
    (slot : Fin (accountAt input index).current.slots.length)
    (obligation : AdmittedObligation (vocabulary input))
    (present : (accountAt input index).current.slots.get slot = .live obligation) :
    Coherent input obligation ∧ Nonnegative input obligation.residual :=
  live_sound input (accountAt input index) slot obligation present

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
