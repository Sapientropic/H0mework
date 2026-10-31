import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLiving
import H0mework.Versions.R2.Foundation.Runtime.Activation

/-! The finite observations below recurse through the original root's
generated successor.  Neither a ledger nor a future-state table is added. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProgrammeWorld ProgrammeSource ProgrammeLiving

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Input Party Good Port Technology Instrument)

def visitAt : Nat → RootVisit (livingRoot input).toAuthoritativeRoot.toRoot
  | 0 => (livingRoot input).toAuthoritativeRoot.toRoot.initialVisit
  | index + 1 => (visitAt index).next rfl

def temporalVisit (index : Nat) : SourceNativeTemporalVisitAt
    (livingRoot input).toAuthoritativeRoot.toLedgerRoot := .finite (visitAt input index)

theorem first_instruction_visit :
    (visitAt input 1).current = next input .bootstrap := rfl

theorem past_length (index : Nat) :
    (pastAt (visitAt input index).current).length = index := by
  induction index with
  | zero => rfl
  | succ index ih =>
      change (pastAt (next input (visitAt input index).current)).length = _
      rw [past_next, List.length_append, List.length_singleton, ih]

theorem first_instruction_occurrence_retained (index : Nat) :
    rawCurrent input (visitAt input 1).current ∈
      pastAt (visitAt input (index + 2)).current := by
  induction index with
  | zero => exact List.mem_cons_of_mem _ List.mem_cons_self
  | succ index ih =>
      change _ ∈ pastAt (next input (visitAt input (index + 2)).current)
      rw [past_next]
      exact List.mem_append_left _ ih

theorem visit_round (index : Nat) :
    (rawCurrent input (visitAt input index).current).round = input.initial.round + index := by
  induction index with
  | zero => rfl
  | succ index ih =>
      change (rawCurrent input (next input (visitAt input index).current)).round = _
      rw [actual_raw_next]
      change (rawCurrent input (visitAt input index).current).round + 1 = _
      rw [ih]
      rfl

theorem visit_current_injective : Function.Injective (fun index => (visitAt input index).current) := by
  intro first second same
  have rounds := congrArg (fun current => (rawCurrent input current).round) same
  rw [visit_round, visit_round] at rounds
  exact Nat.add_left_cancel rounds

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt (N input) :=
  ⟨V input, livingRoot input, temporalVisit input index⟩

def process : SourceNativeLivingRootProcess (N input) where
  State := Nat
  stateAt := stateAt input
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (N input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (visitAt input first).current = (visitAt input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact visit_current_injective input currents
  initial := 0
  successorAt := fun index => ⟨index + 1, rfl, HEq.rfl⟩

def facade : SourceNativeLivingRuntimeFacade (N input) where
  process := process input
  FaceAt := fun _ => Projection
  componentAt := fun _ _ => projectionLaw input
  installationAt := fun _ _ => SourceNativeProjectionLaw.InstallationAt.refl (projectionLaw input)
  projectionAt := fun _ projection => projection

def activated (index : Nat) : LivingRuntimeState (process input) :=
  (facade input).seed.advance index

theorem activated_state (index : Nat) : (activated input index).state = index := by
  induction index with
  | zero => rfl
  | succ index ih => exact congrArg Nat.succ ih

theorem execution_face_shares_whole_ledger_and_next (index : Nat) :
    (process input).toAnswerNextCausalWorld.emitted
        (ULift.up (activated input index).state) =
      ULift.up (activated input index).tick.generated ∧
    (activated input index).tick.generated.occurrence =
      (activated input index).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated input index).current.visit.current ∧
    HEq (activated input index).tick.generated.wholeLedgerWriteBack
      ((activated input index).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated input index).current.visit.current) ∧
    HEq ((facade input).readoutAt (activated input index) .execution)
      ((activated input index).tick.generated.projectionOutcome .execution) ∧
    (activated input index).tick.nextCurrent =
      (process input).stateAt ((process input).successor (activated input index).state) :=
  (facade input).readoutAt_factorizes (activated input index) .execution

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory
