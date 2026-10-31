import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.Step
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.Context

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase

open Source.Program PublicFunction
open Macro.Services

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (origin : Physical.Cursor Party Good Port Technology Instrument)
  (code : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

inductive Stop : Type
  | exhausted {current : Physical.Cursor Party Good Port Technology Instrument}
      (prior : PendingAt source depth count prefixLimit renewalLimit origin code current)
      (empty : prior.remaining = [])
  | blocked {current : Physical.Cursor Party Good Port Technology Instrument}
      (prior : PendingAt source depth count prefixLimit renewalLimit origin code current)
      (pair : Material.Migration.CodePair Party Good Port Technology Instrument)
      (remaining : List (Material.Migration.CodePair Party Good Port Technology Instrument))
      (head : prior.remaining = pair :: remaining)
      (obstruction : Review.Blockage source.seed.law code.request code.scope
        (state source depth count prefixLimit renewalLimit current).raw)
      (generated : Migration.Budget.evaluate source depth count prefixLimit renewalLimit origin code
        prior.paidCount (state source depth count prefixLimit renewalLimit current).raw pair = .blocked obstruction)

/-- A dependent calculation face over the original cursor. Only a finite
already-consumed input count is folded; this stores no future input table. -/
inductive FaceAt (current : Physical.Cursor Party Good Port Technology Instrument) : Type
  | pending (pending : PendingAt source depth count prefixLimit renewalLimit origin code current)
  | selected (selected : SelectedAt source depth count prefixLimit renewalLimit origin code current)
  | stopped (reason : Stop source depth count prefixLimit renewalLimit origin code)
  | frontSubmitted {before : Physical.Cursor Party Good Port Technology Instrument}
      (selected : SelectedAt source depth count prefixLimit renewalLimit origin code before)
      (actual : current = selected.frontTarget)

abbrev View := Σ current : Physical.Cursor Party Good Port Technology Instrument,
  FaceAt source depth count prefixLimit renewalLimit origin code current

def first : View source depth count prefixLimit renewalLimit origin code :=
  ⟨origin, .pending (initial source depth count prefixLimit renewalLimit origin code)⟩

def nextRaw (view : View source depth count prefixLimit renewalLimit origin code) :
    Option (Compile.RawInput Party Good Port Technology Instrument) :=
  match view.2 with
  | .pending pending => match pending.remaining with
    | [] => none
    | _ :: _ => some (.primitive code.request)
  | .selected selected => some (.migrate selected.pair)
  | .stopped _ | .frontSubmitted .. => none

def advance (view : View source depth count prefixLimit renewalLimit origin code) :
    View source depth count prefixLimit renewalLimit origin code :=
  match view.2 with
  | .pending pending =>
      match head : pending.remaining with
      | [] => ⟨view.1, .stopped (.exhausted pending head)⟩
      | pair :: tail =>
          match afterFee source depth count prefixLimit renewalLimit pending pair tail head with
          | .selected selected => ⟨Migration.Budget.feeTarget view.1 code, .selected selected⟩
          | .rejected _ _ _ after _ => ⟨Migration.Budget.feeTarget view.1 code, .pending after⟩
          | .blocked obstruction generated =>
              ⟨Migration.Budget.feeTarget view.1 code, .stopped (.blocked pending pair tail head obstruction generated)⟩
  | .selected selected => ⟨selected.frontTarget, .frontSubmitted selected rfl⟩
  | .stopped reason => ⟨view.1, .stopped reason⟩
  | .frontSubmitted selected actual => ⟨view.1, .frontSubmitted selected actual⟩

/-- Advancement is literally the old physical input fold. The check and
its retained rejection do not execute candidate instructions. -/
theorem advance_is_the_same_physical_input (view : View source depth count prefixLimit renewalLimit origin code) :
    (advance source depth count prefixLimit renewalLimit origin code view).1 =
      match nextRaw source depth count prefixLimit renewalLimit origin code view with
      | some raw => Physical.next (Physical.receive view.1 raw)
      | none => view.1 := by
  rcases view with ⟨current, face⟩
  cases face with
  | pending pending =>
      dsimp only [advance, nextRaw]
      split
      · simp_all
      · split <;> simp_all [Migration.Budget.feeTarget, Migration.Budget.feeInput]
  | selected selected => rfl
  | stopped reason => rfl
  | frontSubmitted selected actual => rfl

def atCount : Nat → View source depth count prefixLimit renewalLimit origin code
  | 0 => first source depth count prefixLimit renewalLimit origin code
  | n + 1 => advance source depth count prefixLimit renewalLimit origin code
      (atCount n)

def atCursor (current : Physical.Cursor Party Good Port Technology Instrument) :=
  atCount source depth count prefixLimit renewalLimit origin code
    (current.past.length - origin.past.length)

/-- This is the source provenance condition consumed by the enclosing
registered epoch. It compares histories, not balances or names. -/
def Aligned (current : Physical.Cursor Party Good Port Technology Instrument) : Prop :=
  current.past = (atCursor source depth count prefixLimit renewalLimit origin code current).1.past

theorem initial_is_aligned : Aligned source depth count prefixLimit renewalLimit origin code origin := by
  simp only [Aligned, atCursor, Nat.sub_self, atCount, first]

theorem aligned_reads_the_literal_current (current : Physical.Cursor Party Good Port Technology Instrument)
    (same : Aligned source depth count prefixLimit renewalLimit origin code current) :
    state source depth count prefixLimit renewalLimit
      (atCursor source depth count prefixLimit renewalLimit origin code current).1 =
      state source depth count prefixLimit renewalLimit current := by
  exact congrArg (Physical.stateAt source.input depth count prefixLimit renewalLimit) same.symm

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.advance_is_the_same_physical_input
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.aligned_reads_the_literal_current
