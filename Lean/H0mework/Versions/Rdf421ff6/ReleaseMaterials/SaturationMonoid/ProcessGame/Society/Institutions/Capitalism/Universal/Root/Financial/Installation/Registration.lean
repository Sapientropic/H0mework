import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.NativeFrame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input)

structure Registration (origin : frame.V.Current) where
  private mk ::
  claim : IssuedClaim input
  selected : Cursor.action input (frame.cursor origin) = .issue claim

def registration? (origin : frame.V.Current) : Option (Registration input frame origin) :=
  match selected : Cursor.action input (frame.cursor origin) with
  | .issue claim => some ⟨claim, selected⟩
  | .movement _ _ | .retain => none

namespace Registration

variable {origin : frame.V.Current} (registered : Registration input frame origin)

def before (_registered : Registration input frame origin) : (process input).GeneratedState :=
  (frame.cursor origin).account

def admitted : (process input).GeneratedState := admit input (registered.before input frame) registered.claim

def law := Activation.law input (registered.before input frame) registered.claim

def firstStep := Activation.firstStep input (registered.before input frame) registered.claim

theorem actual_base_next_account :
    (frame.cursor (frame.V.nativeTarget (frame.program.emit origin).write)).account =
      registered.admitted input frame := by
  have actual := congrArg Cursor.State.account (frame.next_exact origin)
  change _ = (Cursor.action input (frame.cursor origin)).next input (frame.cursor origin).account at actual
  rw [registered.selected] at actual
  exact actual

theorem original_principal_survives_registration :
    total input (admission input registered.claim).residual = registered.claim.quantity :=
  initial_total input registered.claim

theorem no_financial_settlement_from_registration :
    ¬ Nonempty ((registered.law input frame).SettlementAt (registered.firstStep input frame).target) :=
  Activation.registration_is_not_financial_settlement input (registered.before input frame) registered.claim

def action (current : frame.V.Current) : Action input := Cursor.action input (frame.cursor current)

def native (current : frame.V.Current) :
    (process input).Run (frame.cursor current).account.current
      (frame.cursor (frame.V.nativeTarget (frame.program.emit current).write)).account.current :=
  (congrArg (fun cursor : Cursor.State input => cursor.account.current) (frame.next_exact current)).symm ▸
    (Cursor.native input (frame.cursor current))

theorem registered_state_eq {before : (process input).GeneratedState} {claim : IssuedClaim input}
    {left right : (process input).GeneratedState}
    (leftNative : Nonempty ((process input).Run (admit input before claim).current left.current))
    (rightNative : Nonempty ((process input).Run (admit input before claim).current right.current))
    (same : left = right) :
    Activation.State.registered (input := input) (before := before) (claim := claim) left leftNative =
      .registered right rightNative := by
  cases same
  rfl

end Registration

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
