import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.SelectedPrimitive
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee

open Source.Program Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Evolving.Epoch

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Cursor" => ReviewCursor (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Code" => Admission.FeeCode (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

/-- The source already selected this fee in its installed review. Its raw
request is the original parser's independent payment, not a new proposal. -/
structure SelectedAt (source : C) where
  private mk ::
  cursor : Cursor
  original : source.control.review = some cursor
  fee : Code
  originalOperation : fee.request.operation = cursor.code.fee.operation
  signed : fee.request.consents = []
  selected : source.executionRaw = .primitive fee.request
  writeBack : source.afterControl.review = some { cursor with
    feePaid := source.physicalResult.isAccepted, halted := !source.physicalResult.isAccepted }

private def selectedFrom (source : C) (choice : type_of% source.choice)
    (observed : source.choice = choice) : Option (SelectedAt source) := by
  cases choice with
  | ordinary _ => exact none
  | reviewing cursor original review =>
    cases review
    case fee scope parsed =>
      let fee := (ReviewSource.Fees.originalCode scope).withoutConsents
      refine some ⟨cursor, original, fee, rfl, rfl, ?_, ?_⟩
      · unfold Current.executionRaw
        rw [observed]
        rfl
      · unfold Current.afterControl
        rw [observed]
        rfl
    all_goals exact none

def selected? (source : C) : Option (SelectedAt source) :=
  selectedFrom source source.choice rfl

private theorem reading_the_original_choice (source : C) (choice : type_of% source.choice)
    (observed : source.choice = choice) : selected? source = selectedFrom source choice observed := by
  subst choice
  rfl

theorem the_installed_fee_choice_generates_its_own_quantified_payment
    (source : C) (cursor : Cursor) (registered : source.control.review = some cursor)
    (scope : Abolition.Review.FeeScope cursor.code.fee)
    (parsed : ReviewSource.Fees.scope? cursor.code.fee = some scope)
    (observed : source.choice = .reviewing cursor registered (.fee scope parsed)) :
    ∃ chosen, selected? source = some chosen ∧ chosen.fee.scope.amount = scope.amount ∧
      chosen.fee.scope.payer = scope.payer ∧ chosen.fee.scope.good = scope.good := by
  rw [reading_the_original_choice source _ observed]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

def necessities (source : C) (payer : Party) (good : Good) : ℚ :=
  Exit.Redemption.essentials (Physical.Public.interpreter source.native.input)
    (Actual.origin source.native.input source.native.depth source.native.count) payer good

def ceiling (source : C) (payer : Party) (good : Good) : ℚ :=
  source.raw.stock payer good - necessities source payer good

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee
