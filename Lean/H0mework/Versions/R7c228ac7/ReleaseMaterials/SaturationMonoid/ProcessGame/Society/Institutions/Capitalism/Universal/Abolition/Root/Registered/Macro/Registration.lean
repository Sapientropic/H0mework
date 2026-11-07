import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

/-- The only registration factory reads the actual source instruction result.
Its rank pays admission; the original principal remains a live obligation. -/
structure Registration (item : Epoch.Finance.ActualItem input depth count)
    (before : (Epoch.Finance.process input depth count).GeneratedState) where
  private mk ::
  claim : Epoch.Finance.NewClaim input depth count
  exactOrigin : claim.origin = item
  selected : Epoch.Finance.consume input depth count item before = .issued claim exactOrigin

def registration? (item : Epoch.Finance.ActualItem input depth count)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    Option (Registration input depth count item before) :=
  match selected : Epoch.Finance.consume input depth count item before with
  | .issued claim original => some ⟨claim, original, selected⟩
  | .movement _ _ | .retained | .refused _ => none

namespace Registration

variable {item : Epoch.Finance.ActualItem input depth count}
  {before : (Epoch.Finance.process input depth count).GeneratedState}
  (registered : Registration input depth count item before)

def law := Epoch.Finance.Activation.law input depth count before (.inr registered.claim)

def firstStep := Epoch.Finance.Activation.firstStep input depth count before (.inr registered.claim)

def admitted := Epoch.Finance.Activation.admitted input depth count before (.inr registered.claim)

theorem first_step_is_the_same_source_account :
    Epoch.Finance.Activation.account input depth count before (.inr registered.claim)
        (registered.firstStep input depth count).target =
      (Epoch.Finance.consume input depth count item before).next input depth count := by
  rw [registered.selected]
  rfl

theorem original_principal_remains_live :
    (registered.admitted input depth count).current.slots[before.current.slots.length]? =
      some (.live (Epoch.Finance.admission input depth count (.inr registered.claim)).toObligation) :=
  Epoch.Finance.Activation.first_slot_is_the_actual_original_loan input depth count before (.inr registered.claim)

theorem registration_does_not_claim_financial_settlement :
    ¬ Nonempty ((registered.law input depth count).SettlementAt
      (registered.firstStep input depth count).target) :=
  Epoch.Finance.Activation.registration_is_not_financial_settlement input depth count before (.inr registered.claim)

def residualBearer :=
  Epoch.Finance.Activation.registered_obstruction input depth count before (.inr registered.claim)

end Registration

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Registration.first_step_is_the_same_source_account
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Registration.original_principal_remains_live
