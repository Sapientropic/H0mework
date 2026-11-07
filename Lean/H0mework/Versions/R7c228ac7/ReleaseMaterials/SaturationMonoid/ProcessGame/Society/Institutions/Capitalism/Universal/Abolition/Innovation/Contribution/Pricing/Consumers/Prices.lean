import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers

def selectedPayment (loss : ℚ) : Option (ℚ × ℚ × ℚ) :=
  match schedule with
  | .ready source => match source.payment (nature loss) () with
    | some payment => some (payment.1,payment.2.next.stock true (),payment.2.next.stock false ())
    | none => none
  | _ => none

def classified (proposed : ℚ) : Option Nat :=
  match schedule with
  | .ready source => match source.table sampleSignal with
    | .priced plan => match Source.classifyAmount source sampleSignal plan proposed with
      | .compensation _ => some 0
      | .surplus _ _ => some 1
      | .providerShortfall _ => some 2
      | .payerShortfall _ => some 3
    | .obstructed _ => none
  | _ => none

def allLivingAndMaintenanceChecked (loss : ℚ) : Bool :=
  match schedule with
  | .ready source => (Material.checkPeriod input initial [false,true]
      (source.requests (nature loss) ())).isAccepted input initial [false,true] _
  | _ => false

def oldClaims (loss : ℚ) : Option (ℚ × ℚ) :=
  match schedule with
  | .ready source => match source.payment (nature loss) () with
    | some payment => some (payment.2.next.claims () false true,payment.2.next.claims () true false)
    | none => none
  | _ => none

theorem the_generated_price_is_really_paid_in_both_risk_branches :
    selectedPayment 2 = some (4,101,103) ∧ selectedPayment 4 = some (4,99,103) := by
  decide +kernel

theorem every_original_member_is_paid_and_original_claims_are_not_reset :
    allLivingAndMaintenanceChecked 2 = true ∧ allLivingAndMaintenanceChecked 4 = true ∧
      oldClaims 2 = some (0,0) ∧ oldClaims 4 = some (0,0) := by
  decide +kernel

theorem a_shortfall_extra_distribution_and_overcharge_have_different_source_dispositions :
    classified 3 = some 2 ∧ classified 4 = some 0 ∧ classified 7 = some 1 ∧ classified 100 = some 3 := by
  decide +kernel

theorem a_live_unquoted_event_cannot_receive_a_fabricated_risk_payment :
    (match schedule with
    | .ready source => (source.payment (nature 3) ()).isNone
    | _ => false) = true := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers
