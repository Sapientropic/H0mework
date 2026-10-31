import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Backing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source

open ResponsibilityLifecycle
open Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

theorem every_original_financial_admission_has_an_actual_commitment
    (payload : NativeAdmissionPayload (Financial.vocabulary input)) :
    Nonempty (Financial.Event.CommitmentAt input payload.sourceEvent payload.content) := by
  cases payload.origin with
  | producerDemand demand _ _ => cases demand.obstruction
  | explicitCommitment receipt => exact ⟨receipt⟩
  | standingMandate impossible => cases impossible
  | acceptedTask impossible => cases impossible
  | activeDependency impossible => cases impossible
  | protectedRisk impossible => cases impossible

/-- Closure of this actual native financial vocabulary. Compulsory public
responsibility belongs to its own generated action, not a forged loan. -/
theorem every_original_financial_admission_is_its_original_issued_claim
    (payload : NativeAdmissionPayload (Financial.vocabulary input)) :
    payload.sourceEvent = .birth payload.content := by
  obtain ⟨receipt⟩ := every_original_financial_admission_has_an_actual_commitment input payload
  cases source : payload.sourceEvent with
  | birth claim =>
      rw [source] at receipt
      exact congrArg Financial.Event.birth receipt.down
  | review claim review before remaining =>
      rw [source] at receipt
      cases receipt

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source
