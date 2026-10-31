import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.Obligation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

def carry {old : AdmittedObligation (Financial.vocabulary input)} {event : Financial.Event input} :
    ActiveCarryDisposition (Financial.vocabulary input) old event →
      ActiveCarryDisposition (vocabulary input depth count)
        (obligation input depth count old) (.legacy event)
  | .progressed residual receipt => .progressed residual
      ⟨receipt.down.1, congrArg Sum.inl receipt.down.2.1, receipt.down.2.2⟩
  | .progressedAndTransferred _ _ _ impossible | .maintained impossible |
      .deferred impossible | .narrowed _ impossible _ | .transferred _ impossible => impossible.elim

def finalReceipt {old : AdmittedObligation (Financial.vocabulary input)} {event : Financial.Event input} :
    FinalReceipt (Financial.vocabulary input) old event →
      FinalReceipt (vocabulary input depth count)
        (obligation input depth count old) (.legacy event)
  | .fulfilled receipt => .fulfilled
      ⟨receipt.down.1, congrArg Sum.inl receipt.down.2.1,
        congrArg Origin.original receipt.down.2.2.1, receipt.down.2.2.2⟩
  | .waived impossible | .invalidated impossible | .abandonedWithConsequence impossible |
      .impossibleResidueAccepted impossible => impossible.elim

def impossibleRelease {old : AdmittedObligation (Financial.vocabulary input)} {event : Financial.Event input} :
    BearerReleaseReceipt (Financial.vocabulary input) old event → PEmpty
  | .transferredAndAccepted _ impossible | .jurisdictionEndedWithResidue impossible _ |
      .consentRevoked impossible _ | .capacityReleasedWithResidue impossible _ => impossible

def archive (old : TerminalArchive (Financial.vocabulary input)) :
    TerminalArchive (vocabulary input depth count) where
  obligation := obligation input depth count old.obligation
  sourceEvent := .legacy old.sourceEvent
  receipt := finalReceipt input depth count old.receipt

def slot : ObligationSlot (Financial.vocabulary input) → ObligationSlot (vocabulary input depth count)
  | .live old => .live (obligation input depth count old)
  | .terminal old => .terminal (archive input depth count old)

def lifecycle : LifecycleEvent (Financial.vocabulary input) → LifecycleEvent (vocabulary input depth count)
  | .admitted index old => .admitted index (payload input depth count old)
  | .carried index old event receipt => .carried index (obligation input depth count old)
      (.legacy event) (carry input depth count receipt)
  | .terminal index old event receipt => .terminal index (obligation input depth count old)
      (.legacy event) (finalReceipt input depth count receipt)
  | .superseded _ _ _ receipt => receipt.incidence.elim
  | .bearerReleased _ _ _ receipt => (impossibleRelease input receipt).elim
  | .reopened _ _ receipt => receipt.incidence.elim

def state (old : ResponsibilityState (Financial.vocabulary input)) :
    ResponsibilityState (vocabulary input depth count) where
  slots := old.slots.map (slot input depth count)
  history := old.history.map (lifecycle input depth count)

theorem history_slots_keep_original_positions (event : LifecycleEvent (Financial.vocabulary input)) :
    (lifecycle input depth count event).slot = event.slot := by
  cases event with
  | admitted | carried | terminal => rfl
  | superseded _ _ _ receipt => exact receipt.incidence.elim
  | bearerReleased _ _ _ receipt => exact (impossibleRelease input receipt).elim
  | reopened _ _ receipt => exact receipt.incidence.elim

theorem old_slot_count_is_unchanged (old : ResponsibilityState (Financial.vocabulary input)) :
    (state input depth count old).slots.length = old.slots.length := by
  simp only [state, List.length_map]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy
