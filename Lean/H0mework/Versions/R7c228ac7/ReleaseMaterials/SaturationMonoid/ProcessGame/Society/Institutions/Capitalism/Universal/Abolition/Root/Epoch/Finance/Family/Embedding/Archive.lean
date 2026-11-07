import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding.Payload

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat) (index : Index)

local notation "OldV" => Finance.vocabulary (sources index) (depths index) (counts index)
local notation "NewV" => Family.vocabulary sources depths counts

def final {original : AdmittedObligation OldV}
    {source : Finance.Event (sources index) (depths index) (counts index)} :
    FinalReceipt OldV original source →
      FinalReceipt NewV (obligation sources depths counts index original) (event sources depths counts index source)
  | .fulfilled receipt => .fulfilled ⟨receipt.down.1, congrArg (Sigma.mk index) receipt.down.2.1,
      congrArg (Sigma.mk index) receipt.down.2.2.1, receipt.down.2.2.2⟩
  | .waived receipt | .invalidated receipt | .abandonedWithConsequence receipt | .impossibleResidueAccepted receipt => receipt.elim

def archive (original : TerminalArchive OldV) : TerminalArchive NewV :=
  ⟨obligation sources depths counts index original.obligation, event sources depths counts index original.sourceEvent,
    final sources depths counts index original.receipt⟩

def slot : ObligationSlot OldV → ObligationSlot NewV
  | .live original => .live (obligation sources depths counts index original)
  | .terminal original => .terminal (archive sources depths counts index original)

def carry {original : AdmittedObligation OldV}
    {source : Finance.Event (sources index) (depths index) (counts index)} :
    ActiveCarryDisposition OldV original source →
      ActiveCarryDisposition NewV (obligation sources depths counts index original) (event sources depths counts index source)
  | .progressed after receipt => .progressed after ⟨receipt.down.1,
      congrArg (Sigma.mk index) receipt.down.2.1, receipt.down.2.2.1, receipt.down.2.2.2⟩
  | .progressedAndTransferred _ _ _ impossible | .maintained impossible | .deferred impossible
  | .narrowed _ impossible _ | .transferred _ impossible => impossible.elim

def record : LifecycleEvent OldV → LifecycleEvent NewV
  | .admitted position original => .admitted position (payload sources depths counts index original)
  | .carried position original source receipt => .carried position
      (obligation sources depths counts index original) (event sources depths counts index source)
      (carry sources depths counts index receipt)
  | .terminal position original source receipt => .terminal position
      (obligation sources depths counts index original) (event sources depths counts index source)
      (final sources depths counts index receipt)
  | .superseded _ _ _ impossible => impossible.incidence.elim
  | .bearerReleased _ _ _ impossible => by cases impossible <;> exact PEmpty.elim (by assumption)
  | .reopened _ _ impossible => impossible.incidence.elim

def state (original : ResponsibilityState OldV) : ResponsibilityState NewV :=
  ⟨original.slots.map (slot sources depths counts index), original.history.map (record sources depths counts index)⟩

#print axioms archive
#print axioms state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding
