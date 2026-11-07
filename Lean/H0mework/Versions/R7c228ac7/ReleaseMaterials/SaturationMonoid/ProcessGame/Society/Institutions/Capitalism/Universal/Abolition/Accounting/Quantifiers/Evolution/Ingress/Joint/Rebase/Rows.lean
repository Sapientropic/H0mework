import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Support
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Translation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def rowForward (support : (Background.original seed).native.N.Support)
    (state : Option (Productive.oldLaw seed).DebtState) :
    OpenResponsibilityAt (OldN seed) (support,state) →
      OpenResponsibilityAt (NewN seed grossClaim) (supportForward seed grossClaim (support,state)) := by
  rintro ⟨key,opened⟩
  cases key with
  | inl old => exact oldEntry (((Background.translation seed).oldOpenLedger support).forward ⟨old,opened⟩)
  | inr debt => cases state with
      | none => exact opened.elim
      | some old => exact ⟨.inr debt,opened⟩

def rowBackward (support : (Background.original seed).native.N.Support)
    (state : Option (Productive.oldLaw seed).DebtState) :
    OpenResponsibilityAt (NewN seed grossClaim) (supportForward seed grossClaim (support,state)) →
      OpenResponsibilityAt (OldN seed) (support,state) := by
  rintro ⟨key,opened⟩
  cases key with
  | inl old => exact oldEntry (((Background.translation seed).oldOpenLedger support).backward ⟨old,opened⟩)
  | inr debt => cases state with
      | none => exact opened.elim
      | some old => exact ⟨.inr debt,opened⟩

theorem row_backward_forward (support : (OldN seed).Support) (row : OpenResponsibilityAt (OldN seed) support) :
    rowBackward seed grossClaim support.1 support.2 (rowForward seed grossClaim support.1 support.2 row) = row := by
  rcases support with ⟨support,state⟩
  rcases row with ⟨key,opened⟩
  cases key with
  | inl old =>
      change oldEntry (((Background.translation seed).oldOpenLedger support).backward
        (((Background.translation seed).oldOpenLedger support).forward ⟨old,opened⟩)) = _
      rw [((Background.translation seed).oldOpenLedger support).backward_forward]
      rfl
  | inr debt => cases state with
      | none => exact opened.elim
      | some old => rfl

def rowRetract (support : (OldN seed).Support) :
    ConstructiveRetract (OpenResponsibilityAt (OldN seed) support)
      (OpenResponsibilityAt (NewN seed grossClaim) (supportForward seed grossClaim support)) :=
  ⟨rowForward seed grossClaim support.1 support.2,rowBackward seed grossClaim support.1 support.2,
    row_backward_forward seed grossClaim support⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
