import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Translation

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

theorem no_row_is_created_or_deleted_in_the_initial_representation
    (support : (OldN seed).Support)
    (row : OpenResponsibilityAt (NewN seed grossClaim) ((translation seed grossClaim).support.forward support)) :
    ((translation seed grossClaim).oldOpenLedger support).forward
      (((translation seed grossClaim).oldOpenLedger support).backward row) = row := by
  rcases support with ⟨support,state⟩
  rcases row with ⟨key,opened⟩
  cases key with
  | inl old =>
      change oldEntry (((Background.translation seed).oldOpenLedger support).forward
        (((Background.translation seed).oldOpenLedger support).backward ⟨old,opened⟩)) = _
      have same : ((Background.translation seed).oldOpenLedger support).forward
          (((Background.translation seed).oldOpenLedger support).backward ⟨old,opened⟩) = ⟨old,opened⟩ :=
        Abolition.Root.Registered.Macro.Ingress.translated_ledger_has_no_fresh_rows
          seed.input seed.depth seed.count seed.depth seed.count support ⟨old,opened⟩
      exact congrArg (fun entry => oldEntry (law := Productive.law seed grossClaim)
        (state? := state.map Productive.State.legacy) entry) same
  | inr debt => cases state with
      | none => exact opened.elim
      | some old => rfl

theorem each_original_row_keeps_its_actual_translated_key
    (support : (OldN seed).Support) (row : OpenResponsibilityAt (OldN seed) support) :
    (translation seed grossClaim).responsibility.forward row.1 =
      (((translation seed grossClaim).oldOpenLedger support).forward row).1 := by
  rcases support with ⟨support,state⟩
  rcases row with ⟨key,opened⟩
  cases key with
  | inl old =>
      have same := Abolition.Root.Registered.Macro.Ingress.translated_responsibility_is_the_original_row
        seed.input seed.depth seed.count seed.depth seed.count support ⟨old,opened⟩
      exact congrArg (fun key => (Sum.inl key : (NewN seed grossClaim).Responsibility)) same
  | inr debt => cases state with
      | none => exact opened.elim
      | some old => rfl

theorem the_original_productive_identity_is_not_readmitted
    (support : (Background.original seed).native.N.Support) (state : (Productive.oldLaw seed).DebtState) :
    (((translation seed grossClaim).oldOpenLedger (support,some state)).forward
      (debtEntry (N := (Background.original seed).native.N) (law := Productive.oldLaw seed) support state)).1 =
      Sum.inr (Productive.oldLaw seed).debtId := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
