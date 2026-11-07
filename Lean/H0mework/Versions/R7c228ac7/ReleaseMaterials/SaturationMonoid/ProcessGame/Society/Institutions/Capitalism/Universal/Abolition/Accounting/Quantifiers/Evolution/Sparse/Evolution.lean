import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Gate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Code

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

private theorem cast_inverse_origin {N : WorldRelationNetwork} {source middle target : CompleteLiveLedgerAt N}
    (same : source = middle) (evolution : LedgerWriteEvolutionAt N middle target)
    (inverse : ∀ entry,(evolution.destination (evolution.origin entry).1).1 = entry) :
    let changed := Eq.mp (congrArg (fun ledger => LedgerWriteEvolutionAt N ledger target) same.symm) evolution
    ∀ entry,(changed.destination (changed.origin entry).1).1 = entry := by cases same; exact inverse

private theorem cast_inverse_destination {N : WorldRelationNetwork} {source middle target : CompleteLiveLedgerAt N}
    (same : source = middle) (evolution : LedgerWriteEvolutionAt N middle target)
    (inverse : ∀ entry,(evolution.origin (evolution.destination entry).1).1 = entry) :
    let changed := Eq.mp (congrArg (fun ledger => LedgerWriteEvolutionAt N ledger target) same.symm) evolution
    ∀ entry,(changed.origin (changed.destination entry).1).1 = entry := by cases same; exact inverse

private theorem cast_keys {N : WorldRelationNetwork} {source middle target : CompleteLiveLedgerAt N}
    (same : source = middle) (evolution : LedgerWriteEvolutionAt N middle target)
    (keys : Financial.Installation.KeepsKeys evolution) :
    Financial.Installation.KeepsKeys
      (Eq.mp (congrArg (fun ledger => LedgerWriteEvolutionAt N ledger target) same.symm) evolution) := by
  cases same
  exact keys

private theorem transport_keys {N : WorldRelationNetwork} {law : DebtActivationLaw}
    (support : N.Support) {source target : law.DebtState} (event : law.TransportAt source target) :
    Financial.Installation.KeepsKeys (transportLedgerEvolution support event) := by
  constructor <;> rintro ⟨responsibility,opened⟩ <;> cases responsibility with
  | inl old => rfl
  | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

local notation "N" => ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)

def updated := Responsibility.Family.State.advance claim (Current.state claim current) current.actualLaw word

def support : Bool → (N).Support
  | false => Current.support claim current
  | true => ((Current.support claim current).1,some (updated claim current word))

theorem sourceLedger_eq : (⟨Current.support claim current⟩ : CompleteLiveLedgerAt N) =
    activeLedger (Current.support claim current).1 (Current.state claim current) :=
  congrArg CompleteLiveLedgerAt.mk (Current.support_eq claim current)

def actualEvolution : LedgerWriteEvolutionAt N ⟨support claim current word false⟩ ⟨support claim current word true⟩ :=
  Eq.mp (congrArg (fun ledger => LedgerWriteEvolutionAt N ledger ⟨support claim current word true⟩)
    (sourceLedger_eq claim current).symm)
    (transportLedgerEvolution (Current.support claim current).1
      (Responsibility.Family.CarryAt.actual (Current.state claim current) current.actualLaw word))

theorem actual_keeps_every_original_key : Financial.Installation.KeepsKeys (actualEvolution claim current word) :=
  cast_keys (sourceLedger_eq claim current) _ (transport_keys _ _)

def rowEvolution : (phase : Bool) → LedgerWriteEvolutionAt N ⟨support claim current word phase⟩ ⟨support claim current word true⟩
  | false => actualEvolution claim current word
  | true => LedgerWriteEvolutionAt.identity _

theorem actual_inverse_origin : ∀ entry,
    ((actualEvolution claim current word).destination ((actualEvolution claim current word).origin entry).1).1 = entry :=
  cast_inverse_origin (sourceLedger_eq claim current) _ (transportLedgerEvolution_destination_origin _ _)

theorem actual_inverse_destination : ∀ entry,
    ((actualEvolution claim current word).origin ((actualEvolution claim current word).destination entry).1).1 = entry :=
  cast_inverse_destination (sourceLedger_eq claim current) _ (transportLedgerEvolution_origin_destination _ _)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse
