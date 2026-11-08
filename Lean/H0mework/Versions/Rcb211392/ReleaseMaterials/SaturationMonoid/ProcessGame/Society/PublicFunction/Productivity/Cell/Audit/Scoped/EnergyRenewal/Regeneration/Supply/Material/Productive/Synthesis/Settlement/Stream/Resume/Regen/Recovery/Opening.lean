import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def nativeOwed (account : Finance.Account) : ℚ :=
  Financial.Family.ledgerClaims Finance.sources account.current .delivery supplier receiver

def NativeDenomination (scope : Scope) (account : Finance.Account)
    (position : Fin account.current.slots.length) : Prop :=
  let claim := Financial.Family.slotClaim Finance.sources (account.current.slots.get position)
  (law scope).settlementUnit claim.2.instrument = (Finance.sources claim.1).law.settlementUnit claim.2.instrument ∧
    (law scope).settlementRate claim.2.instrument = (Finance.sources claim.1).law.settlementRate claim.2.instrument

instance (scope : Scope) (account : Finance.Account) (position : Fin account.current.slots.length) :
    Decidable (NativeDenomination scope account position) := by
  unfold NativeDenomination
  infer_instance

structure OpeningReady (scope : Scope) (before : Current) (account : Finance.Account) : Prop where
  balance : nativeOwed account = owed before
  denomination : ∀ position, NativeDenomination scope account position

inductive OpeningObstruction (scope : Scope) (before : Current) (account : Finance.Account)
  | originalBalance (different : nativeOwed account ≠ owed before)
  | originalDenomination (position : Fin account.current.slots.length)
      (conflict : ¬ NativeDenomination scope account position)

def denominationObstruction? (scope : Scope) (account : Finance.Account) :
    Option { position // ¬ NativeDenomination scope account position } :=
  (List.finRange account.current.slots.length).findSome? fun position =>
    if conflict : ¬ NativeDenomination scope account position then some ⟨position, conflict⟩ else none

theorem no_denomination_obstruction (scope : Scope) (account : Finance.Account)
    (clear : denominationObstruction? scope account = none) :
    ∀ position, NativeDenomination scope account position := by
  unfold denominationObstruction? at clear
  rw [List.findSome?_eq_none_iff] at clear
  intro position
  by_contra denied
  have check := clear position (List.mem_finRange _)
  simp [dif_pos denied] at check

def inspectOpening (scope : Scope) (before : Current) (account : Finance.Account) :
    PLift (OpeningReady scope before account) ⊕ OpeningObstruction scope before account :=
  if balance : nativeOwed account = owed before then
    match checked : denominationObstruction? scope account with
    | some conflict => .inr (.originalDenomination conflict.val conflict.property)
    | none => .inl ⟨balance, no_denomination_obstruction scope account checked⟩
  else .inr (.originalBalance balance)

theorem OpeningObstruction.excludes {scope : Scope} {before : Current} {account : Finance.Account}
    (refused : OpeningObstruction scope before account) : ¬ OpeningReady scope before account := by
  intro ready
  cases refused with
  | originalBalance different => exact different ready.balance
  | originalDenomination position conflict => exact conflict (ready.denomination position)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery
