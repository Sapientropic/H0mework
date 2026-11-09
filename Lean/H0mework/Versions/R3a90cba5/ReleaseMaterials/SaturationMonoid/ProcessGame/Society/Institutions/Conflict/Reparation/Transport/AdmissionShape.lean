import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Shape

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Shape

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Structure (extended_subsingleton)

variable {law : DebtActivationLaw} {base joint : WorldRelationNetwork}
  (shape : Shape law base joint) (finance : DebtActivationLaw)

private theorem extendedRows_read (support : (ExtendedNetwork base finance).Support)
    (stage : law.DebtState) (entry : OpenResponsibilityAt (ExtendedNetwork base finance) support) :
    let lifted := shape.extendedRows finance support stage (.inl entry)
    lifted.1 = Sum.map shape.key id entry.1 ∧
      lifted.claim = Sum.map shape.claim id entry.claim ∧ lifted.progressBudget = entry.progressBudget := by
  rcases support with ⟨baseSupport, active⟩
  rcases entry with ⟨key, witness⟩
  cases key with
  | inl old =>
    let entry : OpenResponsibilityAt base baseSupport := ⟨old, witness⟩
    change
      (shape.extendedRows finance (baseSupport, active) stage (.inl (oldEntry entry))).1 = .inl (shape.key old) ∧
      (shape.extendedRows finance (baseSupport, active) stage (.inl (oldEntry entry))).claim =
        .inl (shape.claim entry.claim) ∧
      (shape.extendedRows finance (baseSupport, active) stage (.inl (oldEntry entry))).progressBudget =
        entry.progressBudget
    rw [shape.extendedRows_old]
    exact ⟨congrArg Sum.inl (shape.old_key _ _ entry),
      congrArg Sum.inl (shape.old_claim _ _ entry), shape.old_budget _ _ entry⟩
  | inr new =>
    cases active with
    | none => exact nomatch witness
    | some active =>
      rcases witness with ⟨⟨same⟩⟩
      subst new
      exact ⟨rfl, rfl, rfl⟩

/-- Retain the existing insertion below an actual new finance coordinate.
The additional support coordinate is precisely the original finance phase. -/
def under : Shape law (ExtendedNetwork base finance) (ExtendedNetwork joint finance) where
  support := fun s r => (shape.support s.1 r, s.2)
  rows := shape.extendedRows finance
  key := Sum.map shape.key id
  claim := Sum.map shape.claim id
  repairKey := .inl shape.repairKey
  repairClaim := .inl shape.repairClaim
  old_key := fun s r entry => (extendedRows_read shape finance s r entry).1
  old_claim := fun s r entry => (extendedRows_read shape finance s r entry).2.1
  old_budget := fun s r entry => (extendedRows_read shape finance s r entry).2.2
  repair_key := by
    rintro ⟨s, state⟩ r
    rw [shape.extendedRows_repair]
    exact congrArg Sum.inl (shape.repair_key s r)
  repair_claim := by
    rintro ⟨s, state⟩ r
    rw [shape.extendedRows_repair]
    exact congrArg Sum.inl (shape.repair_claim s r)
  repair_budget := by
    rintro ⟨s, state⟩ r
    rw [shape.extendedRows_repair]
    exact shape.repair_budget s r
  anchor := shape.anchor
  incidence := shape.incidence
  lineage := shape.lineage
  anchor_eq := fun s r => shape.anchor_eq s.1 r
  incidence_eq := fun s r => shape.incidence_eq s.1 r
  lineage_eq := fun s r => shape.lineage_eq s.1 r
  oldTransfer := fun s r receipt => match receipt with
    | .inl old => .inl (shape.oldTransfer s.1 r old)
    | .inr native => .inr native
  repairTransfer := fun s r receipt => .inl (shape.repairTransfer s.1 r receipt)
  openFibres := fun baseFibres => extended_subsingleton finance
    (shape.openFibres (fun s k => baseFibres (s, none) (.inl k)))

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Shape
