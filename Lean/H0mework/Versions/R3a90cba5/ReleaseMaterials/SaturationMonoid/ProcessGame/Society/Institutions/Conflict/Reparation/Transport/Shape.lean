import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Slots

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Structure (extended_subsingleton)

/-- One already installed responsibility inside the original finance stack.
Every other open row comes from the original account at this very support. -/
structure Shape (law : DebtActivationLaw) (base joint : WorldRelationNetwork) where
  support : base.Support → law.DebtState → joint.Support
  rows : ∀ s r, (OpenResponsibilityAt base s ⊕ Unit) ≃ OpenResponsibilityAt joint (support s r)
  key : base.Responsibility → joint.Responsibility
  claim : base.Claim → joint.Claim
  repairKey : joint.Responsibility
  repairClaim : joint.Claim
  old_key : ∀ s r entry, (rows s r (.inl entry)).1 = key entry.1
  old_claim : ∀ s r entry, (rows s r (.inl entry)).claim = claim entry.claim
  old_budget : ∀ s r entry, (rows s r (.inl entry)).progressBudget = entry.progressBudget
  repair_key : ∀ s r, (rows s r (.inr ())).1 = repairKey
  repair_claim : ∀ s r, (rows s r (.inr ())).claim = repairClaim
  repair_budget : ∀ s r, (rows s r (.inr ())).progressBudget = law.budget r
  anchor : base.Anchor → joint.Anchor
  incidence : base.Incidence → joint.Incidence
  lineage : base.Lineage → joint.Lineage
  anchor_eq : ∀ s r, joint.anchorAt (support s r) = anchor (base.anchorAt s)
  incidence_eq : ∀ s r, joint.incidenceAt (support s r) = incidence (base.incidenceAt s)
  lineage_eq : ∀ s r, joint.lineageAt (support s r) = lineage (base.lineageAt s)
  oldTransfer : ∀ s r, base.DispositionAt s .transfer → joint.DispositionAt (support s r) .transfer
  repairTransfer : ∀ s r, GeneratedStepAt law r ⊕ GeneratedTransportAt law r →
    joint.DispositionAt (support s r) .transfer
  openFibres : (∀ s k, Subsingleton (base.OpenAt s k)) → ∀ s k, Subsingleton (joint.OpenAt s k)

namespace Shape

variable {law : DebtActivationLaw} {base joint : WorldRelationNetwork}

def install (base : WorldRelationNetwork) (law : DebtActivationLaw) : Shape law base (ExtendedNetwork base law) where
  support := fun s r => (s, some r)
  rows := fun s r => expose base law s (some r)
  key := Sum.inl
  claim := Sum.inl
  repairKey := .inr law.debtId
  repairClaim := .inr law.debtClaim
  old_key := fun _ _ _ => rfl
  old_claim := fun _ _ _ => rfl
  old_budget := fun _ _ _ => rfl
  repair_key := fun _ _ => rfl
  repair_claim := fun _ _ => rfl
  repair_budget := fun _ _ => rfl
  anchor := id
  incidence := id
  lineage := id
  anchor_eq := fun _ _ => rfl
  incidence_eq := fun _ _ => rfl
  lineage_eq := fun _ _ => rfl
  oldTransfer := fun _ _ => Sum.inl
  repairTransfer := fun _ _ => Sum.inr
  openFibres := extended_subsingleton law

variable (shape : Shape law base joint)

abbrev original {s : base.Support} {r : law.DebtState} (entry : OpenResponsibilityAt base s) :=
  shape.rows s r (.inl entry)

abbrev repair (s : base.Support) (r : law.DebtState) := shape.rows s r (.inr ())

def extendedRows (next : DebtActivationLaw) (s : (ExtendedNetwork base next).Support) (r : law.DebtState) :
    (OpenResponsibilityAt (ExtendedNetwork base next) s ⊕ Unit) ≃
      OpenResponsibilityAt (ExtendedNetwork joint next) (shape.support s.1 r, s.2) :=
  (Equiv.sumCongr (expose base next s.1 s.2).symm (Equiv.refl Unit)).trans
    ((swapMiddle _ _ _).trans ((Equiv.sumCongr (shape.rows s.1 r) (Equiv.refl _)).trans
      (expose joint next (shape.support s.1 r) s.2)))

theorem extendedRows_old (next : DebtActivationLaw) (s : base.Support) (stage : Option next.DebtState)
    (r : law.DebtState) (entry : OpenResponsibilityAt base s) :
    extendedRows shape next (s, stage) r (.inl (oldEntry entry)) =
      oldEntry (shape.original (r := r) entry) := by
  cases stage <;> cases entry <;> rfl

theorem extendedRows_later (next : DebtActivationLaw) (s : base.Support) (stage : next.DebtState)
    (r : law.DebtState) :
    extendedRows shape next (s, some stage) r (.inl (debtEntry s stage)) =
      debtEntry (shape.support s r) stage := rfl

theorem extendedRows_repair (next : DebtActivationLaw) (s : base.Support) (stage : Option next.DebtState)
    (r : law.DebtState) :
    extendedRows shape next (s, stage) r (.inr ()) = oldEntry (shape.repair s r) := by
  cases stage <;> rfl

end Shape

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
