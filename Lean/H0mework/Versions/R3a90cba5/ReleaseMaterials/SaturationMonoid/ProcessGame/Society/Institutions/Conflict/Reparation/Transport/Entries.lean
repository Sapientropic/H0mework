import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Shape

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld

abbrev Motion (law : DebtActivationLaw) (before after : law.DebtState) :=
  law.StepAt before after ⊕ law.TransportAt before after

namespace Motion

variable {law : DebtActivationLaw} {before after : law.DebtState}

def receipt : Motion law before after → GeneratedStepAt law before ⊕ GeneratedTransportAt law before
  | .inl payment => .inl ⟨after, payment⟩
  | .inr carry => .inr ⟨after, carry⟩

theorem budget_le (motion : Motion law before after) : law.budget after ≤ law.budget before :=
  motion.elim (fun step => (law.step_budget_lt step).le) law.transport_budget_le

end Motion

namespace Shape

variable {law : DebtActivationLaw} {base joint : WorldRelationNetwork}
  (shape : Shape law base joint) {before after : base.Support}
  {first last : law.DebtState}

private theorem anchor_preserved (same : base.anchorAt before = base.anchorAt after) :
    joint.anchorAt (shape.support before first) = joint.anchorAt (shape.support after last) :=
  (shape.anchor_eq _ _).trans ((congrArg shape.anchor same).trans (shape.anchor_eq _ _).symm)

private theorem incidence_preserved (same : base.incidenceAt before = base.incidenceAt after) :
    joint.incidenceAt (shape.support before first) = joint.incidenceAt (shape.support after last) :=
  (shape.incidence_eq _ _).trans ((congrArg shape.incidence same).trans (shape.incidence_eq _ _).symm)

private theorem lineage_preserved (same : base.lineageAt before = base.lineageAt after) :
    joint.lineageAt (shape.support before first) = joint.lineageAt (shape.support after last) :=
  (shape.lineage_eq _ _).trans ((congrArg shape.lineage same).trans (shape.lineage_eq _ _).symm)

private theorem claim_preserved {old : OpenResponsibilityAt base before} {next : OpenResponsibilityAt base after}
    (same : old.claim = next.claim) :
    (shape.original (r := first) old).claim = (shape.original (r := last) next).claim :=
  (shape.old_claim _ _ _).trans ((congrArg shape.claim same).trans (shape.old_claim _ _ _).symm)

/-- Preserve the old transfer or debit. When the old support carried a
row unchanged, the reparation transition accounts for the joint support. -/
def oldEvolution (motion : Motion law first last)
    {old : OpenResponsibilityAt base before} {next : OpenResponsibilityAt base after}
    (evolution : LedgerEntryEvolutionAt base old next) :
    LedgerEntryEvolutionAt joint (shape.original (r := first) old) (shape.original (r := last) next) := by
  cases evolution with
  | carried same entry =>
    cases same
    cases entry
    exact .transferred (shape.repairTransfer _ _ motion.receipt) (shape.lineage_preserved rfl)
      (shape.claim_preserved rfl) ((shape.old_budget _ _ _).trans (shape.old_budget _ _ _).symm).le
  | maintained anchor incidence lineage responsibility claim debit =>
    refine .maintained (shape.anchor_preserved anchor) (shape.incidence_preserved incidence)
      (shape.lineage_preserved lineage) ?_ (shape.claim_preserved claim) ?_
    · rw [shape.old_key, shape.old_key, responsibility]
    · rw [shape.old_budget, shape.old_budget]
      exact debit
  | transferred receipt lineage claim budget =>
    refine .transferred (shape.oldTransfer _ _ receipt) (shape.lineage_preserved lineage)
      (shape.claim_preserved claim) ?_
    rw [shape.old_budget, shape.old_budget]
    exact budget

def repairEvolution (motion : Motion law first last)
    (original : LedgerWriteEvolutionAt base ⟨before⟩ ⟨after⟩)
    (owner : OpenResponsibilityAt base before) :
    LedgerEntryEvolutionAt joint (shape.repair before first) (shape.repair after last) := by
  refine .transferred (shape.repairTransfer _ _ motion.receipt)
    (shape.lineage_preserved (original.destination owner).2.toDebtLineage.lineage_eq)
    ((shape.repair_claim _ _).trans (shape.repair_claim _ _).symm) ?_
  rw [shape.repair_budget, shape.repair_budget]
  exact motion.budget_le

end Shape

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
