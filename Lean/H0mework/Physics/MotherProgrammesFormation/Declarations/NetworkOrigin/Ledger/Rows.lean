import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Presentation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def Presentation.mapRow {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {s t : N.Support} {a : OpenResponsibilityAt N s} {b : OpenResponsibilityAt N t}
    (row : LedgerEntryEvolutionAt N a b) : LedgerEntryEvolutionAt G (p.ledger s a) (p.ledger t b) := by
  cases row with
  | carried supportEq entryEq =>
      cases supportEq
      cases entryEq
      exact .carried rfl HEq.rfl
  | maintained anchorEq incidenceEq lineageEq responsibilityEq claimEq debit =>
      refine .maintained ?_ ?_ ?_ (congrArg p.responsibility responsibilityEq) ?_ ?_
      · exact (p.anchor_commutes s).trans ((congrArg p.anchor anchorEq).trans (p.anchor_commutes t).symm)
      · exact (p.incidence_commutes s).trans ((congrArg p.incidence incidenceEq).trans (p.incidence_commutes t).symm)
      · exact (p.lineage_commutes s).trans ((congrArg p.lineage lineageEq).trans (p.lineage_commutes t).symm)
      · exact (p.ledger_claim s a).trans ((congrArg p.claim claimEq).trans (p.ledger_claim t b).symm)
      · simpa only [p.ledger_budget] using debit
  | transferred receipt lineageEq claimEq budget =>
      refine .transferred (p.dispositionAt s .transfer receipt) ?_ ?_ ?_
      · exact (p.lineage_commutes s).trans ((congrArg p.lineage lineageEq).trans (p.lineage_commutes t).symm)
      · exact (p.ledger_claim s a).trans ((congrArg p.claim claimEq).trans (p.ledger_claim t b).symm)
      · simpa only [p.ledger_budget] using budget

def Presentation.restoreRow {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {s t : N.Support} {a : OpenResponsibilityAt N s} {b : OpenResponsibilityAt N t}
    (row : LedgerEntryEvolutionAt G (p.ledger s a) (p.ledger t b)) : LedgerEntryEvolutionAt N a b := by
  cases row with
  | carried supportEq entryEq =>
      have same := p.support.injective supportEq
      cases same
      have entries := (p.ledger s).injective (eq_of_heq entryEq)
      cases entries
      exact .carried rfl HEq.rfl
  | maintained anchorEq incidenceEq lineageEq responsibilityEq claimEq debit =>
      refine .maintained ?_ ?_ ?_ (p.responsibility.injective responsibilityEq) ?_ ?_
      · exact p.anchor.injective ((p.anchor_commutes s).symm.trans (anchorEq.trans (p.anchor_commutes t)))
      · exact p.incidence.injective ((p.incidence_commutes s).symm.trans (incidenceEq.trans (p.incidence_commutes t)))
      · exact p.lineage.injective ((p.lineage_commutes s).symm.trans (lineageEq.trans (p.lineage_commutes t)))
      · exact p.claim.injective ((p.ledger_claim s a).symm.trans (claimEq.trans (p.ledger_claim t b)))
      · simpa only [p.ledger_budget] using debit
  | transferred receipt lineageEq claimEq budget =>
      refine .transferred ((p.dispositionAt s .transfer).symm receipt) ?_ ?_ ?_
      · exact p.lineage.injective ((p.lineage_commutes s).symm.trans (lineageEq.trans (p.lineage_commutes t)))
      · exact p.claim.injective ((p.ledger_claim s a).symm.trans (claimEq.trans (p.ledger_claim t b)))
      · simpa only [p.ledger_budget] using budget

theorem Presentation.restore_map_row {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {s t : N.Support} {a : OpenResponsibilityAt N s} {b : OpenResponsibilityAt N t}
    (row : LedgerEntryEvolutionAt N a b) : p.restoreRow (p.mapRow row) = row := by
  cases row with
  | carried supportEq entryEq =>
      cases supportEq
      cases entryEq
      rfl
  | maintained => rfl
  | transferred receipt lineageEq claimEq budget =>
      simp only [mapRow, restoreRow, Equiv.symm_apply_apply]

theorem Presentation.map_restore_row {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {s t : N.Support} {a : OpenResponsibilityAt N s} {b : OpenResponsibilityAt N t}
    (row : LedgerEntryEvolutionAt G (p.ledger s a) (p.ledger t b)) :
    p.mapRow (p.restoreRow row) = row := by
  cases row with
  | carried supportEq entryEq =>
      have same := p.support.injective supportEq
      cases same
      have entries := (p.ledger s).injective (eq_of_heq entryEq)
      cases entries
      rfl
  | maintained => rfl
  | transferred receipt lineageEq claimEq budget =>
      simp only [mapRow, restoreRow, Equiv.apply_symm_apply]

def Presentation.rowEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {s t : N.Support} (a : OpenResponsibilityAt N s) (b : OpenResponsibilityAt N t) :
    LedgerEntryEvolutionAt N a b ≃ LedgerEntryEvolutionAt G (p.ledger s a) (p.ledger t b) where
  toFun := p.mapRow
  invFun := p.restoreRow
  left_inv := p.restore_map_row
  right_inv := p.map_restore_row

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
