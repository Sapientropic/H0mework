import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Presentation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkRestriction
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section
variable {N G : WorldRelationNetwork.{0}} (p : MotherNetworkOrigin.Presentation N G)

/-- Original carrier types specify the inverse schema. Every value operation
is read from the actual generated network, including whole open-row budgets. -/
def restrictNetwork : WorldRelationNetwork.{0} where
  Support := N.Support
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  Responsibility := N.Responsibility
  Claim := N.Claim
  anchorAt := fun support => p.anchor.symm (G.anchorAt (p.support support))
  incidenceAt := fun support => p.incidence.symm (G.incidenceAt (p.support support))
  lineageAt := fun support => p.lineage.symm (G.lineageAt (p.support support))
  OpenAt := N.OpenAt
  openClaimAt := fun {support} {responsibility} entry => p.claim.symm (G.openClaimAt (p.openAt support responsibility entry))
  openProgressBudgetAt := fun {support} {responsibility} entry => G.openProgressBudgetAt (p.openAt support responsibility entry)
  HoldsAt := N.HoldsAt
  ObstructionAt := N.ObstructionAt
  obstructionClaim := fun {support} obstruction => p.claim.symm (G.obstructionClaim (p.obstructionAt support obstruction))
  SemanticChangeAt := N.SemanticChangeAt
  DispositionAt := N.DispositionAt

theorem restrictNetwork_eq : restrictNetwork p = N := by
  have anchorEq : (fun support => p.anchor.symm (G.anchorAt (p.support support))) = N.anchorAt :=
    funext fun support => (congrArg p.anchor.symm (p.anchor_commutes support)).trans (p.anchor.symm_apply_apply _)
  have incidenceEq : (fun support => p.incidence.symm (G.incidenceAt (p.support support))) = N.incidenceAt :=
    funext fun support => (congrArg p.incidence.symm (p.incidence_commutes support)).trans (p.incidence.symm_apply_apply _)
  have lineageEq : (fun support => p.lineage.symm (G.lineageAt (p.support support))) = N.lineageAt :=
    funext fun support => (congrArg p.lineage.symm (p.lineage_commutes support)).trans (p.lineage.symm_apply_apply _)
  have claimEq : (fun {support} {responsibility} entry => p.claim.symm (G.openClaimAt (p.openAt support responsibility entry))) =
      @N.openClaimAt := by
    funext support responsibility entry
    exact (congrArg p.claim.symm (p.openClaim_commutes support responsibility entry)).trans (p.claim.symm_apply_apply _)
  have budgetEq : (fun {support} {responsibility} entry => G.openProgressBudgetAt (p.openAt support responsibility entry)) =
      @N.openProgressBudgetAt := by
    funext support responsibility entry
    exact p.budget_commutes support responsibility entry
  have obstructionEq : (fun {support} obstruction => p.claim.symm (G.obstructionClaim (p.obstructionAt support obstruction))) =
      @N.obstructionClaim := by
    funext support obstruction
    exact (congrArg p.claim.symm (p.obstructionClaim_commutes support obstruction)).trans (p.claim.symm_apply_apply _)
  unfold restrictNetwork
  rw [anchorEq, incidenceEq, lineageEq, claimEq, budgetEq, obstructionEq]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkRestriction
