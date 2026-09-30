import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.TheoryTransport.Source

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section

/-- A complete theory correspondence over the given complete network
correspondence. The final equality retains both theorem programs. -/
structure Presentation {N G : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N G)
    (old : TheoryState N) (generated : TheoryState G) where
  version : old.inventory.Version ≃ generated.inventory.Version
  version_eq : generated.inventory.version = version old.inventory.version
  law : old.inventory.Law ≃ generated.inventory.Law
  realization : ∀ support (obstruction : N.ObstructionAt support),
    old.inventory.RealizationAt obstruction ≃ generated.inventory.RealizationAt (n.obstructionAt support obstruction)
  without : ∀ choice support (obstruction : N.ObstructionAt support),
    old.inventory.RealizationWithoutAt choice obstruction ≃
      generated.inventory.RealizationWithoutAt (law choice) (n.obstructionAt support obstruction)
  expression : ∀ support, old.ExpressionAt support ≃ generated.ExpressionAt (n.support support)
  denotes : ∀ support value, generated.denotes (expression support value) = n.claim (old.denotes value)
  theoremMember : ∀ support value, old.TheoremAt value ≃ generated.TheoremAt (expression support value)
  presentation : ∀ support value,
    presentationFromEquiv ((theoremMember support value).trans
      ((presentationEquiv (generated.theoremPresentation (expression support value))).trans
        ((Equiv.cast (congrArg (G.HoldsAt (n.support support)) (denotes support value))).trans
          (n.holdsAt support (old.denotes value)).symm))) = old.theoremPresentation value

variable {N G : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N G)
    (old : TheoryState N)

def transportedPresentation : Presentation n old (transportedTheory n old) where
  version := Equiv.refl _
  version_eq := rfl
  law := Equiv.refl _
  realization := fun support obstruction =>
    fiberEquiv (obstructionEquiv n) (fun point => old.inventory.RealizationAt point.2) ⟨support, obstruction⟩
  without := fun choice support obstruction =>
    fiberEquiv (obstructionEquiv n) (fun point => old.inventory.RealizationWithoutAt choice point.2)
      ⟨support, obstruction⟩
  expression := fiberEquiv n.support old.ExpressionAt
  denotes := fun _ _ => rfl
  theoremMember := fun _ _ => Equiv.refl _
  presentation := fun support value =>
    presentation_conjugate_recovers (Equiv.refl _) (n.holdsAt support (old.denotes value))
      (old.theoremPresentation value)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport
