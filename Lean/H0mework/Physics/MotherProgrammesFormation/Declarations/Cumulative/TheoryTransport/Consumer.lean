import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.TheoryTransport.Total

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section

private theorem presentation_cancel_right {A B C : Type}
    (value : A ≃ B) (right : C ≃ B) (original : ConstructivePresentation A C)
    (same : presentationFromEquiv value =
      presentationFromEquiv ((presentationEquiv original).trans right)) :
    presentationFromEquiv (value.trans right.symm) = original := by
  have transported := congrArg (fun presentation : ConstructivePresentation A B =>
    presentationFromEquiv ((presentationEquiv presentation).trans right.symm)) same
  exact transported.trans (presentation_conjugate_recovers (Equiv.refl _) right original)

/-- Compose the complete cross-network transporter with the fixed-network
material presentation. No original theory field is supplied to the factory. -/
def formedPresentation {N G : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N G)
    (old : TheoryState N) {generated : TheoryState G}
    (formed : MotherArenaTheory.Presentation (transportedTheory n old) generated) :
    Presentation n old generated where
  version := formed.version
  version_eq := formed.version_eq
  law := formed.law
  realization := fun support obstruction =>
    ((transportedPresentation n old).realization support obstruction).trans
      (formed.realization (n.support support) (n.obstructionAt support obstruction))
  without := fun choice support obstruction =>
    ((transportedPresentation n old).without choice support obstruction).trans
      (formed.without choice (n.support support) (n.obstructionAt support obstruction))
  expression := fun support =>
    ((transportedPresentation n old).expression support).trans (formed.expression (n.support support))
  denotes := fun support value =>
    formed.denotes (n.support support) ((transportedPresentation n old).expression support value)
  theoremMember := fun support value =>
    formed.theoremMember (n.support support) ((transportedPresentation n old).expression support value)
  presentation := fun support value =>
    presentation_cancel_right _ (n.holdsAt support (old.denotes value)) (old.theoremPresentation value)
      (formed.presentation (n.support support) ((transportedPresentation n old).expression support value))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport
