import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Operations
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Recovery

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section
variable {N : WorldRelationNetwork.{0}}

/-- Every original theory field is retained. The last field restores the
entire native theorem presentation, including its inverse programme. -/
structure Presentation (old generated : TheoryState N) where
  version : old.inventory.Version ≃ generated.inventory.Version
  version_eq : generated.inventory.version = version old.inventory.version
  law : old.inventory.Law ≃ generated.inventory.Law
  realization : ∀ support (obstruction : N.ObstructionAt support),
    old.inventory.RealizationAt obstruction ≃ generated.inventory.RealizationAt obstruction
  without : ∀ choice support (obstruction : N.ObstructionAt support),
    old.inventory.RealizationWithoutAt choice obstruction ≃ generated.inventory.RealizationWithoutAt (law choice) obstruction
  expression : ∀ support, old.ExpressionAt support ≃ generated.ExpressionAt support
  denotes : ∀ support value, generated.denotes (expression support value) = old.denotes value
  theoremMember : ∀ support value, old.TheoremAt value ≃ generated.TheoremAt (expression support value)
  presentation : ∀ support value,
    presentationFromEquiv ((theoremMember support value).trans
      ((presentationEquiv (generated.theoremPresentation (expression support value))).trans
        (Equiv.cast (congrArg (N.HoldsAt support) (denotes support value))))) = old.theoremPresentation value

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
