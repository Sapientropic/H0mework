import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.TheoryTransport.Fibers

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section

variable {N G : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N G)
    (old : TheoryState N)

def transportedInventory : LawInventory G where
  Version := old.inventory.Version
  version := old.inventory.version
  Law := old.inventory.Law
  RealizationAt := fun {support} obstruction =>
    Fiber (obstructionEquiv n) (fun point => old.inventory.RealizationAt point.2) ⟨support, obstruction⟩
  RealizationWithoutAt := fun law {support} obstruction =>
    Fiber (obstructionEquiv n) (fun point => old.inventory.RealizationWithoutAt law point.2) ⟨support, obstruction⟩

abbrev Expression (support : G.Support) := Fiber n.support old.ExpressionAt support

def holdsAt {support : G.Support} (expression : Expression n old support) :
    N.HoldsAt expression.val.1 (old.denotes expression.val.2) ≃
      G.HoldsAt support (n.claim (old.denotes expression.val.2)) :=
  (n.holdsAt expression.val.1 (old.denotes expression.val.2)).trans
    (Equiv.cast (congrArg (fun index => G.HoldsAt index (n.claim (old.denotes expression.val.2)))
      expression.property))

/-- Complete cross-network transport. The finite or infinite original law
inventory and language are retained through full dependent fibers. -/
def transportedTheory : TheoryState G where
  inventory := transportedInventory n old
  ExpressionAt := Expression n old
  denotes := fun expression => n.claim (old.denotes expression.val.2)
  TheoremAt := fun expression => old.TheoremAt expression.val.2
  theoremPresentation := fun expression =>
    presentationFromEquiv ((presentationEquiv (old.theoremPresentation expression.val.2)).trans
      (holdsAt n old expression))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport
