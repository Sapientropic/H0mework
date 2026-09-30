import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.TheoryTransport.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport.Presentation
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {n : MotherNetworkOrigin.Presentation N G}
    {old : TheoryState N} {generated : TheoryState G} (p : Presentation n old generated)

def restrictInventory : LawInventory N where
  Version := old.inventory.Version
  version := p.version.symm generated.inventory.version
  Law := old.inventory.Law
  RealizationAt := old.inventory.RealizationAt
  RealizationWithoutAt := old.inventory.RealizationWithoutAt

theorem restrictInventory_eq : p.restrictInventory = old.inventory := by
  have selected : p.version.symm generated.inventory.version = old.inventory.version :=
    (congrArg p.version.symm p.version_eq).trans (p.version.symm_apply_apply _)
  unfold restrictInventory
  rw [selected]

def restrictDenotes (support : N.Support) (value : old.ExpressionAt support) : N.Claim :=
  n.claim.symm (generated.denotes (p.expression support value))

theorem restrictDenotes_eq : p.restrictDenotes = fun (support : N.Support) (value : old.ExpressionAt support) => old.denotes value := by
  funext support value
  exact (congrArg n.claim.symm (p.denotes support value)).trans (n.claim.symm_apply_apply _)

def restrictTheoremPresentation (support : N.Support) (value : old.ExpressionAt support) :
    ConstructivePresentation (old.TheoremAt value) (N.HoldsAt support (old.denotes value)) :=
  presentationFromEquiv ((p.theoremMember support value).trans
    ((presentationEquiv (generated.theoremPresentation (p.expression support value))).trans
      ((Equiv.cast (congrArg (G.HoldsAt (n.support support)) (p.denotes support value))).trans
        (n.holdsAt support (old.denotes value)).symm)))

theorem restrictTheoremPresentation_eq (support : N.Support) (value : old.ExpressionAt support) :
    p.restrictTheoremPresentation support value = old.theoremPresentation value :=
  p.presentation support value

/-- A faithful restriction in the original type indices. All data-valued
operations, including both theorem programs, are read from the generated
theory; the complete family correspondences specify their inverse schemas. -/
def restrictTheory : TheoryState N where
  inventory := p.restrictInventory
  ExpressionAt := old.ExpressionAt
  denotes := fun {support} value => p.restrictDenotes support value
  TheoremAt := old.TheoremAt
  theoremPresentation := fun {support} value =>
    Equiv.cast (congrArg (fun claim => ConstructivePresentation (old.TheoremAt value) (N.HoldsAt support claim))
      (congrFun (congrFun p.restrictDenotes_eq support) value).symm)
      (p.restrictTheoremPresentation support value)

private theorem assembled_restriction_eq (inventory : LawInventory N)
    (inventory_eq : inventory = old.inventory)
    (denotes : ∀ support, old.ExpressionAt support → N.Claim)
    (denotes_eq : denotes = fun support (value : old.ExpressionAt support) => old.denotes value)
    (programmes : ∀ support (value : old.ExpressionAt support),
      ConstructivePresentation (old.TheoremAt value) (N.HoldsAt support (old.denotes value)))
    (programmes_eq : programmes = fun support (value : old.ExpressionAt support) => old.theoremPresentation value) :
    (show TheoryState N from {
      inventory := inventory
      ExpressionAt := old.ExpressionAt
      denotes := fun {support} value => denotes support value
      TheoremAt := old.TheoremAt
      theoremPresentation := fun {support} value =>
        Equiv.cast (congrArg (fun claim => ConstructivePresentation (old.TheoremAt value) (N.HoldsAt support claim))
          (congrFun (congrFun denotes_eq support) value).symm) (programmes support value) }) = old := by
  cases inventory_eq
  cases denotes_eq
  cases programmes_eq
  rfl

theorem restrictTheory_eq : p.restrictTheory = old :=
  assembled_restriction_eq p.restrictInventory p.restrictInventory_eq p.restrictDenotes p.restrictDenotes_eq
    p.restrictTheoremPresentation (funext fun support => funext (p.restrictTheoremPresentation_eq support))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport.Presentation
