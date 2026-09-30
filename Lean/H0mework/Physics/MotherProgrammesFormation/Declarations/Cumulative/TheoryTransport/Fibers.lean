import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Presentation
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Presentation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section

/-- A complete dependent family over an equivalent base. The equality records
the actual index; no equivalence is used as a type equality. -/
def Fiber {A B : Type} (base : A ≃ B) (family : A → Type) (index : B) :=
  {point : (Σ value : A, family value) // base point.1 = index}

def fiberEquiv {A B : Type} (base : A ≃ B) (family : A → Type) (index : A) :
    family index ≃ Fiber base family (base index) :=
  Equiv.ofBijective (fun value => ⟨⟨index, value⟩, rfl⟩) (by
    constructor
    · intro first last same
      exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val same)).2
    · rintro ⟨⟨other, value⟩, same⟩
      have equal : other = index := base.injective same
      cases equal
      exact ⟨value, rfl⟩)

def fiberTotalEquiv {A B : Type} (base : A ≃ B) (family : A → Type) :
    (Σ value : A, family value) ≃ (Σ value : B, Fiber base family value) :=
  Equiv.sigmaCongr base (fiberEquiv base family)

abbrev ObstructionPoint (N : WorldRelationNetwork.{0}) := Σ support, N.ObstructionAt support

def obstructionEquiv {N G : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N G) :
    ObstructionPoint N ≃ ObstructionPoint G :=
  Equiv.sigmaCongr n.support n.obstructionAt

theorem obstructionClaim_commutes {N G : WorldRelationNetwork.{0}}
    (n : MotherNetworkOrigin.Presentation N G) (point : ObstructionPoint N) :
    G.obstructionClaim (obstructionEquiv n point).2 = n.claim (N.obstructionClaim point.2) :=
  n.obstructionClaim_commutes point.1 point.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport
