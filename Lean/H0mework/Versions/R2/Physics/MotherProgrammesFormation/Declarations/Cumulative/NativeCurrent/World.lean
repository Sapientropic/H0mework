import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.NetworkRestriction.Native

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- Heterogeneous node consumers also need the complete network as a value.
It is inverse-read from the actual generated network before the dependent
current is transported across the resulting literal network equality. -/
def world {N G : WorldRelationNetwork.{0}} (p : MotherNetworkOrigin.Presentation N G)
    (current : SourceNativeLivingRootCurrentAt N) :
    Σ network : WorldRelationNetwork.{0}, SourceNativeLivingRootCurrentAt network :=
  ⟨MotherNetworkRestriction.restrictNetwork p,
    Equiv.cast (congrArg SourceNativeLivingRootCurrentAt (MotherNetworkRestriction.restrictNetwork_eq p).symm) current⟩

private theorem actual_cast_heq {A B : Type 3} (same : A = B) (value : A) :
    HEq (Equiv.cast same value) value := by cases same; rfl

theorem world_eq {N G : WorldRelationNetwork.{0}} (p : MotherNetworkOrigin.Presentation N G)
    (current : SourceNativeLivingRootCurrentAt N) : world p current = ⟨N, current⟩ :=
  Sigma.ext (MotherNetworkRestriction.restrictNetwork_eq p)
    (actual_cast_heq (congrArg SourceNativeLivingRootCurrentAt (MotherNetworkRestriction.restrictNetwork_eq p).symm) current)

theorem world_of_formed {rank : Ordinal.{0}} {N G : WorldRelationNetwork.{0}}
    (p : MotherNetworkOrigin.Presentation N G) (old : SourceNativeLivingRootCurrentAt N)
    (header : Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, SourceNativeLivingRootClosure N vocabulary)
    (material : MotherArenaHigher.Material rank) (formed : formCurrent header material = some old) :
    ∃ available : (formCurrent header material).isSome,
      world p ((formCurrent header material).get available) = ⟨N, old⟩ := by
  have available : (formCurrent header material).isSome := by rw [formed]; rfl
  have same : (formCurrent header material).get available = old :=
    Option.some.inj ((Option.some_get available).trans formed)
  exact ⟨available, (congrArg (world p) same).trans (world_eq p old)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
