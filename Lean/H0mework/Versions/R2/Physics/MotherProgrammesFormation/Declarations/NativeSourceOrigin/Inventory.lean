import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.ActualOrigin.Consumer
import H0mework.Foundation.Source.SupportInventory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

/-- The full affected inventory is the complete open-responsibility fibre
already formed with the network. Support remains part of each event. -/
def native {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : Source N V) :
    SourceNativeSource N V where
  initial := source.initial
  law := {
    EventAt := fun c support => {event : source.actual.OccurrenceAt c // source.account.supportOf event = support}
    compile := fun event => source.actual.compile event.val
    AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt N support
    affectedInventoryPresentation := fun _ => {
      forward := id, backward := id, backward_forward := fun _ => rfl, forward_backward := fun _ => rfl }
    anchorKey := source.account.anchorKey
    incidenceKey := source.account.incidenceKey
    lineageKey := source.account.lineageKey
    anchor_commutes := fun event => (source.account.anchor_commutes event.val).trans
      (congrArg N.anchorAt event.property)
    incidence_commutes := fun event => (source.account.incidence_commutes event.val).trans
      (congrArg N.incidenceAt event.property)
    lineage_commutes := fun event => (source.account.lineage_commutes event.val).trans
      (congrArg N.lineageAt event.property) }

def eventEquiv {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : Source N V) (c : V.Current) :
    source.actual.OccurrenceAt c ≃ (native source).toRootSource.actual.OccurrenceAt c where
  toFun := fun event => ⟨source.account.supportOf event, ⟨event, rfl⟩⟩
  invFun := fun event => event.2.val
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨support, event, same⟩
    cases same
    rfl

theorem compile_original {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : Source N V)
    {c : V.Current} (event : source.actual.OccurrenceAt c) :
    (native source).toRootSource.actual.compile (eventEquiv source c event) = source.actual.compile event := rfl

theorem support_original {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : Source N V)
    {c : V.Current} (event : source.actual.OccurrenceAt c) :
    (native source).toRootSource.account.supportOf (eventEquiv source c event) =
      source.account.supportOf event := rfl

/-- Eliminate the original full presentation, retaining every inventory value
and its inverse. No new target inventory table is supplied to the factory. -/
def inventoryOriginal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (source : SourceNativeSource N V) {c : V.Current} {support : N.Support}
    (event : source.law.EventAt c support) :
    ConstructivePresentation (source.law.AffectedInventoryAt event)
      ((native source.toRootSource).law.AffectedInventoryAt
        (eventEquiv source.toRootSource c ⟨support, event⟩).2) :=
  source.law.affectedInventoryPresentation event

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
