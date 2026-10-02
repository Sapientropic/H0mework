import H0mework.Foundation.Responsibility.JointSource.Native.Image

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (program : Program lower)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)

abbrev Current := Sigma (EventAt registered)

def native (current : Current registered) : NativeAt current.2 :=
  let image := program.emit current.1
  nativeFromGenerated current.2 image.write image.structural_eq image.targetOccurrence
    image.evolution image.generated_eq

abbrev World := ExtendedNetwork N (Idle.law registered.input.environment registered.input.expression)

abbrev supportAt (current : Current registered) : (World registered).Support :=
  ⟨lower.source.source.toRootSource.account.supportOf (lower.emitted current.1), some current.2.state⟩

/-- Non-native fibres retain the old payload and its exact source occurrence;
this native program supplies no occurrence in those fibres. -/
def vocabulary : Vocabulary where
  Current := Current registered
  Anchor := V.Anchor
  Incidence := V.Incidence
  Lineage := V.Lineage
  anchorAt := fun current => V.anchorAt current.1
  incidenceAt := fun current => V.incidenceAt current.1
  lineageAt := fun current => V.lineageAt current.1
  NativeWriteAt := fun current => NativeAt current.2
  RelationWriteAt := fun current => {write : V.RelationWriteAt current.1 //
    lower.source.source.toRootSource.actual.compile (lower.emitted current.1) = .relationWrite write}
  ContinuedTransportAt := fun current => {write : V.ContinuedTransportAt current.1 //
    lower.source.source.toRootSource.actual.compile (lower.emitted current.1) = .continuedTransport write}
  BorromeanRedirectAt := fun current => {write : V.BorromeanRedirectAt current.1 //
    lower.source.source.toRootSource.actual.compile (lower.emitted current.1) = .borromeanRedirect write}
  FaithfulTerminalAt := fun current => {write : V.FaithfulTerminalAt current.1 //
    lower.source.source.toRootSource.actual.compile (lower.emitted current.1) = .faithfulTerminal write}
  nativeTarget := fun generated => ⟨V.nativeTarget generated.write, generated.nextEvent⟩
  relationTarget := by
    intro current payload
    have impossible := (program.emit current.1).structural_eq.symm.trans payload.2
    cases impossible
  continuedTarget := by
    intro current payload
    have impossible := (program.emit current.1).structural_eq.symm.trans payload.2
    cases impossible
  redirectTarget := by
    intro current payload
    have impossible := (program.emit current.1).structural_eq.symm.trans payload.2
    cases impossible

abbrev JointV := vocabulary program registered

inductive SourceEventAt : (current : Current registered) → (World registered).Support → Type u
  | generated (current : Current registered) : SourceEventAt current (supportAt registered current)

def eventAlgebra : SourceNativeEventAlgebra (World registered) (JointV program registered) where
  EventAt := SourceEventAt registered
  compile := by
    intro current support event
    cases event
    exact .nativeWrite (native program registered current)
  AffectedInventoryAt := fun {current} {_support} _ =>
    Option (lower.source.source.law.AffectedInventoryAt (lower.emitted current.1).2)
  affectedInventoryPresentation := by
    intro current support event
    cases event
    exact activeInventoryPresentation
      (law := Idle.law registered.input.environment registered.input.expression) current.2.state
      (lower.source.source.law.affectedInventoryPresentation (lower.emitted current.1).2)
  anchorKey := lower.source.source.law.anchorKey
  incidenceKey := lower.source.source.law.incidenceKey
  lineageKey := lower.source.source.law.lineageKey
  anchor_commutes := by
    intro current support event
    cases event
    exact lower.source.source.law.anchor_commutes (lower.emitted current.1).2
  incidence_commutes := by
    intro current support event
    cases event
    exact lower.source.source.law.incidence_commutes (lower.emitted current.1).2
  lineage_commutes := by
    intro current support event
    cases event
    exact lower.source.source.law.lineage_commutes (lower.emitted current.1).2

def source : SourceNativeSource (World registered) (JointV program registered) where
  initial := ⟨origin, initialEvent registered⟩
  law := eventAlgebra program registered

def emitted (current : Current registered) :
    (source program registered).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt registered current, .generated current⟩

def targetCurrent (current : Current registered) : Current registered :=
  (JointV program registered).nativeTarget (native program registered current)

def targetEvent (current : Current registered) :
    (source program registered).toRootSource.actual.OccurrenceAt (targetCurrent program registered current) :=
  emitted program registered (targetCurrent program registered current)

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
