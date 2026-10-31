import H0mework.Versions.R2.Foundation.Authority.SourceProjectionInventory
import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Material faces of the original socioeconomic root occurrence

This is the physical readout interface consumed by the universal window
theorems.  Its event is a restriction of the original actual occurrence;
its target and whole-ledger disposition are calculated by the original
source.  Classification producers supply its three acquisition faces separately.
`stockAt` counts executable-use stock relative to the source relation family;
a transfer through a control gate is acquisition even when no goods are newly
produced.  Raw physical production and financial claims are separate source
readouts.  Quantities need no discreteness, minimum cost or Archimedean axiom.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u

abbrev NativeEventAt {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) (current : V.Current) :=
  source.source.toRootSource.actual.OccurrenceAt current

abbrev ContinuingEventAt {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) (current : V.Current) :=
  { occurrence : NativeEventAt source current //
    (source.source.toRootSource.actual.compile occurrence).nextCurrent?.isSome = true }

def actualTarget {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    (event : ContinuingEventAt source current) : V.Current :=
  (source.source.toRootSource.actual.compile event.val).nextCurrent?.get event.property

theorem actualTarget_exact {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    (event : ContinuingEventAt source current) :
    (source.source.toRootSource.actual.compile event.val).nextCurrent? =
      some (actualTarget event) := by
  exact (Option.some_get event.property).symm

/-- No institutional name, wage label or capitalism-membership proposition
enters this interface.  An unresolved positive quantity must expose a row of
the exact original responsibility fibre, never a new residual registry. -/
structure RootEconomicMaterialLaw
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) (Quantity : Type u)
    [AddCommMonoid Quantity] [LinearOrder Quantity] [IsOrderedCancelAddMonoid Quantity] :
    Type (u + 1) where
  Good : Type u
  Clock : Type u
  stockAt : V.Current → Good → Quantity
  StockInvariant : V.Current → Prop
  stock_nonnegative : ∀ current, StockInvariant current → ∀ good, 0 ≤ stockAt current good
  invariant_next : {current : V.Current} → (event : ContinuingEventAt source current) →
    StockInvariant current → StockInvariant (actualTarget event)
  clockAt : V.Current → Clock
  necessaryUse : {current : V.Current} → ContinuingEventAt source current → Good → Quantity
  reproduction : {current : V.Current} → ContinuingEventAt source current → Good → Quantity
  dependentAcquired : {current : V.Current} → ContinuingEventAt source current → Good → Quantity
  independentAcquired : {current : V.Current} → ContinuingEventAt source current → Good → Quantity
  unclassifiedAcquired : {current : V.Current} → ContinuingEventAt source current → Good → Quantity
  otherOutflow : {current : V.Current} → ContinuingEventAt source current → Good → Quantity
  quantities_nonnegative : {current : V.Current} → (event : ContinuingEventAt source current) →
    (good : Good) → 0 ≤ necessaryUse event good ∧ 0 ≤ reproduction event good ∧
      0 ≤ dependentAcquired event good ∧ 0 ≤ independentAcquired event good ∧
      0 ≤ unclassifiedAcquired event good ∧ 0 ≤ otherOutflow event good
  balance : {current : V.Current} → (event : ContinuingEventAt source current) → (good : Good) →
    stockAt (actualTarget event) good + necessaryUse event good +
        reproduction event good + otherOutflow event good =
      stockAt current good + dependentAcquired event good +
        independentAcquired event good + unclassifiedAcquired event good
  unclassifiedBearer : {current : V.Current} → (event : ContinuingEventAt source current) →
    (good : Good) → 0 < unclassifiedAcquired event good →
      OpenResponsibilityAt N (source.source.toRootSource.account.supportOf event.val)

namespace RootEconomicMaterialLaw

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {source : SourceNativeLedgerSource N V}
  {Quantity : Type u} [AddCommMonoid Quantity] [LinearOrder Quantity]
  [IsOrderedCancelAddMonoid Quantity] (law : RootEconomicMaterialLaw source Quantity)

abbrev Current (_law : RootEconomicMaterialLaw source Quantity) := V.Current
abbrev EventAt (_law : RootEconomicMaterialLaw source Quantity) := ContinuingEventAt source

def target {current : law.Current} (event : law.EventAt current) : law.Current :=
  actualTarget event

def stock (current : law.Current) (good : law.Good) : Quantity := law.stockAt current good
def clock (current : law.Current) : law.Clock := law.clockAt current

def wholeLedgerWriteBack {current : law.Current} (event : law.EventAt current) :=
  source.ledgerCompiler.compile event.val

def originalDisposition {current : law.Current} (event : law.EventAt current)
    (entry : OpenResponsibilityAt N
      (source.source.toRootSource.account.supportOf event.val)) :
    LedgerEntryDispositionAt N entry :=
  (law.wholeLedgerWriteBack event).entryDisposition entry

theorem target_is_original {current : law.Current} (event : law.EventAt current) :
    (source.source.toRootSource.actual.compile event.val).nextCurrent? =
      some (law.target event) := actualTarget_exact event

def unresolvedDisposition {current : law.Current} (event : law.EventAt current)
    (good : law.Good) (unresolved : 0 < law.unclassifiedAcquired event good) :
    LedgerEntryDispositionAt N (law.unclassifiedBearer event good unresolved) :=
  law.originalDisposition event (law.unclassifiedBearer event good unresolved)

/-- A zero-field dependent face.  All material and responsibility readouts
remain fixed functions of the same original source occurrence. -/
structure FaceAt (law : RootEconomicMaterialLaw source Quantity)
    {current : V.Current} (occurrence : NativeEventAt source current)
    (_continuing : (source.source.toRootSource.actual.compile occurrence).nextCurrent?.isSome = true) :
    Type u where
  private mk ::

def faceAt {current : V.Current} (event : law.EventAt current) :
    law.FaceAt event.val event.property := .mk

def toProjectionLaw : SourceNativeProjectionLaw source where
  Projection := PUnit
  ActiveAt := fun _ {_current} occurrence =>
    ULift (PLift ((source.source.toRootSource.actual.compile occurrence).nextCurrent?.isSome = true))
  InactiveAt := fun _ {_current} occurrence =>
    ULift (PLift ((source.source.toRootSource.actual.compile occurrence).nextCurrent?.isSome ≠ true))
  classify := fun _ {_current} occurrence =>
    if continuing : (source.source.toRootSource.actual.compile occurrence).nextCurrent?.isSome = true then
      .inl ⟨⟨continuing⟩⟩ else .inr ⟨⟨continuing⟩⟩
  PayloadAt := fun _ {_current} occurrence continuing =>
    law.FaceAt occurrence continuing.down.down
  project := fun _ {_current} occurrence continuing =>
    law.faceAt ⟨occurrence, continuing.down.down⟩

theorem same_event_same_target {current : law.Current}
    (left right : law.EventAt current) (same : left.val = right.val) :
    law.target left = law.target right := by
  have equal : left = right := Subtype.ext same
  exact congrArg law.target equal

end RootEconomicMaterialLaw

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source
