import H0mework.Arithmetic.GoldbachDynamics.DecayReachability
import H0mework.Foundation.Finite.EventProcess

/-!
# Operational factor-decay dynamics

Every repair/emission alternative is now an event of one source-owned
event-indexed residual process.  Its signed endpoint difference is the forced
ordered trace, and the canonical write-back reconstructs the source split
from the exact event target.  Existing finite branching paths lift
constructor-for-constructor to these operational paths.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticOperationalFactorDecayProducer

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorDecayReachabilityProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticFullFactorRepairProducer
open CanonicalUnitArithmeticRoot
open SourceGeneratedFiniteEffectiveBranchingReachability
open SourceGeneratedFiniteEventIndexedResidualProcess

noncomputable section

abbrev SignedEndpointResidual := ℤ × ℤ

def splitResidual {index : Nat}
    (state : EffectiveSplitAt index) : SignedEndpointResidual :=
  ((splitLeft state : ℤ), (splitRight state : ℤ))

def factorDecayKeep {index : Nat} {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source)
    (_residual : SignedEndpointResidual) : SignedEndpointResidual :=
  splitResidual channel.target

def factorDecayTrace {index : Nat} {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : SignedEndpointResidual :=
  splitResidual source - splitResidual channel.target

def recollectFactorDecay
    (live trace : SignedEndpointResidual) : SignedEndpointResidual :=
  live + trace

theorem factorDecayChannel_target_ne {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    channel.target ≠ source := by
  intro targetEq
  cases channel with
  | repair alternative =>
      cases alternative with
      | left leftNotPrime selected =>
          have strict := FactorRepairAlternativeAt.left_target_strict
            leftNotPrime selected
          have endpointEq := congrArg splitLeft targetEq
          change splitLeft
              (FactorRepairAlternativeAt.left leftNotPrime selected).target =
            splitLeft source at endpointEq
          exact (ne_of_lt strict) endpointEq
      | right rightNotPrime selected =>
          have strict := FactorRepairAlternativeAt.right_target_strict
            rightNotPrime selected
          have endpointEq := congrArg splitLeft targetEq
          change splitLeft
              (FactorRepairAlternativeAt.right rightNotPrime selected).target =
            splitLeft source at endpointEq
          exact (ne_of_gt strict) endpointEq
  | emission alternative =>
      cases alternative with
      | left leftNotPrime selected =>
          have strict := left_factorEmission_strict leftNotPrime selected
          have endpointEq := congrArg splitLeft targetEq
          change splitLeft (factorEmissionTarget
              (FactorRepairAlternativeAt.left leftNotPrime selected)) =
            splitLeft source at endpointEq
          exact (ne_of_lt strict) endpointEq
      | right rightNotPrime selected =>
          have strict := right_factorEmission_strict rightNotPrime selected
          have endpointEq := congrArg splitRight targetEq
          change splitRight (factorEmissionTarget
              (FactorRepairAlternativeAt.right rightNotPrime selected)) =
            splitRight source at endpointEq
          exact (ne_of_lt strict) endpointEq

theorem recollectFactorDecay_step {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    recollectFactorDecay (splitResidual channel.target)
        (factorDecayTrace channel) =
      splitResidual source := by
  apply Prod.ext <;>
    simp [recollectFactorDecay, factorDecayTrace, splitResidual]

theorem factorDecayTrace_total_zero {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    (factorDecayTrace channel).1 + (factorDecayTrace channel).2 = 0 := by
  have sourceLanding := split_landing source
  have targetLanding := channel.target_lands
  change
    (splitLeft source : ℤ) - splitLeft channel.target +
        ((splitRight source : ℤ) - splitRight channel.target) = 0
  omega

abbrev factorDecayProcess (index : Nat) : Process where
  State := EffectiveSplitAt index
  Residual := SignedEndpointResidual
  Trace := SignedEndpointResidual
  EventAt := FactorDecayChannelAt
  update := FactorDecayChannelAt.target
  update_ne := factorDecayChannel_target_ne
  residual := splitResidual
  keep := factorDecayKeep
  residual_transport := by intro state channel; rfl
  stepTrace := factorDecayTrace
  recollect := recollectFactorDecay
  recollect_step := recollectFactorDecay_step

/-- Finite observer key for a structural channel.  It intentionally forgets
the occurrence history; occurrence-sensitive physical incidence is supplied
by the provenance layer. -/
abbrev FactorDecayStructuralChannelKeyAt (index : Nat) :=
  Sigma (FactorDecayChannelAt : EffectiveSplitAt index → Type)

def factorDecayAuthority (index : Nat) : Authority (factorDecayProcess index) where
  Content := UnitHistory
  Bearer := EffectiveSplitAt index
  Scope := RootedAccountedUnfolding AdditiveCalculationPoint
  Lineage := UnitHistory
  Incidence := FactorDecayStructuralChannelKeyAt index
  SourceObservation := ComplementObservation.canonicalComplementPair
  content := fun _ => evenTargetHistory index
  anchor := fun _ =>
    MinimalRegistrableSourceAnchor.canonical
      (evenTargetOccurrence index) (evenTargetHistory index)
  incidence := fun {state} event => ⟨state, event⟩
  ObstructionAt := fun _ => PUnit
  obstructionContent := fun _ => evenTargetHistory index
  obstructionState := fun {state} _ => state
  admissionBearer := id
  nextBearer := FactorDecayChannelAt.target
  RouteAt := fun _ _ _ => PUnit
  routeReceipt := fun _ _ => PUnit.unit
  content_update := by intro state event; rfl

abbrev OperationalFactorDecayNativeProcess (index : Nat) :=
  NativeProcess (factorDecayProcess index) (factorDecayAuthority index)

instance operationalFactorDecayBearerDecidableEq (index : Nat) :
    DecidableEq (OperationalFactorDecayNativeProcess index).Bearer := by
  change DecidableEq (EffectiveSplitAt index)
  infer_instance

def nativeFactorDecayAdmission {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    NativeResidualUpdate.AdmissionEvent
      (OperationalFactorDecayNativeProcess index) where
  source := ⟨source, channel⟩
  obstruction := PUnit.unit
  content_eq := rfl
  residual_eq := rfl

def nativeFactorDecayBoundary {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    NativeResidualUpdate.BoundaryEvent
      (OperationalFactorDecayNativeProcess index)
      (NativeResidualUpdate.admittedObligation
        (OperationalFactorDecayNativeProcess index)
        (nativeFactorDecayAdmission channel)) where
  source := (nativeFactorDecayAdmission channel).source
  residual_eq := rfl
  content_eq := rfl
  anchor_eq := rfl
  incidence_eq := rfl

def nativeFactorDecayProgressReceipt {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :=
  NativeResidualUpdate.progressReceipt
    (OperationalFactorDecayNativeProcess index)
    (nativeFactorDecayBoundary channel)

noncomputable def nativeFactorDecayProgressEvent {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    NativeResidualUpdate.ProgressEventAt
      (OperationalFactorDecayNativeProcess index)
      (NativeResidualUpdate.admittedState
        (OperationalFactorDecayNativeProcess index)
        (nativeFactorDecayAdmission channel)) := by
  let cursor := NativeResidualUpdate.initialLive
    (OperationalFactorDecayNativeProcess index)
    (nativeFactorDecayAdmission channel)
  exact
    { slot := cursor.slot
      obligation := cursor.obligation
      present := cursor.present
      boundary := nativeFactorDecayBoundary channel }

noncomputable def compileFactorDecayLifecycleEdge {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :=
  NativeResidualUpdate.compileProgressEdge
    (OperationalFactorDecayNativeProcess index)
    (nativeFactorDecayProgressEvent channel)

theorem compileFactorDecayLifecycleEdge_is_progress {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    (compileFactorDecayLifecycleEdge channel).lifecycleEvent.kind.IsProgress :=
  NativeResidualUpdate.compileProgressEdge_kind
    (OperationalFactorDecayNativeProcess index)
    (nativeFactorDecayProgressEvent channel)

/-- Exact dependent lifecycle-edge type generated from one factor channel. -/
abbrev FactorDecayLifecycleEdgeAt {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :=
  (NativeResidualUpdate.RP
    (OperationalFactorDecayNativeProcess index)).Edge
      (NativeResidualUpdate.admittedState
        (OperationalFactorDecayNativeProcess index)
        (nativeFactorDecayAdmission channel))

def operationalSourceEvent {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    SourceGeneratedFiniteEventIndexedResidualProcess.SourceEvent
      (factorDecayProcess index) :=
  ⟨source, channel⟩

def compileFactorDecayEvent {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    GeneratedStepAt (factorDecayProcess index) :=
  canonicalCompile (factorDecayProcess index)
    (operationalSourceEvent channel)

theorem compileFactorDecayEvent_target {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    (compileFactorDecayEvent channel).target = channel.target :=
  rfl

theorem compileFactorDecayEvent_trace {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    (compileFactorDecayEvent channel).trace = factorDecayTrace channel :=
  rfl

theorem compileFactorDecayEvent_writeBack_recollects {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    (factorDecayProcess index).recollectTrace
        (compileFactorDecayEvent channel).writeBack.live
        (compileFactorDecayEvent channel).writeBack.trace =
      splitResidual source :=
  (compileFactorDecayEvent channel).writeBack.recollects_source

/-- One channel's complete operational receipt.  The finite residual step and
the responsibility lifecycle edge are generated from the same dependent
factor channel; neither target can be replaced by a caller. -/
structure OperationalFactorDecayChannelReceiptAt {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : Type where
  private mk ::
  step : GeneratedStepAt (factorDecayProcess index)
  step_eq : step = compileFactorDecayEvent channel
  lifecycleEdge : FactorDecayLifecycleEdgeAt channel
  lifecycleEdge_eq : lifecycleEdge = compileFactorDecayLifecycleEdge channel
  lifecycleProgress : lifecycleEdge.lifecycleEvent.kind.IsProgress

noncomputable def generateChannelReceipt {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    OperationalFactorDecayChannelReceiptAt channel :=
  { step := compileFactorDecayEvent channel
    step_eq := rfl
    lifecycleEdge := compileFactorDecayLifecycleEdge channel
    lifecycleEdge_eq := rfl
    lifecycleProgress := compileFactorDecayLifecycleEdge_is_progress channel }

namespace OperationalFactorDecayChannelReceiptAt

variable {index : Nat} {source : EffectiveSplitAt index}
  {channel : FactorDecayChannelAt source}

theorem target_eq (receipt : OperationalFactorDecayChannelReceiptAt channel) :
    receipt.step.target = channel.target := by
  rw [receipt.step_eq]
  exact compileFactorDecayEvent_target channel

theorem trace_eq (receipt : OperationalFactorDecayChannelReceiptAt channel) :
    receipt.step.trace = factorDecayTrace channel := by
  rw [receipt.step_eq]
  exact compileFactorDecayEvent_trace channel

theorem trace_total_zero
    (receipt : OperationalFactorDecayChannelReceiptAt channel) :
    receipt.step.trace.1 + receipt.step.trace.2 = 0 := by
  rw [receipt.trace_eq]
  exact factorDecayTrace_total_zero channel

theorem writeBack_recollects
    (receipt : OperationalFactorDecayChannelReceiptAt channel) :
    (factorDecayProcess index).recollectTrace
        receipt.step.writeBack.live receipt.step.writeBack.trace =
      splitResidual source := by
  rw [receipt.step_eq]
  exact compileFactorDecayEvent_writeBack_recollects channel

end OperationalFactorDecayChannelReceiptAt

/-- Existing mathematical paths lift without changing any event or target. -/
def operationalizePath {index : Nat}
    {source target : EffectiveSplitAt index} :
    SourceGeneratedFiniteEffectiveBranchingReachability.GeneratedPathAt
        (fullFactorDecayLaw index) source target →
      SourceGeneratedFiniteEventIndexedResidualProcess.GeneratedPathAt
        (factorDecayProcess index) source target
  | .nil => .nil
  | .snoc prior channel => .snoc (operationalizePath prior) channel

def operationalPathWriteBack {index : Nat}
    {source target : EffectiveSplitAt index}
    (path : SourceGeneratedFiniteEffectiveBranchingReachability.GeneratedPathAt
      (fullFactorDecayLaw index) source target) :=
  (operationalizePath path).writeBack

/-- Constructor-for-constructor operational receipt for one already generated
finite branching path. -/
structure OperationalFactorDecayPathReceiptAt {index : Nat}
    {source target : EffectiveSplitAt index}
    (sourcePath :
      SourceGeneratedFiniteEffectiveBranchingReachability.GeneratedPathAt
        (fullFactorDecayLaw index) source target) : Type where
  private mk ::
  path : SourceGeneratedFiniteEventIndexedResidualProcess.GeneratedPathAt
    (factorDecayProcess index) source target
  path_eq : path = operationalizePath sourcePath
  writeBack : PathWriteBack (factorDecayProcess index) path
  writeBack_eq : HEq writeBack (operationalizePath sourcePath).writeBack

def generatePathReceipt {index : Nat}
    {source target : EffectiveSplitAt index}
    (sourcePath :
      SourceGeneratedFiniteEffectiveBranchingReachability.GeneratedPathAt
        (fullFactorDecayLaw index) source target) :
    OperationalFactorDecayPathReceiptAt sourcePath :=
  { path := operationalizePath sourcePath
    path_eq := rfl
    writeBack := (operationalizePath sourcePath).writeBack
    writeBack_eq := HEq.rfl }

end
end CanonicalUnitArithmeticOperationalFactorDecayProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
