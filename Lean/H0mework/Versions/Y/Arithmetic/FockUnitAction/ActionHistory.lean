import H0mework.Versions.X.Arithmetic.GoldbachDynamics.ExactOperationalFace
import H0mework.Versions.Y.Arithmetic.FockState.FactorDecay

/-!
# Exact fixed-target action histories

Every channel of an existing full repair/emission path is compiled to its
operational receipt and Fock-kernel effect.  These chronological action
payloads contain no terminal, fibre, coefficient, settlement, or next-current
field.  The whole path remains rooted in the exact occurrence which generated
the fixed even target.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityActionHistory

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer
open CanonicalUnitArithmeticFullFactorDecayReachabilityProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open ParticleWaveFock
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

/-- One actual factor channel together with its operational and Fock effects.
The private constructor prevents replacement receipts. -/
structure GeneratedFactorActionAt {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : Type where
  private mk ::
  operational : OperationalFactorDecayChannelReceiptAt channel
  operational_eq : operational = generateChannelReceipt channel
  fock : GeneratedFactorDecayFockTraceAt channel operational
  fock_eq : HEq fock
    (generateFactorDecayFockTrace channel (generateChannelReceipt channel))

def generateFactorAction {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    GeneratedFactorActionAt channel :=
  { operational := generateChannelReceipt channel
    operational_eq := rfl
    fock := generateFactorDecayFockTrace channel
      (generateChannelReceipt channel)
    fock_eq := HEq.rfl }

/-- Dependent payload for one edge.  The source state and channel remain in
the sigma index, while the generated operational/Fock material is the value. -/
abbrev GeneratedFactorAction (index : Nat) :=
  Sigma fun source : EffectiveSplitAt index =>
    Sigma fun channel : FactorDecayChannelAt source =>
      GeneratedFactorActionAt channel

def generatedFactorAction {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : GeneratedFactorAction index :=
  ⟨source, channel, generateFactorAction channel⟩

/-- Derived action payloads.  The existing `GeneratedPathAt` remains the sole
chronology; this list is only its edgewise Fock readout. -/
def actionPayloads {index : Nat}
    {start target : EffectiveSplitAt index} :
    GeneratedPathAt (fullFactorDecayLaw index) start target →
      List (GeneratedFactorAction index)
  | .nil => []
  | .snoc prior channel =>
      actionPayloads prior ++ [generatedFactorAction channel]

def actionCount {index : Nat}
    {start target : EffectiveSplitAt index}
    (path : GeneratedPathAt (fullFactorDecayLaw index) start target) : Nat :=
  (actionPayloads path).length

theorem actionPayloads_snoc {index : Nat}
    {start state : EffectiveSplitAt index}
    (prior : GeneratedPathAt (fullFactorDecayLaw index) start state)
    (channel : FactorDecayChannelAt state) :
    actionPayloads (prior.snoc channel) =
      actionPayloads prior ++ [generatedFactorAction channel] :=
  rfl

/-- Every dependent edge payload reads the canonical operational receipt and
its Fock effect; membership in a derived list adds no authority. -/
theorem generatedFactorAction_read
    {index : Nat} (payload : GeneratedFactorAction index) :
    payload.2.2.operational = generateChannelReceipt payload.2.1 ∧
      HEq payload.2.2.fock
        (generateFactorDecayFockTrace payload.2.1
          (generateChannelReceipt payload.2.1)) :=
  ⟨payload.2.2.operational_eq, payload.2.2.fock_eq⟩

/-- The action history is bound to the exact occurrence which generated the
fixed target.  Terminal readout is intentionally absent. -/
structure RootedActionHistoryAt
    {Occurrence : Type} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index)
    {target : EffectiveSplitAt index}
    (sourcePath : GeneratedPathAt (fullFactorDecayLaw index)
      (canonicalSplit index indexInRange) target) : Type where
  private mk ::
  source : RootGeneratedExactOccurrenceOperationalFactorDecayAt
    rootOccurrence index indexInRange
  source_eq : source =
    CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
      rootOccurrence index indexInRange
  operationalPath : OperationalFactorDecayPathReceiptAt sourcePath
  operationalPath_eq : operationalPath = source.pathReceipt sourcePath

def generateRootedActionHistory
    {Occurrence : Type} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index)
    {target : EffectiveSplitAt index}
    (sourcePath : GeneratedPathAt (fullFactorDecayLaw index)
      (canonicalSplit index indexInRange) target) :
    RootedActionHistoryAt rootOccurrence index indexInRange sourcePath := by
  let source :=
    CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
      rootOccurrence index indexInRange
  exact
    { source := source
      source_eq := rfl
      operationalPath := source.pathReceipt sourcePath
      operationalPath_eq := rfl }

namespace RootedActionHistoryAt

theorem occurrenceRoot
    {Occurrence : Type} {rootOccurrence : Occurrence}
    {index : Nat} {indexInRange : 1 ≤ index}
    {target : EffectiveSplitAt index}
    {sourcePath : GeneratedPathAt (fullFactorDecayLaw index)
      (canonicalSplit index indexInRange) target}
    (history : RootedActionHistoryAt rootOccurrence index indexInRange sourcePath) :
    history.source.occurrence.root.rootOccurrence = rootOccurrence :=
  history.source.occurrenceRoot

def actionPayloads
    {Occurrence : Type} {rootOccurrence : Occurrence}
    {index : Nat} {indexInRange : 1 ≤ index}
    {target : EffectiveSplitAt index}
    {sourcePath : GeneratedPathAt (fullFactorDecayLaw index)
      (canonicalSplit index indexInRange) target}
    (_history : RootedActionHistoryAt rootOccurrence index indexInRange sourcePath) :
    List (GeneratedFactorAction index) :=
  ParticleWaveFockPrimePairActualityActionHistory.actionPayloads sourcePath

def actionCount
    {Occurrence : Type} {rootOccurrence : Occurrence}
    {index : Nat} {indexInRange : 1 ≤ index}
    {target : EffectiveSplitAt index}
    {sourcePath : GeneratedPathAt (fullFactorDecayLaw index)
      (canonicalSplit index indexInRange) target}
    (history : RootedActionHistoryAt rootOccurrence index indexInRange sourcePath) : Nat :=
  history.actionPayloads.length

theorem actionPayload_mem_generated
    {Occurrence : Type} {rootOccurrence : Occurrence}
    {index : Nat} {indexInRange : 1 ≤ index}
    {target : EffectiveSplitAt index}
    {sourcePath : GeneratedPathAt (fullFactorDecayLaw index)
      (canonicalSplit index indexInRange) target}
    (history : RootedActionHistoryAt rootOccurrence index indexInRange sourcePath)
    (payload : GeneratedFactorAction index)
    (payloadMem : payload ∈ history.actionPayloads) :
    payload ∈ history.actionPayloads ∧
      payload.2.2.operational = generateChannelReceipt payload.2.1 ∧
      HEq payload.2.2.fock
        (generateFactorDecayFockTrace payload.2.1
          (generateChannelReceipt payload.2.1)) :=
  ⟨payloadMem, generatedFactorAction_read payload⟩

end RootedActionHistoryAt

end
end ParticleWaveFockPrimePairActualityActionHistory
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
