import H0mework.Physics.MotherProgrammesFormation.Declarations.PhysicalSource.Input

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open CofinalHistorySettlementFace CofinalFaithfulSettlementFace RootedAccountedUnfolding
open MotherClosedRestrictions MotherDurationExposure

noncomputable section

abbrev Generator := MotherUnitSource.Generator
abbrev Carrier := MotherUnitSource.Carrier
abbrev Event := MotherHistoryFormation.Event

def readValue (law : MotherPhysicalLaws.Law) (current : Current) (duration : Duration) (body : Body) :
    MotherStreamLaws.Stream :=
  lastStream (MotherPhysicalLaws.eval law (inputAt (current, duration, body)))

def shapeAt (law : MotherPhysicalLaws.Law) (current : Current) (duration : Duration) (kind : Fin 4) :
    RootedAccountedUnfolding ℕ :=
  MotherUnitSource.shapeFromCode (Nat.floor (readValue law current duration (.inr (.inl kind)) 0))

def branchOccurrence (law : MotherPhysicalLaws.Law) (current : Current) (duration : Duration)
    (node : ℕ) : OccurrenceAt current :=
  occurrenceOf current (durationRead (readValue law current duration (.inl node) 0))

def rootExposureAt (law : MotherPhysicalLaws.Law) {current : Current}
    (occurrence : OccurrenceAt current) : RootedAccountedUnfolding (OccurrenceAt current) :=
  .occur occurrence (((shapeAt law current (durationOf occurrence) 0).map
    (branchOccurrence law current (durationOf occurrence))).branches)

theorem rootExposure_root (law : MotherPhysicalLaws.Law) {current : Current}
    (occurrence : OccurrenceAt current) : (rootExposureAt law occurrence).root = occurrence := rfl

def seedAt (law : MotherPhysicalLaws.Law) {current : Current} (occurrence : OccurrenceAt current) :
    RootedAccountedUnfolding Event :=
  MotherHistoryFormation.treeAtCode (Nat.floor (readValue law current (durationOf occurrence) (.inr (.inl 1)) 0))

def continuationAt (law : MotherPhysicalLaws.Law) {current : Current}
    (occurrence : OccurrenceAt current) :
    RootedAccountedUnfolding (Event → RootedAccountedUnfolding Event) :=
  (shapeAt law current (durationOf occurrence) 2).map (fun node event => MotherHistoryFormation.treeAtCode
    (Nat.floor (readValue law current (durationOf occurrence) (.inr (.inr (.inl (node, event)))) 0)))

def evaluatorAt (law : MotherPhysicalLaws.Law) {current : Current}
    (occurrence : OccurrenceAt current) : RootedAccountedUnfolding (Generator → Carrier) :=
  (shapeAt law current (durationOf occurrence) 3).map (fun node generator test scale =>
    MotherEvaluatorTreeFunctions.complexRead
      (readValue law current (durationOf occurrence) (.inr (.inr (.inr (node, generator, test, scale))))))

/-- All four source fields use the same higher law, without target callbacks. -/
def historyLaw (law : MotherPhysicalLaws.Law) : SourceNativeCofinalHistoryMaterialLaw ledgerSource :=
  .create Generator (rootExposureAt law) (rootExposure_root law) (seedAt law) (continuationAt law)

def materialLaw (law : MotherPhysicalLaws.Law) : SourceNativeCofinalFaithfulMaterialLaw ledgerSource Carrier :=
  .create (historyLaw law) (evaluatorAt law)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource
