import H0mework.Physics.MotherProgrammesFormation.Declarations.UnitSource.Input

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherUnitSource

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open CofinalHistorySettlementFace CofinalFaithfulSettlementFace RootedAccountedUnfolding
open NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History
open MotherClosedRestrictions

noncomputable section

abbrev Generator := ConductorHistoryGenerator
abbrev Carrier := ConductorHistoryCarrier
abbrev Event := MotherHistoryFormation.Event

local instance instEncodableRootedAccountedUnfoldingNat_scratch : Encodable (RootedAccountedUnfolding ℕ) := MotherEvaluatorTrees.shapeCodec

def shapeCode (shape : RootedAccountedUnfolding ℕ) : ℕ := Encodable.encode shape

def shapeFromCode (code : ℕ) : RootedAccountedUnfolding ℕ :=
  (Encodable.decode code).getD (.zero 0)

theorem shape_recovered (shape : RootedAccountedUnfolding ℕ) :
    shapeFromCode (shapeCode shape) = shape := by
  simp only [shapeFromCode, shapeCode, Encodable.encodek, Option.getD_some]

def readValue (law : MotherPointwiseLaws.Law) (current : Current) (body : Body) :
    MotherStreamLaws.Stream :=
  lastStream (MotherPointwiseLaws.eval law (inputSamples (current, body)))

def shapeAt (law : MotherPointwiseLaws.Law) (current : Current) (kind : Fin 4) :
    RootedAccountedUnfolding ℕ :=
  shapeFromCode (Nat.floor (readValue law current (.inl kind) 0))

def rootExposureAt (law : MotherPointwiseLaws.Law) {current : Current}
    (_occurrence : OccurrenceAt current) : RootedAccountedUnfolding (OccurrenceAt current) :=
  (shapeAt law current 0).map (fun _ => sourceOccurrence current)

theorem rootExposure_root (law : MotherPointwiseLaws.Law) {current : Current}
    (occurrence : OccurrenceAt current) : (rootExposureAt law occurrence).root = occurrence := by
  exact (root_map (fun _ : ℕ => sourceOccurrence current)
    (shapeAt law current 0)).trans (occurrence_unique occurrence).symm

def seedAt (law : MotherPointwiseLaws.Law) {current : Current} (_occurrence : OccurrenceAt current) :
    RootedAccountedUnfolding Event :=
  MotherHistoryFormation.treeAtCode (Nat.floor (readValue law current (.inl 1) 0))

def continuationAt (law : MotherPointwiseLaws.Law) {current : Current}
    (_occurrence : OccurrenceAt current) :
    RootedAccountedUnfolding (Event → RootedAccountedUnfolding Event) :=
  (shapeAt law current 2).map (fun node event => MotherHistoryFormation.treeAtCode
    (Nat.floor (readValue law current (.inr (.inl (node, event))) 0)))

def evaluatorAt (law : MotherPointwiseLaws.Law) {current : Current}
    (_occurrence : OccurrenceAt current) : RootedAccountedUnfolding (Generator → Carrier) :=
  (shapeAt law current 3).map (fun node generator test scale =>
    MotherEvaluatorTreeFunctions.complexRead
      (readValue law current (.inr (.inr (node, generator, test, scale)))))

/-- The only parameter is one law from the fixed mother factory. -/
def historyLaw (law : MotherPointwiseLaws.Law) :
    SourceNativeCofinalHistoryMaterialLaw CanonicalUnitArithmeticRoot.ledgerSource :=
  .create Generator (rootExposureAt law) (rootExposure_root law) (seedAt law) (continuationAt law)

def materialLaw (law : MotherPointwiseLaws.Law) :
    SourceNativeCofinalFaithfulMaterialLaw CanonicalUnitArithmeticRoot.ledgerSource Carrier :=
  .create (historyLaw law) (evaluatorAt law)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherUnitSource
