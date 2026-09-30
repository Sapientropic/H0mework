import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.SelectionEquations
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Consumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Joint.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

/-- A transporter between two actual source programme outputs at one exact
support. Its inputs are supplied by the joint programme presentation. -/
structure NormalWriteFrame {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    (n : MotherNetworkOrigin.Presentation N G)
    {old : Transitions original} {formed : Transitions generated}
    (rows : LedgerWriteRowSourceAt original old.exactTransitionAt)
    (output : LedgerWriteRowSourceAt generated formed.exactTransitionAt)
    (point : Point original) (current : W.Current)
    (event : generated.law.EventAt current (n.support point.2.1)) where
  row : {target : N.Support} → (a : OpenResponsibilityAt N point.2.1) →
    (b : OpenResponsibilityAt N target) →
    GeneratedLedgerWriteRowAt rows point.2 a b ≃
      GeneratedLedgerWriteRowAt output ⟨n.support point.2.1, event⟩ (n.ledger point.2.1 a) (n.ledger target b)
  row_evolution : ∀ {target : N.Support} (a : OpenResponsibilityAt N point.2.1)
    (b : OpenResponsibilityAt N target) (value : GeneratedLedgerWriteRowAt rows point.2 a b),
    (row a b value).evolution = n.mapRow value.evolution
  remainder : {target : N.Support} → GeneratedLedgerTransportedRemainderAt rows point.2 ⟨target⟩ →
    GeneratedLedgerTransportedRemainderAt output ⟨n.support point.2.1, event⟩ ⟨n.support target⟩
  remainder_evolution : ∀ {target : N.Support} (value : GeneratedLedgerTransportedRemainderAt rows point.2 ⟨target⟩),
    (remainder value).evolution = n.wholeLedgerEquiv point.2.1 target value.evolution

namespace NormalWriteFrame
variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G}
    {old : Transitions original} {formed : Transitions generated}
    {rows : LedgerWriteRowSourceAt original old.exactTransitionAt}
    {output : LedgerWriteRowSourceAt generated formed.exactTransitionAt}
    {point : Point original} {current : W.Current}
    {event : generated.law.EventAt current (n.support point.2.1)}
    (frame : NormalWriteFrame n rows output point current event)

def finiteRows {target : N.Support} (inventory : FiniteGeneratedLedgerWriteRowsAt rows point.2 ⟨target⟩) :
    FiniteGeneratedLedgerWriteRowsAt output ⟨n.support point.2.1, event⟩ ⟨n.support target⟩ where
  size := inventory.size
  sourceEntryAt := fun i => n.ledger point.2.1 (inventory.sourceEntryAt i)
  targetEntryAt := fun i => n.ledger target (inventory.targetEntryAt i)
  rowAt := fun i => frame.row _ _ (inventory.rowAt i)

def identityCoverage {inventory : FiniteGeneratedLedgerWriteRowsAt rows point.2 ⟨point.2.1⟩}
    (coverage : LedgerIdentityRemainderCoverageAt inventory) : LedgerIdentityRemainderCoverageAt (frame.finiteRows inventory) where
  destinationIndex := MotherNetworkOrigin.mapSelection (n.ledger point.2.1) inventory.sourceEntryAt coverage.destinationIndex
  originIndex := MotherNetworkOrigin.mapSelection (n.ledger point.2.1) inventory.targetEntryAt coverage.originIndex

def remainderCoverage {target : N.Support} {inventory : FiniteGeneratedLedgerWriteRowsAt rows point.2 ⟨target⟩}
    (coverage : LedgerTransportedRemainderCoverageAt inventory) : LedgerTransportedRemainderCoverageAt (frame.finiteRows inventory) where
  destinationIndex := MotherNetworkOrigin.mapSelection (n.ledger point.2.1) inventory.sourceEntryAt coverage.destinationIndex
  originIndex := MotherNetworkOrigin.mapSelection (n.ledger target) inventory.targetEntryAt coverage.originIndex

def completeCoverage {target : N.Support} {inventory : FiniteGeneratedLedgerWriteRowsAt rows point.2 ⟨target⟩}
    (coverage : LedgerCompleteFiniteCoverageAt inventory) : LedgerCompleteFiniteCoverageAt (frame.finiteRows inventory) where
  destinationIndex := fun entry => coverage.destinationIndex ((n.ledger point.2.1).symm entry)
  originIndex := fun entry => coverage.originIndex ((n.ledger target).symm entry)
  destination_sound := fun entry => (congrArg (n.ledger point.2.1) (coverage.destination_sound ((n.ledger point.2.1).symm entry))).trans ((n.ledger point.2.1).apply_symm_apply entry)
  origin_sound := fun entry => (congrArg (n.ledger target) (coverage.origin_sound ((n.ledger target).symm entry))).trans ((n.ledger target).apply_symm_apply entry)

def writePatch {target : CompleteLiveLedgerAt N} (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 target) :
    FiniteGeneratedLedgerWritePatchAt output ⟨n.support point.2.1, event⟩ ⟨n.support target.support⟩ := by
  cases patch with
  | identityRemainder inventory coverage => exact .identityRemainder (frame.finiteRows inventory) (frame.identityCoverage coverage)
  | complete inventory coverage => exact .complete (frame.finiteRows inventory) (frame.completeCoverage coverage)
  | transportedRemainder inventory coverage rest => exact .transportedRemainder (frame.finiteRows inventory) (frame.remainderCoverage coverage) (frame.remainder rest)

end NormalWriteFrame
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
