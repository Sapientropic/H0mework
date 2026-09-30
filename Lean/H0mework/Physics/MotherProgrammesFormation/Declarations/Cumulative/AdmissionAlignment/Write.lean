import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.Terminal

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

theorem mapSelection_injective {A B : Type} {size : Nat} (e : A ≃ B) (entryAt : Fin size → A) :
    Function.Injective (MotherNetworkOrigin.mapSelection e entryAt) := by
  intro first last same
  funext entry
  apply Option.map_injective (f := Subtype.val) Subtype.val_injective
  exact (MotherNetworkOrigin.mapSelection_index e entryAt first entry).symm.trans
    ((congrArg (fun selection => (selection (e entry)).map Subtype.val) same).trans
      (MotherNetworkOrigin.mapSelection_index e entryAt last entry))

def finiteRowsDataEquiv {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (operations : Transitions source)
    (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (point : Point source) (target : N.Support) :
    FiniteGeneratedLedgerWriteRowsAt rows point.2 ⟨target⟩ ≃
      (Σ size : Nat, Fin size → Σ first : OpenResponsibilityAt N point.2.1,
        Σ last : OpenResponsibilityAt N target, GeneratedLedgerWriteRowAt rows point.2 first last) where
  toFun := fun value => ⟨value.size, fun index => ⟨value.sourceEntryAt index, value.targetEntryAt index, value.rowAt index⟩⟩
  invFun := fun value => ⟨value.1, fun index => (value.2 index).1,
    fun index => (value.2 index).2.1, fun index => (value.2 index).2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

namespace NormalFrame

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G}
    {old : Transitions original} {formed : Transitions generated}
    {rows : LedgerWriteRowSourceAt original old.exactTransitionAt}
    {output : LedgerWriteRowSourceAt generated formed.exactTransitionAt}
    {point : Point original} {current : W.Current}
    {event : generated.law.EventAt current (n.support point.2.1)}
    (frame : NormalWriteFrame n rows output point current event)

def finiteRowsEquiv (target : N.Support) :
    FiniteGeneratedLedgerWriteRowsAt rows point.2 ⟨target⟩ ≃
      FiniteGeneratedLedgerWriteRowsAt output ⟨n.support point.2.1, event⟩ ⟨n.support target⟩ :=
  (finiteRowsDataEquiv old rows point target).trans
    ((Equiv.sigmaCongrRight (fun _ => Equiv.piCongrRight (fun _ =>
      Equiv.sigmaCongr (n.ledger point.2.1) (fun first =>
        Equiv.sigmaCongr (n.ledger target) (fun last => frame.row first last))))).trans
      (finiteRowsDataEquiv formed output ⟨current, n.support point.2.1, event⟩ (n.support target)).symm)

theorem finiteRows_injective (target : N.Support) :
    Function.Injective (frame.finiteRows (target := target)) :=
  (finiteRowsEquiv frame target).injective

theorem identityCoverage_injective
    (inventory : FiniteGeneratedLedgerWriteRowsAt rows point.2 ⟨point.2.1⟩) :
    Function.Injective (frame.identityCoverage (inventory := inventory)) := by
  intro first last same
  have destination := mapSelection_injective (n.ledger point.2.1) inventory.sourceEntryAt
    (congrArg LedgerIdentityRemainderCoverageAt.destinationIndex same)
  have origin := mapSelection_injective (n.ledger point.2.1) inventory.targetEntryAt
    (congrArg LedgerIdentityRemainderCoverageAt.originIndex same)
  cases first
  cases last
  cases destination
  cases origin
  rfl

theorem remainderCoverage_injective {target : N.Support}
    (inventory : FiniteGeneratedLedgerWriteRowsAt rows point.2 ⟨target⟩) :
    Function.Injective (frame.remainderCoverage (inventory := inventory)) := by
  intro first last same
  have destination := mapSelection_injective (n.ledger point.2.1) inventory.sourceEntryAt
    (congrArg LedgerTransportedRemainderCoverageAt.destinationIndex same)
  have origin := mapSelection_injective (n.ledger target) inventory.targetEntryAt
    (congrArg LedgerTransportedRemainderCoverageAt.originIndex same)
  cases first
  cases last
  cases destination
  cases origin
  rfl

theorem completeCoverage_injective {target : N.Support}
    (inventory : FiniteGeneratedLedgerWriteRowsAt rows point.2 ⟨target⟩) :
    Function.Injective (frame.completeCoverage (inventory := inventory)) := by
  intro first last same
  have destination : first.destinationIndex = last.destinationIndex := by
    funext entry
    have sampled := congrFun (congrArg LedgerCompleteFiniteCoverageAt.destinationIndex same) (n.ledger point.2.1 entry)
    change first.destinationIndex ((n.ledger point.2.1).symm (n.ledger point.2.1 entry)) =
      last.destinationIndex ((n.ledger point.2.1).symm (n.ledger point.2.1 entry)) at sampled
    exact (congrArg first.destinationIndex ((n.ledger point.2.1).symm_apply_apply entry)).symm.trans
      (sampled.trans (congrArg last.destinationIndex ((n.ledger point.2.1).symm_apply_apply entry)))
  have origin : first.originIndex = last.originIndex := by
    funext entry
    have sampled := congrFun (congrArg LedgerCompleteFiniteCoverageAt.originIndex same) (n.ledger target entry)
    change first.originIndex ((n.ledger target).symm (n.ledger target entry)) =
      last.originIndex ((n.ledger target).symm (n.ledger target entry)) at sampled
    simpa only [Equiv.symm_apply_apply] using sampled
  cases first
  cases last
  cases destination
  cases origin
  rfl

theorem writePatch_injective {target : CompleteLiveLedgerAt N} :
    Function.Injective (frame.writePatch (target := target)) := by
  intro first last same
  cases first <;> cases last <;> dsimp only [NormalWriteFrame.writePatch] at same
  all_goals first | cases same | skip
  case identityRemainder.identityRemainder first firstCoverage last lastCoverage =>
    have parts := FiniteGeneratedLedgerWritePatchAt.identityRemainder.inj same
    have rowsSame := finiteRows_injective frame point.2.1 parts.1
    cases rowsSame
    have coverageSame := identityCoverage_injective frame first (eq_of_heq parts.2)
    cases coverageSame
    rfl
  case complete.complete first firstCoverage last lastCoverage =>
    have parts := FiniteGeneratedLedgerWritePatchAt.complete.inj same
    have rowsSame := finiteRows_injective frame target.support parts.1
    cases rowsSame
    have coverageSame := completeCoverage_injective frame first (eq_of_heq parts.2)
    cases coverageSame
    rfl
  case transportedRemainder.transportedRemainder first firstCoverage firstRest last lastCoverage lastRest =>
    have parts := FiniteGeneratedLedgerWritePatchAt.transportedRemainder.inj same
    have rowsSame := finiteRows_injective frame target.support parts.1
    cases rowsSame
    have coverageSame := remainderCoverage_injective frame first (eq_of_heq parts.2.1)
    cases coverageSame
    have restSame := remainderSeal_eq firstRest lastRest
    cases restSame
    rfl

end NormalFrame
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
