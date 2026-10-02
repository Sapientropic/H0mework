import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Fold
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Whole

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

structure WriteFrame {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    (n : MotherNetworkOrigin.Presentation N G)
    {old : Transitions original} {formed : Transitions generated}
    (rows : LedgerWriteRowSourceAt original old.exactTransitionAt)
    (output : LedgerWriteRowSourceAt generated formed.exactTransitionAt)
    (point : Point original) (newPoint : Point generated)
    (same : newPoint.2.1 = n.support point.2.1) where
  row : {target : N.Support} → (a : OpenResponsibilityAt N point.2.1) →
    (b : OpenResponsibilityAt N target) → GeneratedLedgerWriteRowAt rows point.2 a b ≃
      GeneratedLedgerWriteRowAt output newPoint.2
        ((Equiv.cast (congrArg (OpenResponsibilityAt G) same.symm)) (n.ledger point.2.1 a)) (n.ledger target b)
  row_evolution : ∀ {target : N.Support} (a : OpenResponsibilityAt N point.2.1)
    (b : OpenResponsibilityAt N target) (value : GeneratedLedgerWriteRowAt rows point.2 a b),
    (row a b value).evolution = castRowSource G same.symm (n.ledger point.2.1 a) (n.ledger target b) (n.mapRow value.evolution)
  remainder : {target : N.Support} → GeneratedLedgerTransportedRemainderAt rows point.2 ⟨target⟩ →
    GeneratedLedgerTransportedRemainderAt output newPoint.2 ⟨n.support target⟩
  remainder_evolution : ∀ {target : N.Support} (value : GeneratedLedgerTransportedRemainderAt rows point.2 ⟨target⟩),
    (remainder value).evolution = (Equiv.cast (congrArg
      (fun support => LedgerWriteEvolutionAt G ⟨support⟩ ⟨n.support target⟩) same.symm))
        (n.wholeLedgerEquiv point.2.1 target value.evolution)

namespace WriteFrame
variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G}
    {old : Transitions original} {formed : Transitions generated}
    {rows : LedgerWriteRowSourceAt original old.exactTransitionAt}
    {output : LedgerWriteRowSourceAt generated formed.exactTransitionAt}
    {point : Point original} {newPoint : Point generated}
    {same : newPoint.2.1 = n.support point.2.1}
    (frame : WriteFrame n rows output point newPoint same)

def writePatch {target : CompleteLiveLedgerAt N} (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 target) :
    FiniteGeneratedLedgerWritePatchAt output newPoint.2 ⟨n.support target.support⟩ := by
  rcases newPoint with ⟨current, support, event⟩
  change support = n.support point.2.1 at same
  cases same
  exact (show NormalWriteFrame n rows output point current event from
    { row := frame.row, row_evolution := frame.row_evolution,
      remainder := frame.remainder, remainder_evolution := frame.remainder_evolution }).writePatch patch

theorem writePatch_fold {target : CompleteLiveLedgerAt N} (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 target) :
    (frame.writePatch patch).toLedgerWriteEvolution =
      (Equiv.cast (congrArg (fun support => LedgerWriteEvolutionAt G ⟨support⟩ ⟨n.support target.support⟩) same.symm))
        (n.wholeLedgerEquiv point.2.1 target.support patch.toLedgerWriteEvolution) := by
  rcases newPoint with ⟨current, support, event⟩
  change support = n.support point.2.1 at same
  cases same
  exact (show NormalWriteFrame n rows output point current event from
    { row := frame.row, row_evolution := frame.row_evolution,
      remainder := frame.remainder, remainder_evolution := frame.remainder_evolution }).writePatch_fold patch

end WriteFrame

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    {old : Transitions original} {formed : Transitions generated}
    (q : TransitionPresentation (transportedTransitions p old) formed)
    {rows : LedgerWriteRowSourceAt original old.exactTransitionAt}
    {output : LedgerWriteRowSourceAt generated formed.exactTransitionAt}
    (r : WritePresentation (sourceWrite p q rows) output)

def writeFrame (point : Point original) :
    WriteFrame n rows output point (pointEquiv p point) (p.support_eq point.1 point.2) where
  row := fun {target} a b => completeRowSeal p q r ⟨point.1, point.2, target, a, b⟩
  row_evolution := by
    intro target a b value
    let e := rowOutputEquiv p q ⟨point.1, point.2, target, a, b⟩
    have h := completeRow_payload p q r ⟨point.1, point.2, target, a, b⟩ value
    exact congrArg Prod.fst ((e.apply_symm_apply _).symm.trans (congrArg e h))
  remainder := fun {target} value => completeRemainder p q r point ⟨target⟩ value
  remainder_evolution := by
    intro target value
    let e := remainderOutputEquiv p q (point, target)
    have h := completeRemainder_payload p q r point ⟨target⟩ value
    exact (congrArg Sigma.fst ((e.apply_symm_apply _).symm.trans (congrArg e h))).trans
      (remainderOutput_whole p q (point, target) ⟨value.evolution, value.exact⟩)

def writePatch (point : Point original) {target : CompleteLiveLedgerAt N}
    (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 target) :
    FiniteGeneratedLedgerWritePatchAt output (pointEquiv p point).2 ⟨n.support target.support⟩ :=
  (writeFrame p q r point).writePatch patch

theorem writePatch_fold (point : Point original) {target : CompleteLiveLedgerAt N}
    (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 target) :
    (writePatch p q r point patch).toLedgerWriteEvolution = wholeEquiv p point target.support patch.toLedgerWriteEvolution :=
  (writeFrame p q r point).writePatch_fold patch

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
