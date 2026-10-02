import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Branch

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

private theorem event_cast_support {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (source : SourceNativeSource N V) {a b : V.Current} (same : a = b)
    (event : source.toRootSource.actual.OccurrenceAt a) :
    ((Equiv.cast (congrArg source.toRootSource.actual.OccurrenceAt same)) event).1 = event.1 := by
  cases same
  rfl

private theorem castWhole_both (N : WorldRelationNetwork.{0}) {s s' t t' : N.Support}
    (hs : s = s') (ht : t = t') (whole : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩) :
    (Equiv.cast (congrArg₂ (fun a b => LedgerWriteEvolutionAt N ⟨a⟩ ⟨b⟩) hs ht)) whole =
      (Equiv.cast (congrArg (fun b => LedgerWriteEvolutionAt N ⟨s'⟩ ⟨b⟩) ht))
        ((Equiv.cast (congrArg (fun a => LedgerWriteEvolutionAt N ⟨a⟩ ⟨t⟩) hs)) whole) := by
  cases hs; cases ht; rfl

def castPatchTarget {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (operations : Transitions source) (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (point : Point source) {left right : N.Support} (same : left = right)
    (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨left⟩) :
    FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨right⟩ :=
  (Equiv.cast (congrArg (fun support => FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨support⟩) same)) patch

theorem castPatchTarget_fold {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (operations : Transitions source) (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (point : Point source) {left right : N.Support} (same : left = right)
    (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨left⟩) :
    (castPatchTarget operations rows point same patch).toLedgerWriteEvolution =
      (Equiv.cast (congrArg (fun support => LedgerWriteEvolutionAt N ⟨point.2.1⟩ ⟨support⟩) same)) patch.toLedgerWriteEvolution := by
  cases same
  rfl

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    {old : Transitions original} {formed : Transitions generated}
    (q : TransitionPresentation (transportedTransitions p old) formed)
    {rows : LedgerWriteRowSourceAt original old.exactTransitionAt}
    {output : LedgerWriteRowSourceAt generated formed.exactTransitionAt}
    (r : WritePresentation (sourceWrite p q rows) output)
    {oldTerminal : LedgerTerminalRowSourceAt original} {terminal : LedgerTerminalRowSourceAt generated}
    (s : TerminalPresentation (transportedTerminal p oldTerminal) terminal)

def writePatchWithTarget (point : Point original) (target : N.Support) (newTarget : G.Support)
    (same : newTarget = n.support target) (whole : LedgerWriteEvolutionAt N ⟨point.2.1⟩ ⟨target⟩)
    (patch : {patch : FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨target⟩ // patch.toLedgerWriteEvolution = whole}) :
    {patch : FiniteGeneratedLedgerWritePatchAt output (pointEquiv p point).2 ⟨newTarget⟩ //
      patch.toLedgerWriteEvolution = (Equiv.cast (congrArg₂ (fun a b => LedgerWriteEvolutionAt G ⟨a⟩ ⟨b⟩)
        (p.support_eq point.1 point.2).symm same.symm)) (n.wholeLedgerEquiv point.2.1 target whole)} := by
  refine ⟨castPatchTarget formed output (pointEquiv p point) same.symm (writePatch p q r point patch.val), ?_⟩
  exact (castPatchTarget_fold formed output (pointEquiv p point) same.symm (writePatch p q r point patch.val)).trans
    ((congrArg (Equiv.cast (congrArg (fun b => LedgerWriteEvolutionAt G ⟨(pointEquiv p point).2.1⟩ ⟨b⟩) same.symm))
      ((writePatch_fold p q r point patch.val).trans (congrArg (wholeEquiv p point target) patch.property))).trans
        (castWhole_both G (p.support_eq point.1 point.2).symm same.symm (n.wholeLedgerEquiv point.2.1 target whole)).symm)

def transportBodyPatch (point : Point original) (branch : EvolutionAt V point.1)
    (target : TargetFor original branch) (whole : LedgerFor original point.2 branch target)
    (patch : PatchFor old rows oldTerminal point branch target whole) :
    PatchFor formed output terminal (pointEquiv p point) (v.evolution point.1 branch)
      (targetEquiv p branch target) (ledgerForEquiv p point.2 branch target whole) := by
  cases branch with
  | nativeWrite write =>
      have targetSupport := (event_cast_support generated (v.native_eq point.1 write).symm
        (p.event (V.nativeTarget write) target)).trans (p.support_eq (V.nativeTarget write) target)
      exact writePatchWithTarget p q r point target.1 _ targetSupport whole patch
  | relationWrite write =>
      have targetSupport := (event_cast_support generated (v.relation_eq point.1 write).symm
        (p.event (V.relationTarget write) target)).trans (p.support_eq (V.relationTarget write) target)
      exact writePatchWithTarget p q r point target.1 _ targetSupport whole patch
  | continuedTransport write =>
      have targetSupport := (event_cast_support generated (v.continued_eq point.1 write).symm
        (p.event (V.continuedTarget write) target)).trans (p.support_eq (V.continuedTarget write) target)
      exact writePatchWithTarget p q r point target.1 _ targetSupport whole patch
  | borromeanRedirect write =>
      have targetSupport := (event_cast_support generated (v.redirect_eq point.1 write).symm
        (p.event (V.redirectTarget write) target)).trans (p.support_eq (V.redirectTarget write) target)
      exact writePatchWithTarget p q r point target.1 _ targetSupport whole patch
  | faithfulTerminal =>
      exact ⟨terminalPatch p s point patch.val,
        (terminalPatch_fold p s point patch.val).trans (congrArg (terminalEquiv p point) patch.property)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
