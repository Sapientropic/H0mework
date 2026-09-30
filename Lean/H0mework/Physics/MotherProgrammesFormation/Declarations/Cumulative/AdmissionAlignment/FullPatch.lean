import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.Write

/-! The existing full source patch transporter preserves every stored datum.
Its inverse on its exact image supports recovery in the original dependent
indices, without asserting equality between different source types. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

private theorem event_cast_support {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) {first last : V.Current} (same : first = last)
    (event : source.toRootSource.actual.OccurrenceAt first) :
    (Equiv.cast (congrArg source.toRootSource.actual.OccurrenceAt same) event).1 = event.1 := by
  cases same
  rfl

theorem frame_writePatch_injective
    {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G}
    {old : Transitions original} {formed : Transitions generated}
    {rows : LedgerWriteRowSourceAt original old.exactTransitionAt}
    {output : LedgerWriteRowSourceAt generated formed.exactTransitionAt}
    {point : Point original} {newPoint : Point generated}
    {same : newPoint.2.1 = n.support point.2.1}
    (frame : WriteFrame n rows output point newPoint same)
    {target : CompleteLiveLedgerAt N} : Function.Injective (frame.writePatch (target := target)) := by
  rcases newPoint with ⟨current, support, event⟩
  change support = n.support point.2.1 at same
  cases same
  exact NormalFrame.writePatch_injective (show NormalWriteFrame n rows output point current event from
    { row := frame.row, row_evolution := frame.row_evolution,
      remainder := frame.remainder, remainder_evolution := frame.remainder_evolution })

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
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

theorem writePatch_injective (point : Point original) {target : CompleteLiveLedgerAt N} :
    Function.Injective (writePatch p q r point (target := target)) :=
  frame_writePatch_injective (writeFrame p q r point)

theorem writePatchWithTarget_injective (point : Point original) (target : N.Support) (newTarget : G.Support)
    (same : newTarget = n.support target) (whole : LedgerWriteEvolutionAt N ⟨point.2.1⟩ ⟨target⟩) :
    Function.Injective (writePatchWithTarget p q r point target newTarget same whole) := by
  intro first last equal
  apply Subtype.ext
  apply writePatch_injective p q r point
  exact (Equiv.cast (congrArg
    (fun support => FiniteGeneratedLedgerWritePatchAt output (pointEquiv p point).2 ⟨support⟩) same.symm)).injective
      (congrArg Subtype.val equal)

theorem transportBodyPatch_injective (point : Point original) (branch : EvolutionAt V point.1)
    (target : TargetFor original branch) (whole : LedgerFor original point.2 branch target) :
    Function.Injective (transportBodyPatch p q r s point branch target whole) := by
  cases branch with
  | nativeWrite write =>
      have same := (event_cast_support generated (v.native_eq point.1 write).symm
        (p.event (V.nativeTarget write) target)).trans (p.support_eq (V.nativeTarget write) target)
      exact writePatchWithTarget_injective p q r point target.1 _ same whole
  | relationWrite write =>
      have same := (event_cast_support generated (v.relation_eq point.1 write).symm
        (p.event (V.relationTarget write) target)).trans (p.support_eq (V.relationTarget write) target)
      exact writePatchWithTarget_injective p q r point target.1 _ same whole
  | continuedTransport write =>
      have same := (event_cast_support generated (v.continued_eq point.1 write).symm
        (p.event (V.continuedTarget write) target)).trans (p.support_eq (V.continuedTarget write) target)
      exact writePatchWithTarget_injective p q r point target.1 _ same whole
  | borromeanRedirect write =>
      have same := (event_cast_support generated (v.redirect_eq point.1 write).symm
        (p.event (V.redirectTarget write) target)).trans (p.support_eq (V.redirectTarget write) target)
      exact writePatchWithTarget_injective p q r point target.1 _ same whole
  | faithfulTerminal value =>
      intro first last equal
      apply Subtype.ext
      exact (terminalPatchEquiv p s point).injective (congrArg Subtype.val equal)

theorem castBodyPatch_injective
    {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (operations : Transitions source) (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (terminal : LedgerTerminalRowSourceAt source) (point : Point source)
    {first last : EvolutionAt V point.1} (same : first = last)
    (body : Sigma (LedgerFor source point.2 first)) :
    Function.Injective (castBodyPatch operations rows terminal point same body) := by
  cases same
  exact fun _ _ equal => equal

theorem fullPatch_injective (point : Point original)
    (compiled : SourceNativeLedgerEvolutionAt original point.2) :
    Function.Injective (fullPatch p q r s point compiled) := by
  let body := bodyOfCompilation point compiled
  let newBody : Sigma (LedgerFor generated (pointEquiv p point).2
      (v.evolution point.1 (original.toRootSource.actual.compile point.2))) :=
    ⟨targetEquiv p _ body.1, ledgerForEquiv p point.2 _ body.1 body.2⟩
  let actualBody := (Equiv.cast (congrArg
    (fun branch => Sigma (LedgerFor generated (pointEquiv p point).2 branch))
      (p.compile_eq point.1 point.2).symm)) newBody
  exact (bodyPatchEquiv formed output terminal (pointEquiv p point) actualBody).symm.injective.comp
    ((castBodyPatch_injective formed output terminal (pointEquiv p point)
      (p.compile_eq point.1 point.2).symm newBody).comp
      ((transportBodyPatch_injective p q r s point _ body.1 body.2).comp
        (compilePatchEquiv old rows oldTerminal point compiled).injective))

def fullPatchImageEquiv (point : Point original)
    (compiled : SourceNativeLedgerEvolutionAt original point.2) :
    SourceNativeFiniteLedgerPatchAt original old.exactTransitionAt rows oldTerminal compiled ≃
      Set.range (fullPatch p q r s point compiled) :=
  Equiv.ofInjective (fullPatch p q r s point compiled) (fullPatch_injective p q r s point compiled)

theorem fullPatch_recovers (point : Point original)
    (compiled : SourceNativeLedgerEvolutionAt original point.2)
    (patch : SourceNativeFiniteLedgerPatchAt original old.exactTransitionAt rows oldTerminal compiled) :
    (fullPatchImageEquiv p q r s point compiled).symm
      ⟨fullPatch p q r s point compiled patch, patch, rfl⟩ = patch :=
  (fullPatchImageEquiv p q r s point compiled).symm_apply_apply patch

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
