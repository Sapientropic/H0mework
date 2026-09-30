import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Transport

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

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

/-- All branch-internal patch data follow the very same dependent target/whole
map used by the signed complete compilation equivalence. -/
def fullPatch (point : Point original) (compiled : SourceNativeLedgerEvolutionAt original point.2)
    (patch : SourceNativeFiniteLedgerPatchAt original old.exactTransitionAt rows oldTerminal compiled) :
    SourceNativeFiniteLedgerPatchAt generated formed.exactTransitionAt output terminal
      (fullCompilationEquiv p point.2 compiled) := by
  let body := bodyOfCompilation point compiled
  let newBody : Sigma (LedgerFor generated (pointEquiv p point).2
      (v.evolution point.1 (original.toRootSource.actual.compile point.2))) :=
    ⟨targetEquiv p _ body.1, ledgerForEquiv p point.2 _ body.1 body.2⟩
  let actualBody := (Equiv.cast (congrArg
    (fun branch => Sigma (LedgerFor generated (pointEquiv p point).2 branch))
      (p.compile_eq point.1 point.2).symm)) newBody
  have transferred : PatchFor formed output terminal (pointEquiv p point)
      (v.evolution point.1 (original.toRootSource.actual.compile point.2)) newBody.1 newBody.2 :=
    transportBodyPatch p q r s point _ body.1 body.2
      (compilePatchEquiv old rows oldTerminal point compiled patch)
  exact (bodyPatchEquiv formed output terminal (pointEquiv p point) actualBody).symm
    (castBodyPatch formed output terminal (pointEquiv p point)
      (p.compile_eq point.1 point.2).symm newBody transferred)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
