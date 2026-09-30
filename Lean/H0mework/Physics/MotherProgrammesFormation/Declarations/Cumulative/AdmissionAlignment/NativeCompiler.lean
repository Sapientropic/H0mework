import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.JointOutput

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherFullPatches MotherPatchInventory
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}

/-- A coverage-side presentation of the actual complete compiler output.
Every field is already supplied by the signed full-source formation mouth. -/
structure CompilerPresentation
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (originalCompiler : SourceNativeLedgerCompiler original)
    (generatedCompiler : SourceNativeLedgerCompiler generated) where
  transitions : TransitionPresentation
    (transportedTransitions p (Transitions.ofCompiler originalCompiler)) (Transitions.ofCompiler generatedCompiler)
  rows : WritePresentation (sourceWrite p transitions originalCompiler.writeRowSource) generatedCompiler.writeRowSource
  terminal : TerminalPresentation (transportedTerminal p originalCompiler.terminalRowSource) generatedCompiler.terminalRowSource
  compilation : ∀ point : Point original,
    (fullCompilationEquiv p point.2).symm (generatedCompiler.compile (pointEquiv p point).2) =
      originalCompiler.compile point.2
  patch : ∀ point : Point original, generatedCompiler.compilePatch (pointEquiv p point).2 =
    originalPatchAt p originalCompiler (originalCompilations generatedCompiler) transitions rows terminal compilation point

namespace CompilerPresentation

variable {p : MotherNativeSourceOrigin.Presentation n v original generated}
    {originalCompiler : SourceNativeLedgerCompiler original}
    {generatedCompiler : SourceNativeLedgerCompiler generated}
    (presentation : CompilerPresentation p originalCompiler generatedCompiler)

theorem actual_output_eq_image (point : Point original) :
    outputEmbedding p presentation.transitions presentation.rows presentation.terminal point
      (compilerOutput originalCompiler point) = compilerOutput generatedCompiler (pointEquiv p point) := by
  have transported := producedOutput_eq_image p originalCompiler (originalCompilations generatedCompiler)
    presentation.transitions presentation.rows presentation.terminal presentation.compilation point
  exact transported.trans (congrArg
    (fun patch => (⟨generatedCompiler.compile (pointEquiv p point).2, patch⟩ :
      FullOutput (Transitions.ofCompiler generatedCompiler) generatedCompiler.writeRowSource
        generatedCompiler.terminalRowSource (pointEquiv p point))) (presentation.patch point).symm)

def actualImage (point : Point original) :
    Set.range (outputEmbedding p presentation.transitions presentation.rows presentation.terminal point) :=
  ⟨compilerOutput generatedCompiler (pointEquiv p point), compilerOutput originalCompiler point,
    presentation.actual_output_eq_image point⟩

def restore (point : Point original) :
    FullOutput (Transitions.ofCompiler originalCompiler) originalCompiler.writeRowSource
      originalCompiler.terminalRowSource point :=
  (outputImageEquiv p presentation.transitions presentation.rows presentation.terminal point).symm
    (presentation.actualImage point)

theorem restore_eq (point : Point original) :
    presentation.restore point = compilerOutput originalCompiler point := by
  have same : presentation.actualImage point =
      outputImageEquiv p presentation.transitions presentation.rows presentation.terminal point
        (compilerOutput originalCompiler point) :=
    Subtype.ext (presentation.actual_output_eq_image point).symm
  exact (congrArg (outputImageEquiv p presentation.transitions presentation.rows presentation.terminal point).symm same).trans
    ((outputImageEquiv p presentation.transitions presentation.rows presentation.terminal point).symm_apply_apply _)

theorem restore_compile (point : Point original) :
    (presentation.restore point).1 = originalCompiler.compile point.2 :=
  congrArg Sigma.fst (presentation.restore_eq point)

theorem restore_patch (point : Point original) :
    HEq (presentation.restore point).2 (originalCompiler.compilePatch point.2) := by
  generalize restoredEq : presentation.restore point = restored at *
  have same := presentation.restore_eq point
  rw [restoredEq] at same
  cases same
  rfl

end CompilerPresentation

def presentationOfPatches
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (compiler : SourceNativeLedgerCompiler original) (compiled : CompilationSection generated)
    {operations : Transitions generated}
    (q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) operations)
    {rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt}
    (r : WritePresentation (sourceWrite p q compiler.writeRowSource) rows)
    {terminal : LedgerTerminalRowSourceAt generated}
    (s : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) terminal)
    (recover : ∀ point : Point original,
      (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2) :
    let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
    CompilerPresentation p compiler
      (compilerOfPatches value (originalPatchSection p compiler compiled q r s recover)) := {
  transitions := q
  rows := r
  terminal := s
  compilation := recover
  patch := originalPatchSection_at p compiler compiled q r s recover
}

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
