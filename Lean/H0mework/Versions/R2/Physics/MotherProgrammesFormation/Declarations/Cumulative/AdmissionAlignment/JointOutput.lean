import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.FullPatch

/-! Joint recovery of the entire compilation and its dependent finite patch.
The common carrier is the exact image of the already signed source
transporter. Its inverse reads both values; no original result is stored
inside a generated factory or substituted for an unread generated value. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

abbrev FullOutput {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (operations : Transitions source)
    (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (terminal : LedgerTerminalRowSourceAt source) (point : Point source) :=
  Σ compiled : SourceNativeLedgerEvolutionAt source point.2,
    SourceNativeFiniteLedgerPatchAt source operations.exactTransitionAt rows terminal compiled

def compilerOutput {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (compiler : SourceNativeLedgerCompiler source) (point : Point source) :
    FullOutput (Transitions.ofCompiler compiler) compiler.writeRowSource compiler.terminalRowSource point :=
  ⟨compiler.compile point.2, compiler.compilePatch point.2⟩

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

def outputEmbedding (point : Point original) :
    FullOutput old rows oldTerminal point ↪ FullOutput formed output terminal (pointEquiv p point) where
  toFun := fun value => ⟨fullCompilationEquiv p point.2 value.1, fullPatch p q r s point value.1 value.2⟩
  inj' := by
    rintro ⟨firstCompile, firstPatch⟩ ⟨lastCompile, lastPatch⟩ same
    have compiledSame := (fullCompilationEquiv p point.2).injective (congrArg Sigma.fst same)
    cases compiledSame
    have patchSame := fullPatch_injective p q r s point firstCompile (eq_of_heq (Sigma.mk.inj same).2)
    cases patchSame
    rfl

def outputImageEquiv (point : Point original) :
    FullOutput old rows oldTerminal point ≃ Set.range (outputEmbedding p q r s point) :=
  Equiv.ofInjective (outputEmbedding p q r s point) (outputEmbedding p q r s point).injective

theorem output_recovers (point : Point original) (value : FullOutput old rows oldTerminal point) :
    (outputImageEquiv p q r s point).symm
      ⟨outputEmbedding p q r s point value, value, rfl⟩ = value :=
  (outputImageEquiv p q r s point).symm_apply_apply value

private theorem sigma_cast {A : Type} (P : A → Type) {first last : A}
    (same : first = last) (value : P first) :
    (⟨first, value⟩ : Sigma P) = ⟨last, Equiv.cast (congrArg P same) value⟩ := by
  cases same
  rfl

variable (compiler : SourceNativeLedgerCompiler original) (compiled : CompilationSection generated)
    (qs : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) formed)
    (rs : WritePresentation (sourceWrite p qs compiler.writeRowSource) output)
    (ss : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) terminal)
    (recover : ∀ point : Point original,
      (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2)

def producedOutput (point : Point original) : FullOutput formed output terminal (pointEquiv p point) :=
  ⟨compiled (pointEquiv p point), originalPatchAt p compiler compiled qs rs ss recover point⟩

theorem producedOutput_eq_image (point : Point original) :
    outputEmbedding p qs rs ss point (compilerOutput compiler point) =
      producedOutput p compiler compiled qs rs ss recover point :=
  sigma_cast (SourceNativeFiniteLedgerPatchAt generated formed.exactTransitionAt output terminal)
    (compilation_image p compiler compiled recover point)
    (fullPatch p qs rs ss point (compiler.compile point.2) (compiler.compilePatch point.2))

def producedImage (point : Point original) : Set.range (outputEmbedding p qs rs ss point) :=
  ⟨producedOutput p compiler compiled qs rs ss recover point,
    compilerOutput compiler point, producedOutput_eq_image p compiler compiled qs rs ss recover point⟩

/-- This consumes the exact compilation/patch shape returned by the signed
full-source factory, and recovers the complete original pair. -/
theorem producedOutput_recovers (point : Point original) :
    (outputImageEquiv p qs rs ss point).symm
      (producedImage p compiler compiled qs rs ss recover point) = compilerOutput compiler point := by
  have same : producedImage p compiler compiled qs rs ss recover point =
      outputImageEquiv p qs rs ss point (compilerOutput compiler point) :=
    Subtype.ext (producedOutput_eq_image p compiler compiled qs rs ss recover point).symm
  exact (congrArg (outputImageEquiv p qs rs ss point).symm same).trans
    ((outputImageEquiv p qs rs ss point).symm_apply_apply (compilerOutput compiler point))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
