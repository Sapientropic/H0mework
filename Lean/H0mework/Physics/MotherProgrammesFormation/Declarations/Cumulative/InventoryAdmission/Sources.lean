import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.NetworkOrigin

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

abbrev SourcePair := Σ represented : MotherRestructuringReceipts.CompilerValue,
  Σ ActualV : ConstructiveRoot.Vocabulary.{0}, SourceNativeLedgerSource represented.1.1.1.1 ActualV

def formSourcesParts (parent material : M) : Option SourcePair :=
  (MotherRestructuringReceipts.formRestructuringCompiler parent).bind (fun represented =>
    (MotherPatchInventory.formLedgerSource material).bind (fun ⟨N, V, actual⟩ =>
      if same : N = represented.1.1.1.1 then
        some ⟨represented, V, Eq.mp (congrArg (fun network => SourceNativeLedgerSource network V) same) actual⟩
      else none))

/-- Both complete source declarations are formed before the dependent
admission fields. Their network equality is checked inside the factory. -/
def formSources (material : M) : Option SourcePair :=
  let parts := MotherHigherLawValue.split material
  formSourcesParts parts.1 parts.2

theorem sources_formed (parent material : M) (represented : MotherRestructuringReceipts.CompilerValue)
    (parentFormed : MotherRestructuringReceipts.formRestructuringCompiler parent = some represented)
    (V : ConstructiveRoot.Vocabulary.{0}) (actual : SourceNativeLedgerSource represented.1.1.1.1 V)
    (actualFormed : MotherPatchInventory.formLedgerSource material = some ⟨represented.1.1.1.1, V, actual⟩) :
    formSources (MotherHigherLawValue.pack (parent, material)) = some ⟨represented, V, actual⟩ := by
  simp only [formSources, MotherHigherLawValue.split_pack, formSourcesParts, parentFormed, Option.bind_some, actualFormed]
  split
  · rfl
  · contradiction

theorem every_actual_source (parent : M) (represented : MotherRestructuringReceipts.CompilerValue)
    (parentFormed : MotherRestructuringReceipts.formRestructuringCompiler parent = some represented)
    {N : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N represented.1.1.1.1)
    (V : ConstructiveRoot.Vocabulary.{0}) (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original)
    (encode : SourceWriteTotal compiler ↪ B) :
    ∃ material : M, ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : SourceNativeSource represented.1.1.1.1 W,
      ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
      ∃ compiled : CompilationSection generated, ∃ terminal : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated, ∃ rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt,
      ∃ s : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) terminal,
      ∃ q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) operations,
      ∃ r : WritePresentation (sourceWrite p q compiler.writeRowSource) rows,
      ∃ recover : ∀ point : Point original, (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2,
        let value : WriteProgramValue := ⟨⟨represented.1.1.1.1, W, generated⟩, compiled, terminal, operations, rows⟩
        let patches := originalPatchSection p compiler compiled q r s recover
        let full := MotherPatchInventory.compilerOfPatches value patches
        formSources material = some ⟨represented, W, ⟨generated, full⟩⟩ ∧
        ∀ point : Point original, full.compilePatch (pointEquiv p point).2 = originalPatchAt p compiler compiled q r s recover point := by
  let vocabularyCode : MotherVocabularyOrigin.Total V ↪ B :=
    ⟨fun value => encode (.inl (.inl (.inl (.inr (.inl value))))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (encode.injective same)))))⟩
  let eventCode : Point original ↪ B :=
    ⟨fun value => encode (.inl (.inl (.inl (.inr (.inr value))))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (encode.injective same)))))⟩
  obtain ⟨sourceMaterial, W, generated, v, formed, ⟨p⟩⟩ :=
    every_source_on_network_value (networkMaterial parent) (restructuring_network_formed parent represented parentFormed)
      n V original vocabularyCode eventCode
  obtain ⟨material, compiled, terminal, operations, rows, s, q, r, recover, _compilerFormed, sourceFormed, patchAt⟩ :=
    full_compiler_on_source p compiler (MotherHigherLawValue.pack (networkMaterial parent, sourceMaterial)) formed encode
  exact ⟨MotherHigherLawValue.pack (parent, material), W, generated, v, p, compiled, terminal, operations, rows, s, q, r,
    recover, sources_formed parent material represented parentFormed W _ sourceFormed, patchAt⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
