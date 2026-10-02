import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Events

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory MotherObligationOrigin MotherFullCompiler MotherSourcePrograms MotherLedgerRoot MotherProjectionOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

theorem law_projection_formed (material : M) (value : LawValue) (formed : formLaw material = some value) :
    formProjection (MotherHigherLawValue.split material).1 = some value.1 := by
  unfold formLaw formLawParts at formed
  dsimp only at formed
  obtain ⟨projection, projectionFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  obtain ⟨R, vocabularyFormed, selected⟩ := Option.pbind_eq_some_iff.mp selected
  obtain ⟨law, lawFormed, same⟩ := Option.map_eq_some_iff.mp selected
  exact projectionFormed.trans (congrArg (fun value : LawValue => some value.1) same)

def lawPoints (material : M) (value : LawValue) (formed : formLaw material = some value) :
    Coordinates value.1.1.2.2.source.source :=
  rootCoordinates (MotherHigherLawValue.split (MotherHigherLawValue.split material).1).1 value.1.1
    (projection_root_formed _ value.1 (law_projection_formed material value formed))

def lawWorld (material : M) (value : LawValue) (formed : formLaw material = some value) : LedgerCoordinates value.1.1.1 :=
  (rootWorldCoordinates (MotherHigherLawValue.split (MotherHigherLawValue.split material).1).1 value.1.1
    (projection_root_formed _ value.1 (law_projection_formed material value formed))).toLedgerCoordinates

abbrev LawCertification (value : LawValue) :=
  CertificationSection (law := value.2) (fun point => value.1.1.2.2.source.ledgerCompiler.compile point.2)

def compilerOf (value : LawValue) (certificates : LawCertification value) :
    SourceNativeRestructuringLedgerCompiler value.1.1.2.2.source.source where
  ledgerCompiler := value.1.1.2.2.source.ledgerCompiler
  restructuringLaw := value.2
  certifyRestructuring := fun {current} event => certificates ⟨current, event⟩

abbrev CompilerValue := Σ value : LawValue, SourceNativeRestructuringLedgerCompiler value.1.1.2.2.source.source

def formCompilerParts (parent material : M) : Option CompilerValue :=
  (formLaw parent).pbind (fun value formed =>
    (formCertificationSection (coordinatesOfLaw parent value formed) (lawWorld parent value formed) (lawPoints parent value formed)
      (fun point => value.1.1.2.2.source.ledgerCompiler.compile point.2) material).map (fun certificates => ⟨value, compilerOf value certificates⟩))

/-- The public factory receives only one mother material. Every original
compiled branch keeps its full native restructuring certification, including
the selected split/merge receipts and their whole anchor functions. -/
def formRestructuringCompiler (material : M) : Option CompilerValue :=
  let parts := MotherHigherLawValue.split material
  formCompilerParts parts.1 parts.2

def sourceOf (value : CompilerValue) : SourceNativeRestructuringLedgerSource value.1.1.1.1 value.1.1.1.2.1 :=
  ⟨value.1.1.1.2.2.source.source, value.2⟩

def formRestructuringSource (material : M) :
    Option (Σ N : WorldRelationNetwork.{0}, Σ V : ConstructiveRoot.Vocabulary.{0}, SourceNativeRestructuringLedgerSource N V) :=
  (formRestructuringCompiler material).map (fun value => ⟨value.1.1.1.1, value.1.1.1.2.1, sourceOf value⟩)

theorem every_compiler_on_formed_law (parent : M) (value : LawValue) (formed : formLaw parent = some value)
    (certificates : LawCertification value) :
    ∃ material : M, formRestructuringCompiler material = some ⟨value, compilerOf value certificates⟩ ∧
      formRestructuringSource material = some ⟨value.1.1.1, value.1.1.2.1, sourceOf ⟨value, compilerOf value certificates⟩⟩ := by
  obtain ⟨material, allCertificates⟩ := every_certification_section (coordinatesOfLaw parent value formed)
    (lawWorld parent value formed) (lawPoints parent value formed)
    (fun point => value.1.1.2.2.source.ledgerCompiler.compile point.2) certificates
  have compilerFormed : formRestructuringCompiler (MotherHigherLawValue.pack (parent, material)) =
      some ⟨value, compilerOf value certificates⟩ := by
    simp only [formRestructuringCompiler, MotherHigherLawValue.split_pack, formCompilerParts, formed, Option.pbind_some]
    change (formCertificationSection (coordinatesOfLaw parent value formed) (lawWorld parent value formed)
      (lawPoints parent value formed) (fun point => value.1.1.2.2.source.ledgerCompiler.compile point.2) material).map
        (fun certificates => (⟨value, compilerOf value certificates⟩ : CompilerValue)) = _
    rw [allCertificates]
    rfl
  refine ⟨MotherHigherLawValue.pack (parent, material), compilerFormed, ?_⟩
  simp only [formRestructuringSource, compilerFormed, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
