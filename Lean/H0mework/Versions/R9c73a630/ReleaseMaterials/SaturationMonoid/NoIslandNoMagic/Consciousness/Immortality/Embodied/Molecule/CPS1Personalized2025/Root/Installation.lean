import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root.Base
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root.Materials

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

open CPS1MaterialIncidence.NativeRootDataProbe

attribute [local irreducible] InputBodyAt generated_input source_input_body input_body_next

structure NativeInputMaterial {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) : Type where
  sourceBody : InputBodyAt current.input
  sourceActual : sourceBody = current.body
  write : Native.Write current
  writeActual : write = occurrence.2

def sourceNativeInputMaterial {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) : NativeInputMaterial occurrence :=
  ⟨current.body,rfl,occurrence.2,rfl⟩

inductive Projection | inputs | sequence | experiment | response | certificate
  deriving DecidableEq, Repr

def projectionLaw : SourceNativeProjectionLaw ledgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun face {_} occurrence _ => match face with
    | .inputs => SourceNativeLedgerEvolutionAt ledgerSource.source occurrence × (NativeInputMaterial occurrence × InputMaterial)
    | .sequence => SourceNativeLedgerEvolutionAt ledgerSource.source occurrence × SequenceMaterial
    | .experiment => SourceNativeLedgerEvolutionAt ledgerSource.source occurrence × ExperimentMaterial
    | .response => SourceNativeLedgerEvolutionAt ledgerSource.source occurrence × ResponseMaterial
    | .certificate => PLift OriginalProgramClosure
  project := by
    intro face current occurrence active
    cases face with
    | inputs => exact (ledgerCompiler.compile occurrence,sourceNativeInputMaterial occurrence,generatedInputMaterial)
    | sequence => exact (ledgerCompiler.compile occurrence,generatedSequenceMaterial)
    | experiment => exact (ledgerCompiler.compile occurrence,generatedExperimentMaterial)
    | response => exact (ledgerCompiler.compile occurrence,generatedResponseMaterial)
    | certificate => exact ⟨sourceGeneratedOriginalProgram⟩

def authoritySource : SourceNativeAuthoritySource N V :=
  { baseAuthoritySource with projectionLaw := projectionLaw }

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := emitted
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure N V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def installation : SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.refl projectionLaw

theorem original_source_ledger_and_identity :
    authoritySource.restructuringSource = restructuringSource ∧
    N.anchorAt () = captureKey ∧ N.incidenceAt () = incidenceKey ∧ N.lineageAt () = comparisonLineage ∧
    entry.1 = .originalProgramResponse ∧
    N.openClaimAt entry.2 = .registeredCPS1ProgramAndClinicalResponse := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root
