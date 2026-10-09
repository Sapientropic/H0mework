import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs.Closure
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

structure Material where
  inputs : Root.InputMaterial
  sequence : Root.SequenceMaterial
  experiment : Root.ExperimentMaterial
  response : Root.ResponseMaterial
  originalAlleles : List Allele
  reference : Bases
  caption : String
  provenance : String × String × String
  generatedCoding : Fin 17 → Bases
  consumers : Fin 17 → (Bool × Bool) × Option (List String)
  shownReads : Nat
  originalQReads : Nat
  a8Reads : Nat
  openFrameReads : Nat
noncomputable def material : Material :=
  ⟨CPS1Personalized2025.Runtime.readInputs parentRuntime,
    CPS1Personalized2025.Runtime.readSequence parentRuntime,
    CPS1Personalized2025.Runtime.readExperiment parentRuntime,
    CPS1Personalized2025.Runtime.readResponse parentRuntime,
    Source.rows,Source.reference,Source.caption,(Source.parentSha,Source.pdfSha,Source.imageSha),
    fun i => Sequence.coding (Source.row i).word,Readout.extension.revisedFace,
    Counts.shown,Counts.count Sequence.originalQ,Counts.count Sequence.a8,Counts.count Sequence.openFrame⟩

inductive Projection | material | certificate deriving DecidableEq, Repr
noncomputable def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun face {_} occurrence _ => match face with
    | .material => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × Material
    | .certificate => PLift JointAlleleClosure
  project := by
    intro face current occurrence active
    cases face with
    | material => exact (ParentLedger.ledgerCompiler.compile occurrence,material)
    | certificate => exact ⟨sourceGeneratedJointAlleles⟩

noncomputable def authoritySource := ParentBase.withProjectionCoface projectionLaw
noncomputable def componentInstallation :
    SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw
noncomputable def inheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw
noncomputable def authoritativeRoot : SourceNativeAuthoritativeRootClosure ParentN ParentV where
  source := authoritySource
  emitted := Root.authoritativeRoot.emitted
  compiler_commutes := Root.authoritativeRoot.compiler_commutes
noncomputable def livingRoot : SourceNativeLivingRootClosure ParentN ParentV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem same_source_and_complete_ledger :
    authoritySource.restructuringSource = ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission = ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface = ParentBase.lawSurface ∧
    (∀ current, authoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      Root.authoritativeRoot.toLedgerRoot.generatedLedgerAt current) := ⟨rfl,rfl,rfl,fun _ => rfl⟩
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
