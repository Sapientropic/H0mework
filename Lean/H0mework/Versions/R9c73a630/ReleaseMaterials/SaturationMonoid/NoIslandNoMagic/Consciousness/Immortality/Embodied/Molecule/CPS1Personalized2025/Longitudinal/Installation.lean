import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal.Closure
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

structure Material where
  inputs : Root.InputMaterial
  sequence : Root.SequenceMaterial
  experiment : Root.ExperimentMaterial
  response : Root.ResponseMaterial
  originalAlleles : List Ngs.Allele
  reference : Bases
  caption : String
  provenance : String × String × String
  generatedCoding : Fin 17 → Bases
  consumers : Fin 17 → (Bool × Bool) × Option (List String)
  shownReads : Nat
  originalQReads : Nat
  a8Reads : Nat
  openFrameReads : Nat
  maintenance : LongitudinalMaintenance
  capability : NextRoundCapability
  formulation : FormulationAccount
  residuals : Residuals

noncomputable def material : Material :=
  ⟨(Ngs.readMaterial parentRuntime).inputs,(Ngs.readMaterial parentRuntime).sequence,
    (Ngs.readMaterial parentRuntime).experiment,(Ngs.readMaterial parentRuntime).response,
    (Ngs.readMaterial parentRuntime).originalAlleles,(Ngs.readMaterial parentRuntime).reference,
    (Ngs.readMaterial parentRuntime).caption,(Ngs.readMaterial parentRuntime).provenance,
    (Ngs.readMaterial parentRuntime).generatedCoding,(Ngs.readMaterial parentRuntime).consumers,
    (Ngs.readMaterial parentRuntime).shownReads,(Ngs.readMaterial parentRuntime).originalQReads,
    (Ngs.readMaterial parentRuntime).a8Reads,(Ngs.readMaterial parentRuntime).openFrameReads,
    Source.chains,Source.capability,Source.formulation,Source.residuals⟩

inductive Projection | material | certificate deriving DecidableEq, Repr

noncomputable def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun face {_} occurrence _ => match face with
    | .material => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × Material
    | .certificate => PLift LongitudinalClosure
  project := by
    intro face current occurrence active
    cases face with
    | material => exact (ParentLedger.ledgerCompiler.compile occurrence,material)
    | certificate => exact ⟨sourceGeneratedLongitudinalMaintenance⟩

noncomputable def authoritySource := ParentBase.withProjectionCoface projectionLaw

noncomputable def componentInstallation :
    SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

noncomputable def inheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

noncomputable def authoritativeRoot : SourceNativeAuthoritativeRootClosure ParentN ParentV where
  source := authoritySource
  emitted := Ngs.authoritativeRoot.emitted
  compiler_commutes := Ngs.authoritativeRoot.compiler_commutes

noncomputable def livingRoot : SourceNativeLivingRootClosure ParentN ParentV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem same_source_and_complete_ledger :
    authoritySource.restructuringSource = ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission = ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface = ParentBase.lawSurface ∧
    (∀ current, authoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      Ngs.authoritativeRoot.toLedgerRoot.generatedLedgerAt current) := ⟨rfl,rfl,rfl,fun _ => rfl⟩

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
