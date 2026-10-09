import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply.Closure
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

/-- The material at the generated next reproduces every Longitudinal parent
material verbatim (same reads of the parent runtime) and additionally carries
the paid physical-supply account, the OPEN delivery record, the supply
residuals and the carried-forward supply capability. -/
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
  maintenance : Longitudinal.LongitudinalMaintenance
  capability : Longitudinal.NextRoundCapability
  formulation : Longitudinal.FormulationAccount
  residuals : Longitudinal.Residuals
  supply : SupplyAccount
  delivery : PhysicalDelivery
  supplyResiduals : SupplyResiduals
  supplyCapability : SupplyCapability

noncomputable def material : Material :=
  ⟨(Longitudinal.readMaterial parentRuntime).inputs,(Longitudinal.readMaterial parentRuntime).sequence,
    (Longitudinal.readMaterial parentRuntime).experiment,(Longitudinal.readMaterial parentRuntime).response,
    (Longitudinal.readMaterial parentRuntime).originalAlleles,(Longitudinal.readMaterial parentRuntime).reference,
    (Longitudinal.readMaterial parentRuntime).caption,(Longitudinal.readMaterial parentRuntime).provenance,
    (Longitudinal.readMaterial parentRuntime).generatedCoding,(Longitudinal.readMaterial parentRuntime).consumers,
    (Longitudinal.readMaterial parentRuntime).shownReads,(Longitudinal.readMaterial parentRuntime).originalQReads,
    (Longitudinal.readMaterial parentRuntime).a8Reads,(Longitudinal.readMaterial parentRuntime).openFrameReads,
    (Longitudinal.readMaterial parentRuntime).maintenance,(Longitudinal.readMaterial parentRuntime).capability,
    (Longitudinal.readMaterial parentRuntime).formulation,(Longitudinal.readMaterial parentRuntime).residuals,
    Source.account,Source.physicalDelivery,Source.supplyResiduals,Source.capability⟩

inductive Projection | material | certificate deriving DecidableEq, Repr

noncomputable def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun face {_} occurrence _ => match face with
    | .material => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × Material
    | .certificate => PLift PhysicalSupplyClosure
  project := by
    intro face current occurrence active
    cases face with
    | material => exact (ParentLedger.ledgerCompiler.compile occurrence,material)
    | certificate => exact ⟨sourceGeneratedPhysicalSupply⟩

noncomputable def authoritySource := ParentBase.withProjectionCoface projectionLaw

noncomputable def componentInstallation :
    SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

noncomputable def inheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

noncomputable def authoritativeRoot : SourceNativeAuthoritativeRootClosure ParentN ParentV where
  source := authoritySource
  emitted := Longitudinal.authoritativeRoot.emitted
  compiler_commutes := Longitudinal.authoritativeRoot.compiler_commutes

noncomputable def livingRoot : SourceNativeLivingRootClosure ParentN ParentV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem same_source_and_complete_ledger :
    authoritySource.restructuringSource = ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission = ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface = ParentBase.lawSurface ∧
    (∀ current, authoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      Longitudinal.authoritativeRoot.toLedgerRoot.generatedLedgerAt current) := ⟨rfl,rfl,rfl,fun _ => rfl⟩

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply
