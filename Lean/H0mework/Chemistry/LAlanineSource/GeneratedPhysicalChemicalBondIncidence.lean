import Lean.Data.Json
import Lean.Elab.Command
import H0mework.Cognition.Empirical.Sha256
import H0mework.Chemistry.LAlanineSource.TargetErasedBondDensity

/-! # Post-freeze physical/chemical incidence adjudication for L-alanine -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Producer

noncomputable section

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open Interface Source Calculation

private def jsonAt? (value : Lean.Json) : List String → Except String Lean.Json
  | [] => pure value
  | key :: rest => do jsonAt? (← value.getObjVal? key) rest

private def jsonAsAt? (alpha : Type) [Lean.FromJson alpha]
    (value : Lean.Json) (path : List String) : Except String alpha := do
  Lean.fromJson? (← jsonAt? value path)

private def expectStringAt (value : Lean.Json) (path : List String)
    (expected : String) : Except String Unit := do
  let actual ← jsonAsAt? String value path
  unless actual == expected do throw s!"evidence string {path} changed"

private def expectNatAt (value : Lean.Json) (path : List String)
    (expected : Nat) : Except String Unit := do
  let actual ← jsonAsAt? Nat value path
  unless actual == expected do throw s!"evidence Nat {path} changed"

private def expectIntAt (value : Lean.Json) (path : List String)
    (expected : Int) : Except String Unit := do
  let actual ← jsonAsAt? Int value path
  unless actual == expected do throw s!"evidence Int {path} changed"

private def expectBoolAt (value : Lean.Json) (path : List String)
    (expected : Bool) : Except String Unit := do
  let actual ← jsonAsAt? Bool value path
  unless actual == expected do throw s!"evidence Bool {path} changed"

private def expectStringArraysAt (value : Lean.Json) (path : List String)
    (expected : Array (Array String)) : Except String Unit := do
  let actual ← jsonAsAt? (Array (Array String)) value path
  unless actual == expected do throw s!"evidence addresses {path} changed"

private def verifyEvidence (value : Lean.Json) : Except String Unit := do
  expectStringAt value ["schema"]
    "lalanine40k-quantum-bond-density-adjudication/v1"
  expectStringAt value ["source_artifact", "sha256"]
    "7b042ae4fb66516165dcbc77fa66dd19e9fa6ea0160a4b99147f7862e2a8ba09"
  expectBoolAt value ["source_artifact", "fresh_replay_byte_identical"] true
  for entry in [("rows", 158892)] do
    expectNatAt value ["unmerged", entry.1] entry.2
  for entry in [("measured_rows", 159400), ("kept_rows", 158892),
      ("p222_unique_rows", 15910), ("p222_theoretical_rows", 16476),
      ("friedel_merged_unique_rows", 8955),
      ("friedel_merged_theoretical_rows", 9018)] do
    expectNatAt value ["reduction_log_receipt", entry.1] entry.2
  let commuting := ["physical_chemical_commuting"]
  for entry in [("registered_heavy_pair_rows", 15),
      ("computed_bcp_rows", 5), ("published_heavy_bond_rows", 5)] do
    expectNatAt value (commuting ++ [entry.1]) entry.2
  expectBoolAt value (commuting ++ ["computed_equals_published"]) true
  expectStringArraysAt value (commuting ++ ["addresses"])
    #[#["C004", "C005"], #["C004", "O001"], #["C004", "O002"],
      #["C005", "C006"], #["C005", "N003"]]
  let diffraction := ["diffraction_adjudication"]
  for entry in [("embedded_reflection_rows", 15872),
      ("positive_observed_squared_rows", 15680)] do
    expectNatAt value (diffraction ++ [entry.1]) entry.2
  for entry in [("laue_class_count", 8917), ("fold_count", 10),
      ("cross_fold_equivalent_class_leakage", 0)] do
    expectNatAt value (diffraction ++ ["partition", entry.1]) entry.2
  expectBoolAt value
    (diffraction ++ ["ten_fold_adjudication",
      "every_fold_prefers_molecular_density"]) true
  for entry in [("aggregate_molecular_r1_ppb", 100891655),
      ("aggregate_independent_atom_r1_ppb", 103225454),
      ("aggregate_molecular_margin_ppb", 2333799),
      ("minimum_fold_margin_ppb", 139597),
      ("maximum_fold_margin_ppb", 5207119),
      ("aggregate_molecular_pearson_ppb", 994335367),
      ("aggregate_independent_atom_pearson_ppb", 993669330)] do
    expectNatAt value
      (diffraction ++ ["ten_fold_adjudication", entry.1]) entry.2
  for entry in [("aggregate_molecular_r1_ppb", 97199068),
      ("aggregate_independent_atom_r1_ppb", 96905487)] do
    expectNatAt value
      (diffraction ++ ["alternative_fit_loss_hostile", entry.1]) entry.2
  expectIntAt value
    (diffraction ++ ["alternative_fit_loss_hostile",
      "aggregate_molecular_margin_ppb"]) (-293581)
  expectBoolAt value
    (diffraction ++ ["alternative_fit_loss_hostile",
      "universally_prefers_molecular_density"]) false
  expectBoolAt value
    (diffraction ++ ["experimental_or_xcw_density_claimed"]) false
  expectBoolAt value
    (diffraction ++ ["atomwise_anisotropic_displacement_modeled"]) false
  expectBoolAt value
    (diffraction ++ ["metric_independent_model_superiority_claimed"]) false
  expectBoolAt value
    (diffraction ++ ["geometry_refined_against_all_embedded_reflections"])
    true
  expectNatAt value (diffraction ++ ["geometry_refinement_rows"]) 15872
  expectBoolAt value
    (diffraction ++ ["statistically_independent_holdout_claimed"]) false
  expectBoolAt value
    (diffraction ++ ["shell_residual", "uniform_shell_dominance_claimed"])
    false
  expectBoolAt value
    ["target_erasure", "source_geometry_unchanged_after_bond_field_removal"]
    true
  expectBoolAt value ["target_erasure", "source_runtime_read_geom_bond"] false
  expectBoolAt value
    ["target_erasure", "source_runtime_read_connected_atom_local_axes"] false
  expectNatAt value
    ["zenodo_raw_receipt", "converted_raw_esperanto_file_count"] 6
  expectNatAt value
    ["zenodo_raw_receipt", "converted_raw_esperanto_bytes"] 6538061312
  expectBoolAt value
    ["zenodo_raw_receipt", "converted_raw_esperanto_archives_downloaded_or_consumed"]
    false
  expectBoolAt value
    ["hostiles_and_residuals", "promolecule_bcp_topology_collision"] true
  expectBoolAt value
    ["hostiles_and_residuals", "topology_alone_proves_electron_sharing"] false
  expectBoolAt value
    ["hostiles_and_residuals", "distance_only_separates_this_fixture"] true
  expectNatAt value
    ["hostiles_and_residuals", "geometry_gap_microangstrom"] 705747
  expectBoolAt value
    ["hostiles_and_residuals", "finite_search_is_continuum_global_proof"] false
  expectBoolAt value
    ["hostiles_and_residuals", "periodic_environment_modeled"] false

run_cmd do
  let evidenceText :=
    include_str "../../../../evidence/biomedical/evidence/lalanine40k-quantum-bond-density.json"
  unless Sha256.hex evidenceText ==
      "6480c37593da5498d2ffd046e34fb3a886806f0d7b5c898a7c575268c008af78" do
    throwError "L-alanine post-freeze evidence SHA-256 changed"
  let value ← match Lean.Json.parse evidenceText with
    | .ok value => pure value
    | .error error => throwError "L-alanine evidence parse failed: {error}"
  match verifyEvidence value with
  | .ok () => pure ()
  | .error error => throwError "L-alanine post-freeze evidence rejected: {error}"

def registeredChemicalIncidence : ASUHeavyPair → Bool
  | .c004C005 => true
  | .c004C006 => false
  | .c004N003 => false
  | .c004O001 => true
  | .c004O002 => true
  | .c005C006 => true
  | .c005N003 => true
  | .c005O001 => false
  | .c005O002 => false
  | .c006N003 => false
  | .c006O001 => false
  | .c006O002 => false
  | .n003O001 => false
  | .n003O002 => false
  | .o001O002 => false

theorem physicalBondIncidence_commutes (pair : ASUHeavyPair) :
    bcpIncidence pair = registeredChemicalIncidence pair := by
  cases pair <;> rfl

def registeredChemicalIncidenceReadout : IndependentReadout ASUHeavyPair where
  Output := Bool
  read := registeredChemicalIncidence

theorem registeredChemicalIncidence_compatible :
    physicalPairConsumers.ReadoutCompatible registeredChemicalIncidence := by
  intro left right same
  exact (physicalBondIncidence_commutes left).symm.trans <|
    (same .topology).trans (physicalBondIncidence_commutes right)

theorem registeredChemicalIncidence_uniqueFactorization :
    ∃! factor : Set.range physicalCanonicalRead → Bool,
      ∀ pair,
        factor ⟨physicalCanonicalRead pair, pair, rfl⟩ =
          registeredChemicalIncidence pair :=
  (physicalPairConsumers.readoutCompatible_iff_uniqueFactorization
    registeredChemicalIncidence).1 registeredChemicalIncidence_compatible

theorem physicalField_escapes_chemicalIncidenceKernel :
    FaceKernelEscapeAt registeredChemicalIncidence
      physicalFieldIndependentReadout := by
  refine ⟨.c004C005, .c004O001, rfl, ?_⟩
  intro same
  have densitySame := congrArg PairPhysicalReadout.bcpDensityNano same
  exact (by decide : (247272356 : Nat) ≠ 367397560) densitySame

theorem chemicalIncidence_cannotMint_completePhysicalField :
    ¬ Function.FactorsThrough pairReadoutAt registeredChemicalIncidence :=
  physicalField_escapes_chemicalIncidenceKernel.not_factorsThrough

def diffraction : DiffractionDensityAdjudication :=
  { embeddedReflectionRows := 15872
    positiveObservedSquaredRows := 15680
    laueClassCount := 8917
    foldCount := 10
    crossFoldEquivalentClassLeakage := 0
    molecularCrossValidatedR1Ppb := 100891655
    independentAtomCrossValidatedR1Ppb := 103225454
    aggregateCrossValidatedMarginPpb := 2333799
    minimumFoldMarginPpb := 139597
    maximumFoldMarginPpb := 5207119
    everyFoldPrefersMolecularDensity := true
    molecularCrossValidatedPearsonPpb := 994335367
    independentAtomCrossValidatedPearsonPpb := 993669330
    lowResolutionMolecularR1Ppb := 53512496
    lowResolutionIndependentAtomR1Ppb := 58646592
    highResolutionMolecularR1Ppb := 150312833
    highResolutionIndependentAtomR1Ppb := 149725644
    amplitudeL2MolecularR1Ppb := 97199068
    amplitudeL2IndependentAtomR1Ppb := 96905487
    amplitudeL2MolecularMarginPpb := -293581
    amplitudeL2UniversallyPrefersMolecularDensity := false
    uniformShellDominanceClaimed := false
    geometryRefinedAgainstAllReflections := true
    statisticallyIndependentHoldoutClaimed := false
    metricIndependentModelSuperiorityClaimed := false }

def postFreezeAdjudication : PostFreezeChemicalAdjudication :=
  { registeredHeavyPairRows := 15
    computedBCPRows := 5
    publishedHeavyBondRows := 5
    computedEqualsPublished := true
    sourceGeometryUnchangedAfterBondFieldRemoval := true
    diffraction := diffraction
    geometryOnlySeparatesFixture := true
    geometryGapMicroangstrom := 705747 }

def densityArmTopology (_arm : DensityArm) : ASUHeavyPair → Bool :=
  bcpIncidence

def densityArmDeformation : DensityArm → ASUHeavyPair → Int × Int × Int
  | .molecularBLYP => pairDeformationReadout
  | .independentAtomSAD => fun _pair => (0, 0, 0)

def densityArmRegisteredCrossValidatedR1 : DensityArm → Nat
  | .molecularBLYP => diffraction.molecularCrossValidatedR1Ppb
  | .independentAtomSAD => diffraction.independentAtomCrossValidatedR1Ppb

inductive DensityArmConsumer where
  | topology
  | deformation
  | diffraction
  deriving DecidableEq, Repr

def densityArmConsumers : IndependentConsumerSystem DensityArm where
  Consumer := DensityArmConsumer
  Output
    | .topology => ASUHeavyPair → Bool
    | .deformation => ASUHeavyPair → Int × Int × Int
    | .diffraction => Nat
  read
    | .topology => densityArmTopology
    | .deformation => densityArmDeformation
    | .diffraction => densityArmRegisteredCrossValidatedR1
  positive := ⟨.diffraction⟩

theorem densityArmConsumers_indistinguishable_iff_arm_eq
    (left right : DensityArm) :
    densityArmConsumers.Indistinguishable left right ↔ left = right := by
  constructor
  · intro same
    cases left <;> cases right
    · rfl
    · have fitSame := same .diffraction
      exact False.elim ((by decide : (100891655 : Nat) ≠ 103225454) fitSame)
    · have fitSame := same .diffraction
      exact False.elim ((by decide : (103225454 : Nat) ≠ 100891655) fitSame)
    · rfl
  · intro same
    subst right
    exact densityArmConsumers.indistinguishable_refl left

theorem densityArmCanonicalRead_injective :
    Function.Injective densityArmConsumers.canonicalRead := by
  intro left right same
  exact (densityArmConsumers_indistinguishable_iff_arm_eq left right).1
    ((densityArmConsumers.canonicalKernelExact left right).1 same)

noncomputable def densityArmQuotientEquivRange :
    densityArmConsumers.Quotient ≃
      Set.range densityArmConsumers.canonicalRead :=
  densityArmConsumers.canonicalQuotientEquivRange

theorem everyDensityArmConsumer_uniqueFactorization
    (consumer : densityArmConsumers.Consumer) :
    ∃! factor : Set.range densityArmConsumers.canonicalRead →
        densityArmConsumers.Output consumer,
      ∀ arm,
        factor ⟨densityArmConsumers.canonicalRead arm, arm, rfl⟩ =
          densityArmConsumers.read consumer arm :=
  densityArmConsumers.everyConsumer_uniqueFactorization consumer

theorem densityArmCompleteCarrier_uniqueIso
    {Alternate : Type} (alternate : DensityArm → Alternate)
    (alternateExact : FaceKernelExactAt densityArmConsumers alternate) :
    ∃! equivalence : Set.range densityArmConsumers.canonicalRead ≃
        Set.range alternate,
      ∀ arm,
        equivalence ⟨densityArmConsumers.canonicalRead arm, arm, rfl⟩ =
          ⟨alternate arm, arm, rfl⟩ :=
  densityArmConsumers.completeCarrier_uniqueIso alternate alternateExact

def densityArmIdentityReadout : IndependentReadout DensityArm where
  Output := DensityArm
  read := id

theorem densityArmIdentity_escapes_topologyKernel :
    FaceKernelEscapeAt densityArmTopology densityArmIdentityReadout :=
  ⟨.molecularBLYP, .independentAtomSAD, rfl, by
    intro same
    exact DensityArm.noConfusion same⟩

theorem topology_cannotMint_densityArmIdentity :
    ¬ Function.FactorsThrough id densityArmTopology :=
  densityArmIdentity_escapes_topologyKernel.not_factorsThrough

theorem registeredTenFoldReadback_strictlyPrefersMolecularDensity :
    diffraction.molecularCrossValidatedR1Ppb <
      diffraction.independentAtomCrossValidatedR1Ppb := by
  decide

theorem everyRegisteredFold_prefersMolecularDensity :
    diffraction.everyFoldPrefersMolecularDensity = true ∧
      0 < diffraction.minimumFoldMarginPpb := by
  exact ⟨rfl, by decide⟩

theorem highResolutionShell_doesNotUniformlyPreferMolecularDensity :
    diffraction.highResolutionIndependentAtomR1Ppb <
      diffraction.highResolutionMolecularR1Ppb := by
  decide

theorem amplitudeL2_hostile_prefersIndependentAtomDensity :
    diffraction.amplitudeL2IndependentAtomR1Ppb <
      diffraction.amplitudeL2MolecularR1Ppb ∧
      diffraction.amplitudeL2MolecularMarginPpb < 0 := by
  exact ⟨by decide, by decide⟩

structure SourceGeneratedLAlanine40KPhysicalChemicalBondIncidenceCrown : Prop where
  physicalProducer : SourceGeneratedTargetErasedLAlanine40KBondDensityCrown
  sameOccurrenceIncidence : ∀ pair,
    bcpIncidence pair = registeredChemicalIncidence pair
  chemicalFactorization :
    ∃! factor : Set.range physicalCanonicalRead → Bool,
      ∀ pair,
        factor ⟨physicalCanonicalRead pair, pair, rfl⟩ =
          registeredChemicalIncidence pair
  chemicalCannotMintPhysicalField :
    ¬ Function.FactorsThrough pairReadoutAt registeredChemicalIncidence
  densityArmPositiveConsumer : Nonempty densityArmConsumers.Consumer
  densityArmKernel :
    FaceKernelExactAt densityArmConsumers densityArmConsumers.canonicalRead
  densityArmQuotient : Nonempty
    (densityArmConsumers.Quotient ≃
      Set.range densityArmConsumers.canonicalRead)
  everyDensityArmConsumerFactorizes : ∀ consumer,
    ∃! factor : Set.range densityArmConsumers.canonicalRead →
        densityArmConsumers.Output consumer,
      ∀ arm,
        factor ⟨densityArmConsumers.canonicalRead arm, arm, rfl⟩ =
          densityArmConsumers.read consumer arm
  densityArmSameRootUniqueIso : ∀ {Alternate : Type}
      (alternate : DensityArm → Alternate)
      (_alternateExact : FaceKernelExactAt densityArmConsumers alternate),
    ∃! equivalence : Set.range densityArmConsumers.canonicalRead ≃
        Set.range alternate,
      ∀ arm,
        equivalence ⟨densityArmConsumers.canonicalRead arm, arm, rfl⟩ =
          ⟨alternate arm, arm, rfl⟩
  topologyCollision : densityArmTopology .molecularBLYP =
    densityArmTopology .independentAtomSAD
  topologyCannotMintArm : ¬ Function.FactorsThrough id densityArmTopology
  registeredReadbackSelectsMolecular :
    diffraction.molecularCrossValidatedR1Ppb <
      diffraction.independentAtomCrossValidatedR1Ppb
  everyRegisteredFoldSelectsMolecular :
    diffraction.everyFoldPrefersMolecularDensity = true ∧
      0 < diffraction.minimumFoldMarginPpb
  shellResidualVisible : diffraction.highResolutionIndependentAtomR1Ppb <
    diffraction.highResolutionMolecularR1Ppb
  alternativeFitLossReverses :
    diffraction.amplitudeL2IndependentAtomR1Ppb <
        diffraction.amplitudeL2MolecularR1Ppb ∧
      diffraction.amplitudeL2MolecularMarginPpb < 0
  geometryWasFullDataRefined :
    diffraction.geometryRefinedAgainstAllReflections = true
  noStatisticallyIndependentHoldout :
    diffraction.statisticallyIndependentHoldoutClaimed = false
  noMetricIndependentSuperiority :
    diffraction.metricIndependentModelSuperiorityClaimed = false
  targetErased : postFreezeAdjudication.sourceGeometryUnchangedAfterBondFieldRemoval = true
  geometryOnlyFixture : postFreezeAdjudication.geometryOnlySeparatesFixture = true
  geometryGap : postFreezeAdjudication.geometryGapMicroangstrom = 705747
  noXCWDensity : IsEmpty ExperimentalXCWCrystalDensityAt
  noContinuumGlobalCensus : IsEmpty ContinuumGlobalCriticalPointCensusAt
  noAbsoluteBondOntology : IsEmpty AbsoluteChemicalBondOntologyAt
  rawEsperantoNotConsumed : IsEmpty ConsumedConvertedRawEsperantoFramesAt

theorem sourceGeneratedLAlanine40KPhysicalChemicalBondIncidence_crown :
    SourceGeneratedLAlanine40KPhysicalChemicalBondIncidenceCrown where
  physicalProducer := sourceGeneratedTargetErasedLAlanine40KBondDensity_crown
  sameOccurrenceIncidence := physicalBondIncidence_commutes
  chemicalFactorization := registeredChemicalIncidence_uniqueFactorization
  chemicalCannotMintPhysicalField :=
    chemicalIncidence_cannotMint_completePhysicalField
  densityArmPositiveConsumer := densityArmConsumers.positive
  densityArmKernel := densityArmConsumers.canonicalKernelExact
  densityArmQuotient := ⟨densityArmQuotientEquivRange⟩
  everyDensityArmConsumerFactorizes :=
    everyDensityArmConsumer_uniqueFactorization
  densityArmSameRootUniqueIso := densityArmCompleteCarrier_uniqueIso
  topologyCollision := rfl
  topologyCannotMintArm := topology_cannotMint_densityArmIdentity
  registeredReadbackSelectsMolecular :=
    registeredTenFoldReadback_strictlyPrefersMolecularDensity
  everyRegisteredFoldSelectsMolecular :=
    everyRegisteredFold_prefersMolecularDensity
  shellResidualVisible :=
    highResolutionShell_doesNotUniformlyPreferMolecularDensity
  alternativeFitLossReverses :=
    amplitudeL2_hostile_prefersIndependentAtomDensity
  geometryWasFullDataRefined := rfl
  noStatisticallyIndependentHoldout := rfl
  noMetricIndependentSuperiority := rfl
  targetErased := rfl
  geometryOnlyFixture := rfl
  geometryGap := rfl
  noXCWDensity := inferInstance
  noContinuumGlobalCensus := inferInstance
  noAbsoluteBondOntology := inferInstance
  rawEsperantoNotConsumed := inferInstance

end

end LAlanine40K2025.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Producer.physicalBondIncidence_commutes
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Producer.registeredChemicalIncidence_uniqueFactorization
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Producer.sourceGeneratedLAlanine40KPhysicalChemicalBondIncidence_crown
