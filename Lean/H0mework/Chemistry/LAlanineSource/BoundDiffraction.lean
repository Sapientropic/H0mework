import Lean.Data.Json
import Lean.Elab.Command
import H0mework.Cognition.Empirical.Sha256
import H0mework.Chemistry.LAlanineSource.NativeBondDensity

/-! # Target-erased source binding for `lalanine8_40k` -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Source

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
open Interface

private def jsonAt? (value : Lean.Json) : List String → Except String Lean.Json
  | [] => pure value
  | key :: rest => do jsonAt? (← value.getObjVal? key) rest

private def jsonAsAt? (alpha : Type) [Lean.FromJson alpha]
    (value : Lean.Json) (path : List String) : Except String alpha := do
  Lean.fromJson? (← jsonAt? value path)

private def expectStringAt (value : Lean.Json) (path : List String)
    (expected : String) : Except String Unit := do
  let actual ← jsonAsAt? String value path
  unless actual == expected do throw s!"source string {path} changed"

private def expectNatAt (value : Lean.Json) (path : List String)
    (expected : Nat) : Except String Unit := do
  let actual ← jsonAsAt? Nat value path
  unless actual == expected do throw s!"source Nat {path} changed"

private def expectIntAt (value : Lean.Json) (path : List String)
    (expected : Int) : Except String Unit := do
  let actual ← jsonAsAt? Int value path
  unless actual == expected do throw s!"source Int {path} changed"

private def expectBoolAt (value : Lean.Json) (path : List String)
    (expected : Bool) : Except String Unit := do
  let actual ← jsonAsAt? Bool value path
  unless actual == expected do throw s!"source Bool {path} changed"

private def expectStringArraysAt (value : Lean.Json) (path : List String)
    (expected : Array (Array String)) : Except String Unit := do
  let actual ← jsonAsAt? (Array (Array String)) value path
  unless actual == expected do throw s!"source string arrays {path} changed"

private def verifySourceManifest (value : Lean.Json) : Except String Unit := do
  expectStringAt value ["schema"]
    "lalanine40k-target-erased-quantum-bond-density/v1"
  expectStringAt value ["claim_scope"]
    "experimental-nuclear-geometry-blyp-631gd-theoretical-density-finite-search-heavy-pair-bcp-and-deformation-incidence"
  expectStringAt value ["source", "article_doi"]
    "10.1107/S2052252525002647"
  expectStringAt value ["source", "zenodo_doi"]
    "10.5281/zenodo.14688662"
  expectStringAt value ["source", "datablock"] "lalanine8_40k"
  expectStringAt value ["source", "sup1_cif", "sha256"]
    "b706ee653b7b1cf41b1e1361a7b2374cb52ea6041db7c6c3f2d37d670dc3e7db"
  expectNatAt value ["source", "sup1_cif", "bytes"] 2343776
  expectNatAt value ["source", "geometry", "temperature_millikelvin"] 40000
  expectNatAt value ["source", "geometry", "wavelength_femtometer"] 24780
  expectStringAt value ["source", "geometry", "space_group_hm"]
    "P 21 21 21"
  expectNatAt value ["source", "geometry", "space_group_number"] 19
  for entry in [("heavy_atom_count", 6), ("heavy_pair_count", 15),
      ("seed_count", 675)] do
    expectNatAt value ["calculation", "registered_search", entry.1] entry.2
  expectBoolAt value
    ["calculation", "registered_search",
      "continuum_global_exhaustiveness_claimed"] false
  expectStringAt value ["calculation", "method", "functional"] "BLYP"
  expectStringAt value ["calculation", "method", "basis"] "6-31G(d)"
  expectNatAt value ["calculation", "method", "electron_count_micro"]
    48000000
  expectNatAt value
    ["calculation", "method", "independent_atom_electron_count_micro"]
    48000000
  expectIntAt value ["calculation", "method", "scf_energy_nanohartree"]
    (-323451651859)
  expectNatAt value ["calculation", "positive_bcp_count"] 5
  expectStringArraysAt value ["calculation", "positive_bcp_addresses"]
    #[#["C004", "C005"], #["C004", "O001"], #["C004", "O002"],
      #["C005", "C006"], #["C005", "N003"]]
  expectBoolAt value
    ["calculation", "target_erased_hostiles",
      "promolecule_has_same_registered_heavy_pair_bcp_topology"] true
  expectBoolAt value
    ["calculation", "target_erased_hostiles",
      "promolecule_topology_alone_is_not_bond_causality"] true
  for key in ["fobs_consumed_before_bcp_freeze",
      "geom_bond_consumed_before_bcp_freeze",
      "connected_atom_local_axes_consumed",
      "periodic_crystal_environment_modeled",
      "experimental_or_xcw_density_claimed",
      "continuum_global_critical_point_exhaustiveness_claimed",
      "absolute_chemical_bond_ontology_claimed",
      "converted_raw_esperanto_frames_consumed"] do
    expectBoolAt value ["boundaries", key] false

run_cmd do
  let manifestText :=
    include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/source/lalanine40k-source-only-quantum-bond-density.json"
  unless Sha256.hex manifestText ==
      "7b042ae4fb66516165dcbc77fa66dd19e9fa6ea0160a4b99147f7862e2a8ba09" do
    throwError "L-alanine source-only BCP manifest SHA-256 changed"
  let value ← match Lean.Json.parse manifestText with
    | .ok value => pure value
    | .error error => throwError "L-alanine source manifest parse failed: {error}"
  match verifySourceManifest value with
  | .ok () => pure ()
  | .error error => throwError "L-alanine target-erased source rejected: {error}"

def key : LAlanine40KSourceKey :=
  registeredSourceKey

def provenance : LAlanine40KProvenance :=
  { sourceArtifactSha256 :=
      "7b042ae4fb66516165dcbc77fa66dd19e9fa6ea0160a4b99147f7862e2a8ba09"
    evidenceSha256 :=
      "6480c37593da5498d2ffd046e34fb3a886806f0d7b5c898a7c575268c008af78"
    cifSha256 :=
      "b706ee653b7b1cf41b1e1361a7b2374cb52ea6041db7c6c3f2d37d670dc3e7db"
    supportingPdfSha256 :=
      "3954189d11c278a42a5ba78319547e38ea11ee9b81ad460bb474c0e80af01943"
    unmergedSha256 :=
      "95cc8486c00f9f2928d33188969417b1125f34d41b9bbfffa0a026575fe8c799"
    reductionLogSha256 :=
      "3736c3fd80b6ddb31325e0c0b108c4f7cc2a652c7db14ea2ff10fd41fa859b59"
    sourceRuntimeSha256 :=
      "3c73508ecc086b311cc065b420b1f011e6b14af9f762636c403bb9bb1ad005a1"
    densityRuntimeSha256 :=
      "8d79745ab1050959bf9ab8be8ed8e16b61c122258fa7adfcd23c7ad76c58621d"
    diffractionRuntimeSha256 :=
      "e963dae55e4ba27f84fb455bed05429f5ecc8aa91fae3f62f0b579e5b9c7ca5e"
    sourceAdmissionRuntimeSha256 :=
      "b20caaf14b9d6e06d95146a08c74af2cb7119f3776e100233aaadccc3538c26e"
    validationRuntimeSha256 :=
      "5478740c2d8001ea5a2c98f02b33eb8fb99bd71ec01525f9e0ecd4b7da851590"
    pyprojectSha256 :=
      "b147388b2984402d3b020bf49215e953a53304471d355c3c131b2dad884c53bd"
    uvLockSha256 :=
      "27262e03742034045342832aed84adaee58411f84e8917ed2b90e54b87ea622a" }

def observation (distance : Nat) (bcp : Bool)
    (midpointGradient : Nat) (midpointDelta : Int)
    (bcpDensity : Nat) (bcpLaplacian bcpDelta lineIntegral : Int)
    (perpendicular : Nat) : PairPhysicalReadout :=
  { distanceMicroangstrom := distance
    bcpFound := bcp
    midpointGradientNormNano := midpointGradient
    midpointDensityDeltaNano := midpointDelta
    bcpDensityNano := bcpDensity
    bcpLaplacianNano := bcpLaplacian
    bcpDensityDeltaNano := bcpDelta
    lineIntegralDensityDeltaNanoAngstrom := lineIntegral
    perpendicularDistanceMicroangstrom := perpendicular
    pathEndpointsStable := bcp }

def pairReadoutAt : ASUHeavyPair → PairPhysicalReadout
  | .c004C005 => observation 1536621 true 40532889 75644932
      247272356 (-564798545) 72385438 95863019 16145
  | .c004C006 => observation 2526878 false 136839014 (-5807134)
      0 0 0 0 0
  | .c004N003 => observation 2480090 false 133008215 (-11255722)
      0 0 0 0 0
  | .c004O001 => observation 1267857 true 293533897 82690923
      367397560 (-249037294) 86206014 40150033 6841
  | .c004O002 => observation 1250666 true 323292763 88476427
      376136595 2432572 88068527 47410627 6880
  | .c005C006 => observation 1528818 true 22439569 64031202
      242117927 (-523076248) 63055809 77502633 14319
  | .c005N003 => observation 1490750 true 170832204 44071525
      226895573 (-408714129) 6689455 56099548 9796
  | .c005O001 => observation 2380896 false 165786038 (-12016157)
      0 0 0 0 0
  | .c005O002 => observation 2397387 false 179949063 (-7665849)
      0 0 0 0 0
  | .c006N003 => observation 2471132 false 122866061 (-13166527)
      0 0 0 0 0
  | .c006O001 => observation 3084686 false 33824616 (-14725947)
      0 0 0 0 0
  | .c006O002 => observation 3340997 false 87582038 (-9306780)
      0 0 0 0 0
  | .n003O001 => observation 3614505 false 159691882 55734729
      0 0 0 0 0
  | .n003O002 => observation 2685272 false 13195466 (-13434442)
      0 0 0 0 0
  | .o001O002 => observation 2242368 false 231802560 (-15927826)
      0 0 0 0 0

def promoleculeBCPTopologyAt (pair : ASUHeavyPair) : Bool :=
  (pairReadoutAt pair).bcpFound

def calculation : SourceCalculationReadout :=
  { heavyAtomCount := 6
    heavyPairCount := 15
    registeredSeedCount := 675
    positiveBCPCount := 5
    scfEnergyNanohartree := -323451651859
    electronCountMicro := 48000000
    independentAtomElectronCountMicro := 48000000
    maxGradientDerivativeErrorTrillion := 1399
    maxHessianDerivativeErrorTrillion := 2448 }

def boundary : TargetErasureBoundary :=
  { fobsConsumedBeforeFreeze := false
    geomBondConsumedBeforeFreeze := false
    connectedAtomLocalAxesConsumed := false
    periodicCrystalEnvironmentModeled := false
    experimentalOrXCWDensityClaimed := false
    continuumGlobalExhaustivenessClaimed := false
    absoluteBondOntologyClaimed := false
    convertedRawEsperantoConsumed := false }

def sourceRecorded : SourceRecordedTargetErasedDensityAt :=
  { source := key
    provenance := provenance
    calculation := calculation
    pairReadoutAt := pairReadoutAt
    promoleculeBCPTopologyAt := promoleculeBCPTopologyAt
    boundary := boundary }

end LAlanine40K2025.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
