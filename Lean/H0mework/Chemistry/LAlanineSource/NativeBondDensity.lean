/-!
# Source-native carrier for the 40 K L-alanine bond-density occurrence

The occurrence is the complete `lalanine8_40k` diffraction dataset.  Its
target-erased physical face is a fixed finite search over all fifteen
asymmetric-unit heavy-atom pairs.  The published `_geom_bond` incidence and
the diffraction fit are opened only by the later consumer module.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Interface

structure LAlanine40KSourceKey where
  articleDoi : String
  datablock : String
  temperatureMillikelvin : Nat
  wavelengthFemtometer : Nat
  spaceGroup : String
  deriving DecidableEq, Repr

def registeredSourceKey : LAlanine40KSourceKey :=
  { articleDoi := "10.1107/S2052252525002647"
    datablock := "lalanine8_40k"
    temperatureMillikelvin := 40000
    wavelengthFemtometer := 24780
    spaceGroup := "P 21 21 21" }

structure LAlanine40KProvenance where
  sourceArtifactSha256 : String
  evidenceSha256 : String
  cifSha256 : String
  supportingPdfSha256 : String
  unmergedSha256 : String
  reductionLogSha256 : String
  sourceRuntimeSha256 : String
  densityRuntimeSha256 : String
  diffractionRuntimeSha256 : String
  sourceAdmissionRuntimeSha256 : String
  validationRuntimeSha256 : String
  pyprojectSha256 : String
  uvLockSha256 : String
  deriving DecidableEq, Repr

inductive HeavyAtom where
  | c004
  | c005
  | c006
  | n003
  | o001
  | o002
  deriving DecidableEq, Repr

inductive ASUHeavyPair where
  | c004C005
  | c004C006
  | c004N003
  | c004O001
  | c004O002
  | c005C006
  | c005N003
  | c005O001
  | c005O002
  | c006N003
  | c006O001
  | c006O002
  | n003O001
  | n003O002
  | o001O002
  deriving DecidableEq, Repr

def pairEndpoints : ASUHeavyPair → HeavyAtom × HeavyAtom
  | .c004C005 => (.c004, .c005)
  | .c004C006 => (.c004, .c006)
  | .c004N003 => (.c004, .n003)
  | .c004O001 => (.c004, .o001)
  | .c004O002 => (.c004, .o002)
  | .c005C006 => (.c005, .c006)
  | .c005N003 => (.c005, .n003)
  | .c005O001 => (.c005, .o001)
  | .c005O002 => (.c005, .o002)
  | .c006N003 => (.c006, .n003)
  | .c006O001 => (.c006, .o001)
  | .c006O002 => (.c006, .o002)
  | .n003O001 => (.n003, .o001)
  | .n003O002 => (.n003, .o002)
  | .o001O002 => (.o001, .o002)

theorem pairEndpoints_injective : Function.Injective pairEndpoints := by
  intro left right same
  cases left <;> cases right <;> simp_all [pairEndpoints]

structure PairPhysicalReadout where
  distanceMicroangstrom : Nat
  bcpFound : Bool
  midpointGradientNormNano : Nat
  midpointDensityDeltaNano : Int
  bcpDensityNano : Nat
  bcpLaplacianNano : Int
  bcpDensityDeltaNano : Int
  lineIntegralDensityDeltaNanoAngstrom : Int
  perpendicularDistanceMicroangstrom : Nat
  pathEndpointsStable : Bool
  deriving DecidableEq, Repr

structure SourceCalculationReadout where
  heavyAtomCount : Nat
  heavyPairCount : Nat
  registeredSeedCount : Nat
  positiveBCPCount : Nat
  scfEnergyNanohartree : Int
  electronCountMicro : Nat
  independentAtomElectronCountMicro : Nat
  maxGradientDerivativeErrorTrillion : Nat
  maxHessianDerivativeErrorTrillion : Nat
  deriving DecidableEq, Repr

structure TargetErasureBoundary where
  fobsConsumedBeforeFreeze : Bool
  geomBondConsumedBeforeFreeze : Bool
  connectedAtomLocalAxesConsumed : Bool
  periodicCrystalEnvironmentModeled : Bool
  experimentalOrXCWDensityClaimed : Bool
  continuumGlobalExhaustivenessClaimed : Bool
  absoluteBondOntologyClaimed : Bool
  convertedRawEsperantoConsumed : Bool
  deriving DecidableEq, Repr

structure SourceRecordedTargetErasedDensityAt : Type where
  source : LAlanine40KSourceKey
  provenance : LAlanine40KProvenance
  calculation : SourceCalculationReadout
  pairReadoutAt : ASUHeavyPair → PairPhysicalReadout
  promoleculeBCPTopologyAt : ASUHeavyPair → Bool
  boundary : TargetErasureBoundary

structure DiffractionDensityAdjudication where
  embeddedReflectionRows : Nat
  positiveObservedSquaredRows : Nat
  laueClassCount : Nat
  foldCount : Nat
  crossFoldEquivalentClassLeakage : Nat
  molecularCrossValidatedR1Ppb : Nat
  independentAtomCrossValidatedR1Ppb : Nat
  aggregateCrossValidatedMarginPpb : Nat
  minimumFoldMarginPpb : Nat
  maximumFoldMarginPpb : Nat
  everyFoldPrefersMolecularDensity : Bool
  molecularCrossValidatedPearsonPpb : Nat
  independentAtomCrossValidatedPearsonPpb : Nat
  lowResolutionMolecularR1Ppb : Nat
  lowResolutionIndependentAtomR1Ppb : Nat
  highResolutionMolecularR1Ppb : Nat
  highResolutionIndependentAtomR1Ppb : Nat
  amplitudeL2MolecularR1Ppb : Nat
  amplitudeL2IndependentAtomR1Ppb : Nat
  amplitudeL2MolecularMarginPpb : Int
  amplitudeL2UniversallyPrefersMolecularDensity : Bool
  uniformShellDominanceClaimed : Bool
  geometryRefinedAgainstAllReflections : Bool
  statisticallyIndependentHoldoutClaimed : Bool
  metricIndependentModelSuperiorityClaimed : Bool
  deriving DecidableEq, Repr

structure PostFreezeChemicalAdjudication where
  registeredHeavyPairRows : Nat
  computedBCPRows : Nat
  publishedHeavyBondRows : Nat
  computedEqualsPublished : Bool
  sourceGeometryUnchangedAfterBondFieldRemoval : Bool
  diffraction : DiffractionDensityAdjudication
  geometryOnlySeparatesFixture : Bool
  geometryGapMicroangstrom : Nat
  deriving DecidableEq, Repr

inductive DensityArm where
  | molecularBLYP
  | independentAtomSAD
  deriving DecidableEq, Repr

inductive ExperimentalXCWCrystalDensityAt : Type
inductive ContinuumGlobalCriticalPointCensusAt : Type
inductive AbsoluteChemicalBondOntologyAt : Type
inductive ConsumedConvertedRawEsperantoFramesAt : Type

end LAlanine40K2025.Interface
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
