import H0mework.Physics.GravityTail.FixedJointPath

/-!
# Fixed constraint/Cauchy gravity-tail compatible restart

The existing fixed source/current emits a Cartan--EC seed whose coframe is the
identity field.  This module keeps that emitted coframe and regenerates its
connection from the holonomic coframe jet and the same source/action Cartan
response.  It identifies the exact all-point compatibility condition and
proves that condition source-natively on the complete initial Cauchy slice.

Nothing here creates a root occurrence or accepts a target, settlement,
closedness receipt, or caller-supplied coframe jet.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailCompatibleRestart

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeTwoFormPairing
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailCoframeLoadTemporalSpatial01
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailJointPath
open StageNineDiracDualFormNativeFixedP506CartanRestartTemporalElectricKernel
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActualVariationRegularity
open StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalLorentzThreeFormDualInverse
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual

private abbrev Seed : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Current

private abbrev Field (point : BasePoint) : StageNineContinuumPointField :=
  toContinuumPointField (restrictHolonomicConfigurationToIIPlus Seed) point

/-- Fixed source/current-only compatible restart candidate: retain the exact
EC seed coframe and regenerate its connection from that coframe's actual first
jet and the same source/action Cartan response.  Root installation is a
separate same-occurrence responsibility. -/
def fixedSourceGeneratedCompatibleGravityTailBase : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source Seed

theorem fixedGravityTailCompatibleBase_coframe_eq_one :
    fixedSourceGeneratedCompatibleGravityTailBase.coframe = fun _ => (1 : LorentzianCoframe) := by
  rw [fixedSourceGeneratedCompatibleGravityTailBase,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  exact
    fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one

theorem fixedGravityTailCompatibleBase_holonomicCoframeFirstJet_eq_identity
    (point : BasePoint) :
    holonomicCoframeFirstJetAt fixedSourceGeneratedCompatibleGravityTailBase.coframe point =
      identityCoframeMatterGeometry := by
  rw [fixedGravityTailCompatibleBase_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]

theorem fixedGravityTailCompatibleBase_actualTorsion_eq_generated
    (point : BasePoint) :
    actualPointwiseCartanTorsionTwoForm
        (holonomicCoframeFirstJetAt fixedSourceGeneratedCompatibleGravityTailBase.coframe point)
        (fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point) =
      diracDualFormNativeActionCartanTorsionAt Source Seed point := by
  rw [fixedSourceGeneratedCompatibleGravityTailBase,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact diracDualFormNativeActionCartanConnectionAt_actualTorsion
    Source Seed point (by
      rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
      norm_num)

private theorem field_coframe_eq_one (point : BasePoint) :
    (Field point).coframe = 1 := by
  change Seed.coframe point = 1
  rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]

private theorem field_matter_eq_seed (point : BasePoint) :
    (Field point).matter = Seed.matter point :=
  rfl

private theorem field_conjugateMatter_eq_seed (point : BasePoint) :
    (Field point).conjugateMatter = Seed.conjugateMatter point :=
  rfl

private theorem actionCoefficient_normalForm
    (point : BasePoint)
    (variationDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    formNativeLorentzMatterFirstCoefficient Source 0 point (Field point)
        (loweredLorentzBivectorOneFormCoordinate
          variationDirection internalPair) =
      ((Field point).conjugateMatter
        (lorentzSpinActionVector variationDirection internalPair
          (Field point).matter)).re := by
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation generatedVolumeDensity
  rw [field_coframe_eq_one]
  simp only [Matrix.det_one, abs_one, one_mul,
    matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart]
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
        identityCoframeMatterGeometry by rfl]
  simp only [inverseCoframeDiracGamma_identity]
  simp [lorentzSpinActionVector, Fin.sum_univ_four]

private theorem actionSpinResponse_coordinate_normalForm
    (point : BasePoint) (internalPair : Fin 6) (triple : Fin 4) :
    diracDualFormNativeActionSpinResponseAt Source Seed point
        internalPair triple =
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        ((Field point).conjugateMatter
          (lorentzSpinActionVector (missingTripleOfOneForm triple)
            internalPair (Field point).matter)).re) := by
  unfold diracDualFormNativeActionSpinResponseAt
    formNativePhysicalSpinCurrentThreeForm
  change
    -(formNativeMatterSpinThreeForm Source 0 point (Field point)
        internalPair triple) = _
  rw [show
      formNativeMatterSpinThreeForm Source 0 point (Field point)
          internalPair triple =
        oneWedgeThreeSign (missingTripleOfOneForm triple) *
          formNativeLorentzMatterFirstCoefficient Source 0 point
            (Field point)
            (loweredLorentzBivectorOneFormCoordinate
              (missingTripleOfOneForm triple) internalPair) by
    simpa using
      formNativeMatterSpinThreeForm_coordinate Source 0 point (Field point)
        (missingTripleOfOneForm triple) internalPair]
  rw [actionCoefficient_normalForm]

private theorem identityJet_loweredLeviCivitaVector_eq_zero
    (first second : LorentzianIndex) :
    identityCoframeMatterGeometry.loweredLeviCivitaVector first second = 0 := by
  funext internal
  simp [PointwiseLorentzianCoframeJet.loweredLeviCivitaVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
    PointwiseLorentzianCoframeJet.metricDerivative,
    identityCoframeMatterGeometry]

private theorem identityJet_leviCivitaConnection_eq_zero :
    identityCoframeMatterGeometry.leviCivitaConnection = 0 := by
  funext upper first second
  unfold PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
  rw [identityJet_loweredLeviCivitaVector_eq_zero]
  simp

private theorem identityJet_coordinateConnectionMatrix_eq_zero
    (direction : LorentzianIndex) :
    identityCoframeMatterGeometry.coordinateConnectionMatrix direction = 0 := by
  unfold PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
  rw [identityJet_leviCivitaConnection_eq_zero]
  rfl

private theorem identityJet_lorentzSpinConnection_eq_zero :
    identityCoframeMatterGeometry.lorentzSpinConnection = 0 := by
  funext formDirection internalOut internalIn
  change identityCoframeMatterGeometry.lorentzSpinConnectionMatrix
      formDirection internalOut internalIn = 0
  unfold PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
  rw [identityJet_coordinateConnectionMatrix_eq_zero]
  simp [PointwiseLorentzianCoframeJet.coframeDerivativeMatrix,
    identityCoframeMatterGeometry]

private theorem fixedGravityTailCompatibleBase_connection_eq_actionContorsion
    (point : BasePoint) :
    fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point =
      lorentzSkewConnectionOfBivectorOneForm
        (diracDualFormNativeActionCartanContorsionAt Source Seed point) := by
  rw [fixedSourceGeneratedCompatibleGravityTailBase,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection
  dsimp only
  rw [show holonomicCoframeFirstJetAt Seed.coframe point =
      identityCoframeMatterGeometry by
    rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
    apply coframeJet_eq_of_fields_eq
    · rfl
    · funext derivativeDirection internal coordinate
      simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry],
    identityJet_lorentzSpinConnection_eq_zero]
  simp

private theorem positiveActual_coframe_one (point : BasePoint) :
    positiveSourceTargetMatterActual.coframe point = 1 := by
  rw [positiveSourceTargetMatterActual,
    sourceActionGeneratedJointLocalActualLift_coframe_at]
  change positivePhaseProbeCauchyState.coframe 0 = 1
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

private theorem seed_spinResponse_zeroSlice_eq_positive
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionSpinResponseAt Source Seed
        (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeActionSpinResponseAt Source
        positiveSourceTargetMatterActual 0 := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  · calc
      Seed.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
        rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
      _ = positiveSourceTargetMatterActual.coframe 0 :=
        (positiveActual_coframe_one 0).symm
  · change
      fixedP506L0CartanECCauchyTemporalInput.matter
          (canonicalCauchySlicePoint 0 space) =
        positiveSourceTargetMatterActual.matter 0
    calc
      _ = diracSpinTwoMatterProbe :=
        fixedP506L0ActionSelectedGravityTailBase_matter_zeroSlice_constant
          space
      _ = positiveSourceTargetMatterCauchyState.matter 0 :=
        positiveSourceTargetMatterCauchyState_matter.symm
      _ = _ :=
        (sourceActionGeneratedJointLocalActualLift_initialMatter
          Source positiveSourceTargetMatterCauchyState 0).symm
  · change
      fixedP506L0CartanECCauchyTemporalInput.conjugateMatter
          (canonicalCauchySlicePoint 0 space) =
        positiveSourceTargetMatterActual.conjugateMatter 0
    calc
      _ = diracSpinZeroMatterCoordinate :=
        fixedP506L0ActionSelectedGravityTailBase_conjugateMatter_zeroSlice_constant
          space
      _ = positiveSourceTargetMatterCauchyState.conjugateMatter 0 :=
        positiveSourceTargetMatterCauchyState_conjugate.symm
      _ = _ :=
        (sourceActionGeneratedJointLocalActualLift_initialConjugateMatter
          Source positiveSourceTargetMatterCauchyState 0).symm

theorem fixedGravityTailCompatibleBase_actionContorsion_zeroSlice_eq_positiveNormalForm
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionCartanContorsionAt Source Seed
        (canonicalCauchySlicePoint 0 space) =
      positiveDiracDualCartanContorsionNormalForm := by
  calc
    _ = diracDualFormNativeActionCartanContorsionAt Source
          positiveSourceTargetMatterActual 0 := by
      unfold diracDualFormNativeActionCartanContorsionAt
        diracDualFormNativeActionCartanTorsionAt
      rw [show Seed.coframe (canonicalCauchySlicePoint 0 space) =
          positiveSourceTargetMatterActual.coframe 0 by
        calc
          _ = 1 := by
            rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
          _ = _ := (positiveActual_coframe_one 0).symm,
        seed_spinResponse_zeroSlice_eq_positive]
    _ = _ := fixedActionCartanContorsion_eq_positiveNormalForm

private theorem positiveNormal_lift_crossAntisymmetric
    (first internal second : LorentzianIndex) :
    lorentzSkewConnectionOfBivectorOneForm
          positiveDiracDualCartanContorsionNormalForm
          first internal second =
      -lorentzSkewConnectionOfBivectorOneForm
          positiveDiracDualCartanContorsionNormalForm
          second internal first := by
  fin_cases first <;> fin_cases internal <;> fin_cases second <;>
    simp [positiveDiracDualCartanContorsionNormalForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.sum_univ_six]

theorem fixedGravityTailCompatibleBase_connection_zeroSlice_eq_positiveNormalForm
    (space : StageNineSpatialPoint) :
    fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection (canonicalCauchySlicePoint 0 space) =
      lorentzSkewConnectionOfBivectorOneForm
        positiveDiracDualCartanContorsionNormalForm := by
  rw [fixedSourceGeneratedCompatibleGravityTailBase,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection
  change
    (holonomicCoframeFirstJetAt Seed.coframe
          (canonicalCauchySlicePoint 0 space)).lorentzSpinConnection +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt Source Seed
            (canonicalCauchySlicePoint 0 space)) =
      lorentzSkewConnectionOfBivectorOneForm
        positiveDiracDualCartanContorsionNormalForm
  rw [show holonomicCoframeFirstJetAt Seed.coframe
      (canonicalCauchySlicePoint 0 space) = identityCoframeMatterGeometry by
    rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
    apply coframeJet_eq_of_fields_eq
    · rfl
    · funext derivativeDirection internal coordinate
      simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]]
  rw [identityJet_lorentzSpinConnection_eq_zero,
    fixedGravityTailCompatibleBase_actionContorsion_zeroSlice_eq_positiveNormalForm]
  simp

theorem fixedGravityTailCompatibleBase_connection_zeroSlice_crossAntisymmetric
    (space : StageNineSpatialPoint)
    (first internal second : LorentzianIndex) :
    fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection (canonicalCauchySlicePoint 0 space)
          first internal second =
      -fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection (canonicalCauchySlicePoint 0 space)
          second internal first := by
  rw [fixedGravityTailCompatibleBase_connection_zeroSlice_eq_positiveNormalForm]
  exact positiveNormal_lift_crossAntisymmetric first internal second

/-- The lexicographically first nontrivial all-point cross component is
exactly one fixed primal/adjoint matter trace law.  This exposes the first
missing physical producer without accepting the trace value as an input to
the restart. -/
theorem
    fixedGravityTailCompatibleBase_connection_crossAntisymmetric_001_iff_matterTrace
    (point : BasePoint) :
    fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
        0 0 1 =
        -fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          1 0 0 ↔
      (fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter point
          (lorentzSpinActionVector 0 0
            (fixedSourceGeneratedCompatibleGravityTailBase.matter point))).re -
        (fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter point
          (lorentzSpinActionVector 2 5
            (fixedSourceGeneratedCompatibleGravityTailBase.matter point))).re +
      (fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter point
          (lorentzSpinActionVector 3 4
            (fixedSourceGeneratedCompatibleGravityTailBase.matter point))).re =
        0 := by
  rw [fixedGravityTailCompatibleBase_connection_eq_actionContorsion]
  rw [show fixedSourceGeneratedCompatibleGravityTailBase.matter =
      Seed.matter by rfl,
    show fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter =
      Seed.conjugateMatter by rfl]
  unfold diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  simp [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    contorsionOfCartanTorsion, internalFrameContorsionOfTorsion,
    minkowskiRaiseCartanTorsion,
    pullbackCartanTorsionTwoForm,
    pushforwardLorentzBivectorOneForm,
    cartanTorsionOfThreeForm, cartanTorsionOfUndualThreeForm,
    cartanThreeFormFirstContraction,
    cartanThreeFormDoubleContraction,
    internalBivectorUndualThreeForm,
    orderedPhysicalBivectorThreeFormComponent,
    orderedInternalBivectorThreeFormComponent,
    orderedCartanTorsionComponent,
    orientedLorentzThreeFormBasisCoefficient,
    pairFirst, pairSecond, threeFormFirst, threeFormSecond,
    threeFormThird, lorentzianCoframeHodge,
    StageNineGlobalIntegratedAction.coframeTwoFormLinear,
    coframeWedge,
    Fin.sum_univ_four, Fin.sum_univ_six, Matrix.one_apply,
    fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
  simp_rw [actionSpinResponse_coordinate_normalForm]
  simp [missingTripleOfOneForm, oneWedgeThreeSign]
  ring_nf
  simp [Field, toContinuumPointField,
    restrictHolonomicConfigurationToIIPlus]

private theorem lorentzSpinActionVector_trace002_normalForm
    (matter : DiracExteriorMatterCarrier) :
    lorentzSpinActionVector 0 1 matter +
        lorentzSpinActionVector 1 5 matter -
      lorentzSpinActionVector 3 3 matter =
        (Complex.I / 2) •
          diracMatrixMatterAction (diracGamma 2) matter := by
  unfold lorentzSpinActionVector
  funext spinIndex
  simp [loweredLorentzBivectorOneFormCoordinate,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction,
    Fin.sum_univ_four, Fin.sum_univ_six,
    lorentzBivectorFirst, lorentzBivectorSecond,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree]
  fin_cases spinIndex <;>
    simp [smul_smul, ← mul_assoc] <;>
    module

private theorem lorentzSpinActionVector_trace002_pairing_normalForm
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier) :
    (dual (lorentzSpinActionVector 0 1 matter)).re +
        (dual (lorentzSpinActionVector 1 5 matter)).re -
      (dual (lorentzSpinActionVector 3 3 matter)).re =
        -((1 : ℝ) / 2) *
          (dual (diracMatrixMatterAction (diracGamma 2) matter)).im := by
  have vectorEq := congrArg dual
    (lorentzSpinActionVector_trace002_normalForm matter)
  have realEq := congrArg Complex.re vectorEq
  simp only [map_add, map_sub, map_smul, Complex.add_re,
    Complex.sub_re] at realEq
  rw [realEq]
  simp [Complex.mul_re]

private theorem lorentzSpinActionVector_trace003_normalForm
    (matter : DiracExteriorMatterCarrier) :
    lorentzSpinActionVector 0 2 matter -
        lorentzSpinActionVector 1 4 matter +
      lorentzSpinActionVector 2 3 matter =
        (Complex.I / 2) •
          diracMatrixMatterAction (diracGamma 3) matter := by
  unfold lorentzSpinActionVector
  funext spinIndex
  simp [loweredLorentzBivectorOneFormCoordinate,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction,
    Fin.sum_univ_four, Fin.sum_univ_six,
    lorentzBivectorFirst, lorentzBivectorSecond,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree]
  fin_cases spinIndex <;>
    simp [smul_smul, ← mul_assoc] <;>
    module

private theorem lorentzSpinActionVector_trace003_pairing_normalForm
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier) :
    (dual (lorentzSpinActionVector 0 2 matter)).re -
        (dual (lorentzSpinActionVector 1 4 matter)).re +
      (dual (lorentzSpinActionVector 2 3 matter)).re =
        -((1 : ℝ) / 2) *
          (dual (diracMatrixMatterAction (diracGamma 3) matter)).im := by
  have vectorEq := congrArg dual
    (lorentzSpinActionVector_trace003_normalForm matter)
  have realEq := congrArg Complex.re vectorEq
  simp only [map_add, map_sub, map_smul, Complex.add_re,
    Complex.sub_re] at realEq
  rw [realEq]
  simp [Complex.mul_re]

private theorem lorentzSpinActionVector_trace110_normalForm
    (matter : DiracExteriorMatterCarrier) :
    lorentzSpinActionVector 3 2 matter +
        lorentzSpinActionVector 2 1 matter -
      lorentzSpinActionVector 1 0 matter =
        (-(Complex.I / 2)) •
          diracMatrixMatterAction (diracGamma 0) matter := by
  unfold lorentzSpinActionVector
  funext spinIndex
  simp [loweredLorentzBivectorOneFormCoordinate,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction,
    Fin.sum_univ_four, Fin.sum_univ_six,
    lorentzBivectorFirst, lorentzBivectorSecond,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree]
  fin_cases spinIndex <;>
    simp [smul_smul, ← mul_assoc, Complex.I_mul_I] <;>
    module

private theorem lorentzSpinActionVector_trace110_pairing_normalForm
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier) :
    (dual (lorentzSpinActionVector 3 2 matter)).re +
        (dual (lorentzSpinActionVector 2 1 matter)).re -
      (dual (lorentzSpinActionVector 1 0 matter)).re =
        ((1 : ℝ) / 2) *
          (dual (diracMatrixMatterAction (diracGamma 0) matter)).im := by
  have vectorEq := congrArg dual
    (lorentzSpinActionVector_trace110_normalForm matter)
  have realEq := congrArg Complex.re vectorEq
  simp only [map_add, map_sub, map_smul, Complex.add_re,
    Complex.sub_re] at realEq
  rw [realEq]
  simp [Complex.mul_re]


private theorem lorentzSpinActionVector_trace001_normalForm
    (matter : DiracExteriorMatterCarrier) :
    lorentzSpinActionVector 0 0 matter -
        lorentzSpinActionVector 2 5 matter +
      lorentzSpinActionVector 3 4 matter =
        (Complex.I / 2) •
          diracMatrixMatterAction (diracGamma 1) matter := by
  unfold lorentzSpinActionVector
  funext spinIndex
  simp [loweredLorentzBivectorOneFormCoordinate,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction,
    Fin.sum_univ_four, Fin.sum_univ_six,
    lorentzBivectorFirst, lorentzBivectorSecond,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree]
  fin_cases spinIndex <;>
    simp [smul_smul, ← mul_assoc, Complex.I_mul_I] <;>
    module

private theorem lorentzSpinActionVector_trace001_pairing_normalForm
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier) :
    (dual (lorentzSpinActionVector 0 0 matter)).re -
        (dual (lorentzSpinActionVector 2 5 matter)).re +
      (dual (lorentzSpinActionVector 3 4 matter)).re =
        -((1 : ℝ) / 2) *
          (dual (diracMatrixMatterAction (diracGamma 1) matter)).im := by
  have vectorEq := congrArg dual
    (lorentzSpinActionVector_trace001_normalForm matter)
  have realEq := congrArg Complex.re vectorEq
  simp only [map_add, map_sub, map_smul, Complex.add_re,
    Complex.sub_re] at realEq
  rw [realEq]
  simp [Complex.mul_re]

/-- The first all-point contact obstruction is precisely the imaginary part
of the fixed spatial Dirac vector current.  Its missing producer is therefore
a physical primal/adjoint reality invariant, not a generic radial or Cartan
closedness premise. -/
theorem
    fixedGravityTailCompatibleBase_connection_crossAntisymmetric_001_iff_spatialDiracCurrentReal
    (point : BasePoint) :
    fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
        0 0 1 =
        -fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          1 0 0 ↔
      (fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter point
        (diracMatrixMatterAction (diracGamma 1)
          (fixedSourceGeneratedCompatibleGravityTailBase.matter point))).im =
        0 := by
  rw [fixedGravityTailCompatibleBase_connection_crossAntisymmetric_001_iff_matterTrace]
  rw [lorentzSpinActionVector_trace001_pairing_normalForm]
  constructor <;> intro equality
  · linarith
  · rw [equality]
    norm_num

private def compatibleCurrentRepresentativeFirst :
    LorentzianIndex → LorentzianIndex := ![1, 0, 0, 0]

private def compatibleCurrentRepresentativeInternal :
    LorentzianIndex → LorentzianIndex := ![1, 0, 0, 0]

private def compatibleCurrentRepresentativeSecond :
    LorentzianIndex → LorentzianIndex := ![0, 1, 2, 3]

private def compatibleCurrentMatterTrace
    (point : BasePoint) : LorentzianIndex → ℝ :=
  ![
    (Seed.conjugateMatter point
        (lorentzSpinActionVector 3 2 (Seed.matter point))).re +
      (Seed.conjugateMatter point
        (lorentzSpinActionVector 2 1 (Seed.matter point))).re -
      (Seed.conjugateMatter point
        (lorentzSpinActionVector 1 0 (Seed.matter point))).re,
    (Seed.conjugateMatter point
        (lorentzSpinActionVector 0 0 (Seed.matter point))).re -
      (Seed.conjugateMatter point
        (lorentzSpinActionVector 2 5 (Seed.matter point))).re +
      (Seed.conjugateMatter point
        (lorentzSpinActionVector 3 4 (Seed.matter point))).re,
    (Seed.conjugateMatter point
        (lorentzSpinActionVector 0 1 (Seed.matter point))).re +
      (Seed.conjugateMatter point
        (lorentzSpinActionVector 1 5 (Seed.matter point))).re -
      (Seed.conjugateMatter point
        (lorentzSpinActionVector 3 3 (Seed.matter point))).re,
    (Seed.conjugateMatter point
        (lorentzSpinActionVector 0 2 (Seed.matter point))).re -
      (Seed.conjugateMatter point
        (lorentzSpinActionVector 1 4 (Seed.matter point))).re +
      (Seed.conjugateMatter point
        (lorentzSpinActionVector 2 3 (Seed.matter point))).re]

private theorem compatibleCurrentRepresentative_crossAntisymmetric_iff_trace
    (point : BasePoint) (direction : LorentzianIndex) :
    fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          (compatibleCurrentRepresentativeFirst direction)
          (compatibleCurrentRepresentativeInternal direction)
          (compatibleCurrentRepresentativeSecond direction) =
        -fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          (compatibleCurrentRepresentativeSecond direction)
          (compatibleCurrentRepresentativeInternal direction)
          (compatibleCurrentRepresentativeFirst direction) ↔
      compatibleCurrentMatterTrace point direction = 0 := by
  rw [fixedGravityTailCompatibleBase_connection_eq_actionContorsion]
  fin_cases direction <;>
    unfold diracDualFormNativeActionCartanContorsionAt
      diracDualFormNativeActionCartanTorsionAt <;>
    simp [lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      contorsionOfCartanTorsion, internalFrameContorsionOfTorsion,
      minkowskiRaiseCartanTorsion,
      pullbackCartanTorsionTwoForm,
      pushforwardLorentzBivectorOneForm,
      cartanTorsionOfThreeForm, cartanTorsionOfUndualThreeForm,
      cartanThreeFormFirstContraction,
      cartanThreeFormDoubleContraction,
      internalBivectorUndualThreeForm,
      orderedPhysicalBivectorThreeFormComponent,
      orderedInternalBivectorThreeFormComponent,
      orderedCartanTorsionComponent,
      orientedLorentzThreeFormBasisCoefficient,
      pairFirst, pairSecond, threeFormFirst, threeFormSecond,
      threeFormThird, lorentzianCoframeHodge,
      StageNineGlobalIntegratedAction.coframeTwoFormLinear,
      coframeWedge,
      Fin.sum_univ_four, Fin.sum_univ_six, Matrix.one_apply,
      fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one,
      compatibleCurrentRepresentativeFirst,
      compatibleCurrentRepresentativeInternal,
      compatibleCurrentRepresentativeSecond] <;>
    simp_rw [actionSpinResponse_coordinate_normalForm] <;>
    simp [missingTripleOfOneForm, oneWedgeThreeSign,
      compatibleCurrentMatterTrace] <;>
    ring_nf <;>
    simp [Field, toContinuumPointField,
      restrictHolonomicConfigurationToIIPlus]
  · constructor <;> intro equality <;> linarith

/-- Four fixed representative cross components are exactly the four
Dirac-vector-current reality coordinates generated by the same compatible
restart.  This is a finite Clifford quotient; it accepts no current value or
connection settlement from the caller. -/
private theorem fixedGravityTailCompatibleBase_connectionRepresentative_iff_diracCurrentReal
    (point : BasePoint) (direction : LorentzianIndex) :
    fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          (compatibleCurrentRepresentativeFirst direction)
          (compatibleCurrentRepresentativeInternal direction)
          (compatibleCurrentRepresentativeSecond direction) =
        -fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          (compatibleCurrentRepresentativeSecond direction)
          (compatibleCurrentRepresentativeInternal direction)
          (compatibleCurrentRepresentativeFirst direction) ↔
      (fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter point
        (diracMatrixMatterAction (diracGamma direction)
          (fixedSourceGeneratedCompatibleGravityTailBase.matter point))).im =
        0 := by
  rw [compatibleCurrentRepresentative_crossAntisymmetric_iff_trace]
  rw [show fixedSourceGeneratedCompatibleGravityTailBase.matter =
        Seed.matter by rfl,
    show fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter =
        Seed.conjugateMatter by rfl]
  fin_cases direction
  · simp [compatibleCurrentMatterTrace, diracGamma]
    rw [lorentzSpinActionVector_trace110_pairing_normalForm]
    norm_num [diracGamma, Matrix.cons_val_two, Matrix.cons_val_three]
  · simp [compatibleCurrentMatterTrace, diracGamma]
    rw [lorentzSpinActionVector_trace001_pairing_normalForm]
    norm_num [diracGamma, Matrix.cons_val_two, Matrix.cons_val_three]
  · simp [compatibleCurrentMatterTrace, diracGamma]
    rw [lorentzSpinActionVector_trace002_pairing_normalForm]
    norm_num [diracGamma, Matrix.cons_val_two, Matrix.cons_val_three]
  · simp [compatibleCurrentMatterTrace, diracGamma]
    rw [lorentzSpinActionVector_trace003_pairing_normalForm]
    norm_num [diracGamma, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Theorem-level readout: complete contact compatibility forces reality of
every fixed Dirac-vector current coordinate.  The four representatives are
selected internally from the generated connection; this implication is not a
contact-settlement producer. -/
theorem fixedGravityTailCompatibleBase_connectionCrossAntisymmetric_implies_diracCurrentReal
    (point : BasePoint)
    (cross : ∀ first internal second,
      fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          first internal second =
        -fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          second internal first) :
    ∀ direction : LorentzianIndex,
      (fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter point
        (diracMatrixMatterAction (diracGamma direction)
          (fixedSourceGeneratedCompatibleGravityTailBase.matter point))).im =
        0 := by
  intro direction
  exact
    (fixedGravityTailCompatibleBase_connectionRepresentative_iff_diracCurrentReal
      point direction).mp
      (cross (compatibleCurrentRepresentativeFirst direction)
        (compatibleCurrentRepresentativeInternal direction)
        (compatibleCurrentRepresentativeSecond direction))

/-! ## Finite Clifford--Cartan reverse fold -/

private theorem lorentzSpinActionVector_generic_normalForm
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    lorentzSpinActionVector variationDirection internalPair matter =
      Complex.I •
        diracMatrixMatterAction (diracGamma variationDirection)
          (diracMatrixMatterAction
            (((2 : ℂ)⁻¹) •
              (diracGamma (lorentzBivectorFirst internalPair) *
                diracGamma (lorentzBivectorSecond internalPair)))
            matter) := by
  unfold lorentzSpinActionVector diracSpinConnectionLift
  rw [Finset.sum_eq_single variationDirection]
  · rw [Finset.sum_eq_single internalPair]
    · simp [loweredLorentzConnectionCoefficient_ofBivectorOneForm,
        loweredLorentzBivectorOneFormCoordinate]
    · intro pair _ pairNe
      simp [loweredLorentzConnectionCoefficient_ofBivectorOneForm,
        loweredLorentzBivectorOneFormCoordinate, pairNe]
    · simp
  · intro direction _ directionNe
    simp [loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      loweredLorentzBivectorOneFormCoordinate, directionNe]
  · simp

private theorem lorentzSpinActionVector_triple_normalForm
    (direction : LorentzianIndex) (internalPair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    lorentzSpinActionVector direction internalPair matter =
      (Complex.I * (2 : ℂ)⁻¹) •
        diracMatrixMatterAction
          ((diracGamma direction *
              diracGamma (lorentzBivectorFirst internalPair)) *
            diracGamma (lorentzBivectorSecond internalPair))
          matter := by
  rw [lorentzSpinActionVector_generic_normalForm]
  rw [diracMatrixMatterAction_smul_matrix, map_smul]
  rw [← LinearMap.comp_apply,
    ← SU7ExteriorBreakingYukawa.diracMatrixMatterAction_mul]
  rw [smul_smul]
  rw [Matrix.mul_assoc]

private def diracTripleAlternatingMatrix
    (first second third : LorentzianIndex) : DiracMatrix :=
  (diracGamma first * diracGamma second) * diracGamma third -
    complexMinkowskiEntry first second • diracGamma third +
    complexMinkowskiEntry third first • diracGamma second -
    complexMinkowskiEntry second third • diracGamma first

private theorem complexMinkowskiEntry_comm
    (first second : LorentzianIndex) :
    complexMinkowskiEntry first second =
      complexMinkowskiEntry second first := by
  fin_cases first <;> fin_cases second <;>
    norm_num [complexMinkowskiEntry, minkowskiInternalMetric]

private theorem diracGamma_triple_decomposition
    (first second third : LorentzianIndex) :
    (diracGamma first * diracGamma second) * diracGamma third =
      diracTripleAlternatingMatrix first second third +
        complexMinkowskiEntry first second • diracGamma third -
        complexMinkowskiEntry third first • diracGamma second +
        complexMinkowskiEntry second third • diracGamma first := by
  unfold diracTripleAlternatingMatrix
  module

private theorem diracGamma_triple_outer_sum
    (first second third : LorentzianIndex) :
    (diracGamma first * diracGamma second) * diracGamma third +
        (diracGamma third * diracGamma second) * diracGamma first =
      (2 * complexMinkowskiEntry second third) • diracGamma first -
        (2 * complexMinkowskiEntry third first) • diracGamma second +
        (2 * complexMinkowskiEntry first second) • diracGamma third := by
  calc
    _ = diracMatrixCommutator
          (diracGamma first * diracGamma second) (diracGamma third) +
        diracGamma third *
          (diracGamma first * diracGamma second +
            diracGamma second * diracGamma first) := by
      rw [diracMatrixCommutator]
      noncomm_ring
    _ = _ := by
      rw [diracGamma_bivector_commutator, diracGamma_clifford]
      simp

private theorem diracTripleAlternatingMatrix_swap_outer
    (first second third : LorentzianIndex) :
    diracTripleAlternatingMatrix first second third =
      -diracTripleAlternatingMatrix third second first := by
  apply eq_neg_of_add_eq_zero_left
  have outer := diracGamma_triple_outer_sum first second third
  have h12 := complexMinkowskiEntry_comm first second
  have h13 := complexMinkowskiEntry_comm first third
  have h23 := complexMinkowskiEntry_comm second third
  unfold diracTripleAlternatingMatrix
  calc
    _ = ((diracGamma first * diracGamma second) * diracGamma third +
          (diracGamma third * diracGamma second) * diracGamma first) -
        ((2 * complexMinkowskiEntry second third) • diracGamma first -
          (2 * complexMinkowskiEntry third first) • diracGamma second +
          (2 * complexMinkowskiEntry first second) • diracGamma third) := by
      rw [h12, h13, h23]
      module
    _ = 0 := by rw [outer]; module

private theorem diracGamma_triple_last_sum
    (first second third : LorentzianIndex) :
    (diracGamma first * diracGamma second) * diracGamma third +
        (diracGamma first * diracGamma third) * diracGamma second =
      (2 * complexMinkowskiEntry second third) • diracGamma first := by
  calc
    _ = diracGamma first *
        (diracGamma second * diracGamma third +
          diracGamma third * diracGamma second) := by
      noncomm_ring
    _ = _ := by
      rw [diracGamma_clifford]
      simp

private theorem diracTripleAlternatingMatrix_swap_last
    (first second third : LorentzianIndex) :
    diracTripleAlternatingMatrix first second third =
      -diracTripleAlternatingMatrix first third second := by
  apply eq_neg_of_add_eq_zero_left
  have tripleSum := diracGamma_triple_last_sum first second third
  have h12 := complexMinkowskiEntry_comm first second
  have h13 := complexMinkowskiEntry_comm first third
  have h23 := complexMinkowskiEntry_comm second third
  unfold diracTripleAlternatingMatrix
  calc
    _ = ((diracGamma first * diracGamma second) * diracGamma third +
          (diracGamma first * diracGamma third) * diracGamma second) -
        (2 * complexMinkowskiEntry second third) • diracGamma first := by
      rw [h12, h13, h23]
      module
    _ = 0 := by rw [tripleSum]; module

private theorem diracMatrixMatterAction_neg_matrix
    (matrix : DiracMatrix) (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (-matrix) matter =
      -diracMatrixMatterAction matrix matter := by
  calc
    diracMatrixMatterAction (-matrix) matter =
        diracMatrixMatterAction (0 - matrix) matter := by rw [zero_sub]
    _ = diracMatrixMatterAction 0 matter -
        diracMatrixMatterAction matrix matter :=
      StageNineDiracMatterCoordinateCalculus.diracMatrixMatterAction_sub_matrix
        0 matrix matter
    _ = -diracMatrixMatterAction matrix matter := by
      rw [show diracMatrixMatterAction 0 matter = 0 by
        funext row
        simp [diracMatrixMatterAction]]
      exact zero_sub _

private def axialLorentzSpinActionVector
    (first second third : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier :=
  (Complex.I * (2 : ℂ)⁻¹) •
    diracMatrixMatterAction
      (diracTripleAlternatingMatrix first second third) matter

private theorem lorentzSpinActionVector_decomposition
    (direction : LorentzianIndex) (internalPair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    lorentzSpinActionVector direction internalPair matter =
      axialLorentzSpinActionVector direction
          (lorentzBivectorFirst internalPair)
          (lorentzBivectorSecond internalPair) matter +
        (Complex.I * (2 : ℂ)⁻¹ *
            complexMinkowskiEntry direction
              (lorentzBivectorFirst internalPair)) •
          diracMatrixMatterAction
            (diracGamma (lorentzBivectorSecond internalPair)) matter -
        (Complex.I * (2 : ℂ)⁻¹ *
            complexMinkowskiEntry (lorentzBivectorSecond internalPair)
              direction) •
          diracMatrixMatterAction
            (diracGamma (lorentzBivectorFirst internalPair)) matter +
        (Complex.I * (2 : ℂ)⁻¹ *
            complexMinkowskiEntry (lorentzBivectorFirst internalPair)
              (lorentzBivectorSecond internalPair)) •
          diracMatrixMatterAction (diracGamma direction) matter := by
  rw [lorentzSpinActionVector_triple_normalForm,
    diracGamma_triple_decomposition]
  simp only [
    StageNineLorentzConnectionActualVariationRegularity.diracMatrixMatterAction_add_matrix,
    StageNineDiracMatterCoordinateCalculus.diracMatrixMatterAction_sub_matrix,
    StageNineLorentzConnectionActualVariationRegularity.diracMatrixMatterAction_smul_matrix,
    smul_add, smul_sub, smul_smul]
  unfold axialLorentzSpinActionVector
  module

private theorem axialLorentzSpinActionVector_swap_outer
    (first second third : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    axialLorentzSpinActionVector first second third matter =
      -axialLorentzSpinActionVector third second first matter := by
  unfold axialLorentzSpinActionVector
  rw [diracTripleAlternatingMatrix_swap_outer,
    diracMatrixMatterAction_neg_matrix]
  simp

private theorem axialLorentzSpinActionVector_swap_last
    (first second third : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    axialLorentzSpinActionVector first second third matter =
      -axialLorentzSpinActionVector first third second matter := by
  unfold axialLorentzSpinActionVector
  rw [diracTripleAlternatingMatrix_swap_last,
    diracMatrixMatterAction_neg_matrix]
  simp

private theorem imaginaryMetricGamma_pairing_re_zero
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier)
    (currentReal : ∀ direction : LorentzianIndex,
      (dual (diracMatrixMatterAction (diracGamma direction) matter)).im = 0)
    (metricFirst metricSecond direction : LorentzianIndex) :
    (dual
      ((Complex.I * (2 : ℂ)⁻¹ *
          complexMinkowskiEntry metricFirst metricSecond) •
        diracMatrixMatterAction (diracGamma direction) matter)).re = 0 := by
  rw [map_smul]
  have real := currentReal direction
  fin_cases metricFirst <;> fin_cases metricSecond <;>
    norm_num [complexMinkowskiEntry, minkowskiInternalMetric] at real ⊢ <;>
    exact real

private theorem lorentzSpinActionPairing_eq_axial_of_currentReal
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier)
    (currentReal : ∀ direction : LorentzianIndex,
      (dual (diracMatrixMatterAction (diracGamma direction) matter)).im = 0)
    (direction : LorentzianIndex) (internalPair : Fin 6) :
    (dual (lorentzSpinActionVector direction internalPair matter)).re =
      (dual (axialLorentzSpinActionVector direction
        (lorentzBivectorFirst internalPair)
        (lorentzBivectorSecond internalPair) matter)).re := by
  rw [lorentzSpinActionVector_decomposition, map_add, map_sub, map_add]
  simp only [Complex.add_re, Complex.sub_re]
  rw [imaginaryMetricGamma_pairing_re_zero dual matter currentReal,
    imaginaryMetricGamma_pairing_re_zero dual matter currentReal,
    imaginaryMetricGamma_pairing_re_zero dual matter currentReal]
  ring

private theorem axialLorentzSpinActionPairing_swap_outer
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier)
    (first second third : LorentzianIndex) :
    (dual (axialLorentzSpinActionVector first second third matter)).re =
      -(dual (axialLorentzSpinActionVector third second first matter)).re := by
  rw [axialLorentzSpinActionVector_swap_outer, map_neg, Complex.neg_re]

private theorem axialLorentzSpinActionPairing_swap_last
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier)
    (first second third : LorentzianIndex) :
    (dual (axialLorentzSpinActionVector first second third matter)).re =
      -(dual (axialLorentzSpinActionVector first third second matter)).re := by
  rw [axialLorentzSpinActionVector_swap_last, map_neg, Complex.neg_re]

private theorem lowered_axialLorentzSpinActionPairing
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier)
    (first second third : LorentzianIndex) :
    loweredLorentzBivectorMatrix
        (fun internalPair =>
          (dual (axialLorentzSpinActionVector first
            (lorentzBivectorFirst internalPair)
            (lorentzBivectorSecond internalPair) matter)).re)
        second third =
      (dual (axialLorentzSpinActionVector first second third matter)).re := by
  have swap :=
    axialLorentzSpinActionPairing_swap_last dual matter first second third
  fin_cases second <;> fin_cases third <;>
    simp [loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, Fin.sum_univ_six] at swap ⊢ <;>
    linarith

private def orderedLorentzSpinActionPairing
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier)
    (first second third : LorentzianIndex) : ℝ :=
  loweredLorentzBivectorMatrix
    (fun internalPair =>
      (dual (lorentzSpinActionVector first internalPair matter)).re)
    second third

private theorem orderedLorentzSpinActionPairing_eq_axial_of_currentReal
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier)
    (currentReal : ∀ direction : LorentzianIndex,
      (dual (diracMatrixMatterAction (diracGamma direction) matter)).im = 0)
    (first second third : LorentzianIndex) :
    orderedLorentzSpinActionPairing dual matter first second third =
      (dual (axialLorentzSpinActionVector first second third matter)).re := by
  unfold orderedLorentzSpinActionPairing
  rw [show
    (fun internalPair =>
      (dual (lorentzSpinActionVector first internalPair matter)).re) =
      (fun internalPair =>
        (dual (axialLorentzSpinActionVector first
          (lorentzBivectorFirst internalPair)
          (lorentzBivectorSecond internalPair) matter)).re) by
    funext internalPair
    exact lorentzSpinActionPairing_eq_axial_of_currentReal
      dual matter currentReal first internalPair]
  exact lowered_axialLorentzSpinActionPairing dual matter first second third

private theorem orderedLorentzSpinActionPairing_crossAntisymmetric_of_currentReal
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier)
    (currentReal : ∀ direction : LorentzianIndex,
      (dual (diracMatrixMatterAction (diracGamma direction) matter)).im = 0) :
    ∀ first internal second,
      orderedLorentzSpinActionPairing dual matter first internal second =
        -orderedLorentzSpinActionPairing dual matter second internal first := by
  intro first internal second
  rw [orderedLorentzSpinActionPairing_eq_axial_of_currentReal
      dual matter currentReal,
    orderedLorentzSpinActionPairing_eq_axial_of_currentReal
      dual matter currentReal]
  exact axialLorentzSpinActionPairing_swap_outer
    dual matter first internal second

private def responseCoefficient
    (response : PhysicalBivectorThreeForm)
    (direction : LorentzianIndex) (internalPair : Fin 6) : ℝ :=
  -(oneWedgeThreeSign direction *
    response internalPair (missingTripleOfOneForm direction))

private def orderedResponseCoefficient
    (response : PhysicalBivectorThreeForm)
    (direction internalFirst internalSecond : LorentzianIndex) : ℝ :=
  loweredLorentzBivectorMatrix (responseCoefficient response direction)
    internalFirst internalSecond

private def axialResponseContorsion
    (response : PhysicalBivectorThreeForm) : LorentzBivectorOneForm :=
  fun direction internalPair =>
    -((1 / 2 : ℝ) * minkowskiInternalSign direction *
      minkowskiInternalSign (pairFirst internalPair) *
      minkowskiInternalSign (pairSecond internalPair)) *
        responseCoefficient response direction internalPair

private theorem lowered_axialResponseContorsion
    (response : PhysicalBivectorThreeForm)
    (direction first second : LorentzianIndex) :
    loweredLorentzBivectorMatrix (axialResponseContorsion response direction)
        first second =
      -((1 / 2 : ℝ) * minkowskiInternalSign direction *
        minkowskiInternalSign first * minkowskiInternalSign second) *
          orderedResponseCoefficient response direction first second := by
  fin_cases direction <;> fin_cases first <;> fin_cases second <;>
    simp [axialResponseContorsion, orderedResponseCoefficient,
      loweredLorentzBivectorMatrix, orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six]

private theorem minkowskiInternalSign_square
    (direction : LorentzianIndex) :
    minkowskiInternalSign direction * minkowskiInternalSign direction = 1 := by
  fin_cases direction <;> simp [minkowskiInternalSign]

private def axialResponseTorsion
    (response : PhysicalBivectorThreeForm) : PointwiseCartanTorsionTwoForm :=
  ⟨fun pair internal =>
    -(minkowskiInternalSign (pairFirst pair) *
      minkowskiInternalSign (pairSecond pair)) *
        orderedResponseCoefficient response (pairFirst pair) internal
          (pairSecond pair)⟩

private theorem axialResponseContorsion_connectionCross
    (response : PhysicalBivectorThreeForm)
    (responseCross : ∀ first internal second,
      orderedResponseCoefficient response first internal second =
        -orderedResponseCoefficient response second internal first) :
    ∀ first internal second,
      lorentzSkewConnectionOfBivectorOneForm
          (axialResponseContorsion response) first internal second =
        -lorentzSkewConnectionOfBivectorOneForm
          (axialResponseContorsion response) second internal first := by
  intro first internal second
  unfold lorentzSkewConnectionOfBivectorOneForm
  rw [lowered_axialResponseContorsion,
    lowered_axialResponseContorsion, responseCross]
  ring

private theorem axialResponseContorsion_torsion_eq
    (response : PhysicalBivectorThreeForm)
    (responseCross : ∀ first internal second,
      orderedResponseCoefficient response first internal second =
        -orderedResponseCoefficient response second internal first) :
    cartanTorsionOfContorsion 1 (axialResponseContorsion response) =
      axialResponseTorsion response := by
  ext pair internal
  simp only [cartanTorsionOfContorsion,
    pullbackLorentzBivectorOneForm_one,
    pushforwardCartanTorsionTwoForm_one, minkowskiRaiseCartanTorsion,
    internalFrameCartanTorsion]
  change
    minkowskiInternalSign internal *
        (loweredLorentzBivectorMatrix (axialResponseContorsion response
              (pairFirst pair)) internal (pairSecond pair) -
          loweredLorentzBivectorMatrix (axialResponseContorsion response
              (pairSecond pair)) internal (pairFirst pair)) =
      -(minkowskiInternalSign (pairFirst pair) *
        minkowskiInternalSign (pairSecond pair)) *
          orderedResponseCoefficient response (pairFirst pair) internal
            (pairSecond pair)
  rw [lowered_axialResponseContorsion,
    lowered_axialResponseContorsion,
    responseCross (pairFirst pair) internal (pairSecond pair)]
  have internalSquare := minkowskiInternalSign_square internal
  ring_nf
  rw [pow_two, internalSquare, one_mul]

private theorem forall_fin_zero_prop {P : Fin 0 → Prop} :
    (∀ index, P index) ↔ True :=
  ⟨fun _ => True.intro, fun _ index => Fin.elim0 index⟩

set_option maxHeartbeats 3000000 in
private theorem axialResponseContorsion_forward_eq
    (response : PhysicalBivectorThreeForm)
    (responseCross : ∀ first internal second,
      orderedResponseCoefficient response first internal second =
        -orderedResponseCoefficient response second internal first) :
    cartanTorsionThreeForm 1 (axialResponseTorsion response) = response := by
  funext internalPair triple
  simp only [Fin.forall_fin_succ, forall_fin_zero_prop, and_true]
    at responseCross
  rcases responseCross with
    ⟨⟨⟨h000, h001, h002, h003⟩, ⟨h010, h011, h012, h013⟩,
        ⟨h020, h021, h022, h023⟩, ⟨h030, h031, h032, h033⟩⟩,
      ⟨⟨h100, h101, h102, h103⟩, ⟨h110, h111, h112, h113⟩,
        ⟨h120, h121, h122, h123⟩, ⟨h130, h131, h132, h133⟩⟩,
      ⟨⟨h200, h201, h202, h203⟩, ⟨h210, h211, h212, h213⟩,
        ⟨h220, h221, h222, h223⟩, ⟨h230, h231, h232, h233⟩⟩,
      ⟨⟨h300, h301, h302, h303⟩, ⟨h310, h311, h312, h313⟩,
        ⟨h320, h321, h322, h323⟩, ⟨h330, h331, h332, h333⟩⟩⟩
  simp [orderedResponseCoefficient, responseCoefficient,
    loweredLorentzBivectorMatrix, orientedLorentzBivectorBasisCoefficient,
    missingTripleOfOneForm, oneWedgeThreeSign,
    pairFirst, pairSecond, Fin.sum_univ_six] at h000 h001 h002 h003 h010 h011 h012 h013 h020 h021 h022 h023 h030 h031 h032 h033 h100 h101 h102 h103 h110 h111 h112 h113 h120 h121 h122 h123 h130 h131 h132 h133 h200 h201 h202 h203 h210 h211 h212 h213 h220 h221 h222 h223 h230 h231 h232 h233 h300 h301 h302 h303 h310 h311 h312 h313 h320 h321 h322 h323 h330 h331 h332 h333
  fin_cases internalPair <;> fin_cases triple <;>
    simp [cartanTorsionThreeForm, cartanTorsionCoframeWedgeThreeForm,
      torsionCoframeWedgeThreeForm, internalBivectorDualThreeForm,
      rawPointwiseCartanTorsion,
      orderedCartanTorsionComponent,
      axialResponseTorsion, responseCoefficient,
      orderedResponseCoefficient,
      loweredLorentzBivectorMatrix, orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, threeFormFirst, threeFormSecond, threeFormThird,
      lorentzianCoframeHodge, missingTripleOfOneForm, oneWedgeThreeSign,
      minkowskiInternalSign, Fin.sum_univ_six, Matrix.one_apply] <;>
    linarith

private theorem
    responseCrossAntisymmetric_implies_generatedConnectionCrossAntisymmetric
    (response : PhysicalBivectorThreeForm)
    (responseCross : ∀ first internal second,
      orderedResponseCoefficient response first internal second =
        -orderedResponseCoefficient response second internal first) :
    ∀ first internal second,
      lorentzSkewConnectionOfBivectorOneForm
          (contorsionOfCartanTorsion 1
            (cartanTorsionOfThreeForm 1 response))
          first internal second =
        -lorentzSkewConnectionOfBivectorOneForm
          (contorsionOfCartanTorsion 1
            (cartanTorsionOfThreeForm 1 response))
          second internal first := by
  have responseEq := axialResponseContorsion_forward_eq response responseCross
  have contorsionEq :
      contorsionOfCartanTorsion 1 (cartanTorsionOfThreeForm 1 response) =
        axialResponseContorsion response := by
    have torsionEq :=
      axialResponseContorsion_torsion_eq response responseCross
    calc
      contorsionOfCartanTorsion 1 (cartanTorsionOfThreeForm 1 response) =
          contorsionOfCartanTorsion 1
            (cartanTorsionOfThreeForm 1
              (cartanTorsionThreeForm 1 (axialResponseTorsion response))) := by
            rw [responseEq]
      _ = contorsionOfCartanTorsion 1
            (axialResponseTorsion response) := by
            rw [cartanTorsionOfThreeForm_leftInverse]
            norm_num
      _ = contorsionOfCartanTorsion 1
            (cartanTorsionOfContorsion 1
              (axialResponseContorsion response)) := by
            rw [torsionEq]
      _ = axialResponseContorsion response := by
            rw [contorsionOfCartanTorsion_leftInverse]
            norm_num
  rw [contorsionEq]
  exact axialResponseContorsion_connectionCross response responseCross

private theorem fixedActionSpinResponse_responseCoefficient
    (point : BasePoint) (direction : LorentzianIndex)
    (internalPair : Fin 6) :
    responseCoefficient
        (diracDualFormNativeActionSpinResponseAt Source Seed point)
        direction internalPair =
      ((Field point).conjugateMatter
        (lorentzSpinActionVector direction internalPair
          (Field point).matter)).re := by
  unfold responseCoefficient
  rw [actionSpinResponse_coordinate_normalForm]
  have signSquare := oneWedgeThreeSign_square direction
  ring_nf
  rw [missingTripleOfOneForm_involutive, signSquare, one_mul]

private theorem fixedActionSpinResponse_crossAntisymmetric_of_currentReal
    (point : BasePoint)
    (currentReal : ∀ direction : LorentzianIndex,
      (fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter point
        (diracMatrixMatterAction (diracGamma direction)
          (fixedSourceGeneratedCompatibleGravityTailBase.matter point))).im =
        0) :
    ∀ first internal second,
      orderedResponseCoefficient
          (diracDualFormNativeActionSpinResponseAt Source Seed point)
          first internal second =
        -orderedResponseCoefficient
          (diracDualFormNativeActionSpinResponseAt Source Seed point)
          second internal first := by
  have fieldCurrentReal : ∀ direction : LorentzianIndex,
      ((Field point).conjugateMatter
        (diracMatrixMatterAction (diracGamma direction)
          (Field point).matter)).im = 0 := by
    intro direction
    rw [field_matter_eq_seed, field_conjugateMatter_eq_seed]
    simpa only [show fixedSourceGeneratedCompatibleGravityTailBase.matter =
        Seed.matter by rfl,
      show fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter =
        Seed.conjugateMatter by rfl] using currentReal direction
  have orderedCross :=
    orderedLorentzSpinActionPairing_crossAntisymmetric_of_currentReal
      (Field point).conjugateMatter (Field point).matter fieldCurrentReal
  have coefficientEq :
      responseCoefficient
          (diracDualFormNativeActionSpinResponseAt Source Seed point) =
        fun direction internalPair =>
          ((Field point).conjugateMatter
            (lorentzSpinActionVector direction internalPair
              (Field point).matter)).re := by
    funext direction internalPair
    exact fixedActionSpinResponse_responseCoefficient
      point direction internalPair
  intro first internal second
  unfold orderedResponseCoefficient
  rw [coefficientEq]
  exact orderedCross first internal second

private theorem
    fixedGravityTailCompatibleBase_diracCurrentReal_implies_connectionCrossAntisymmetric
    (point : BasePoint)
    (currentReal : ∀ direction : LorentzianIndex,
      (fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter point
        (diracMatrixMatterAction (diracGamma direction)
          (fixedSourceGeneratedCompatibleGravityTailBase.matter point))).im =
        0) :
    ∀ first internal second,
      fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          first internal second =
        -fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          second internal first := by
  rw [fixedGravityTailCompatibleBase_connection_eq_actionContorsion]
  unfold diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  have seedCoframe : Seed.coframe point = 1 := by
    rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
  rw [seedCoframe]
  exact
    responseCrossAntisymmetric_implies_generatedConnectionCrossAntisymmetric
      (diracDualFormNativeActionSpinResponseAt Source Seed point)
      (fixedActionSpinResponse_crossAntisymmetric_of_currentReal
        point currentReal)

/-- Exact finite quotient of the compatible restart: its complete connection
cross condition is equivalent to reality of all four Dirac-vector-current
coordinates of the same generated Base.  This theorem classifies the
remaining obstruction; it does not generate the all-point reality law. -/
theorem
    fixedGravityTailCompatibleBase_connectionCrossAntisymmetric_iff_diracCurrentReal
    (point : BasePoint) :
    (∀ first internal second,
      fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          first internal second =
        -fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
          second internal first) ↔
      ∀ direction : LorentzianIndex,
        (fixedSourceGeneratedCompatibleGravityTailBase.conjugateMatter point
          (diracMatrixMatterAction (diracGamma direction)
            (fixedSourceGeneratedCompatibleGravityTailBase.matter point))).im =
          0 := by
  constructor
  · exact
      fixedGravityTailCompatibleBase_connectionCrossAntisymmetric_implies_diracCurrentReal
        point
  · exact
      fixedGravityTailCompatibleBase_diracCurrentReal_implies_connectionCrossAntisymmetric
        point

private theorem compatibleEC_actionTorsion_eq_seed
    (point : BasePoint) :
    diracDualFormNativeActionCartanTorsionAt Source
        (diracDualFormNativeCartanECSynchronizedECActual Source fixedSourceGeneratedCompatibleGravityTailBase
          point) point =
      diracDualFormNativeActionCartanTorsionAt Source Seed point := by
  have spinEq :
      diracDualFormNativeActionSpinResponseAt Source
          (diracDualFormNativeCartanECSynchronizedECActual Source
            fixedSourceGeneratedCompatibleGravityTailBase point) point =
        diracDualFormNativeActionSpinResponseAt Source Seed point := by
    apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
    · rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
        fixedGravityTailCompatibleBase_coframe_eq_one,
        fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
    · rfl
    · rfl
  unfold diracDualFormNativeActionCartanTorsionAt
  have spinEq' :
      diracDualFormNativeActionSpinResponseAt Source
          (diracDualFormNativeCartanECSynchronizedECActual Source
            (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
              Source Seed) point) point =
        diracDualFormNativeActionSpinResponseAt Source Seed point := by
    simpa only [fixedSourceGeneratedCompatibleGravityTailBase] using spinEq
  rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
    fixedSourceGeneratedCompatibleGravityTailBase,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    spinEq']

theorem fixedGravityTailCompatibleBase_contactJet_derivative_normalForm
    (point : BasePoint)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    (diracDualFormNativeCartanECSynchronizedCoframeFirstJet
        Source fixedSourceGeneratedCompatibleGravityTailBase point).derivative
        derivativeDirection internal coordinate =
      -((1 : ℝ) / 2) *
        (fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
            derivativeDirection internal coordinate +
          fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point
            coordinate internal derivativeDirection) := by
  unfold diracDualFormNativeCartanECSynchronizedCoframeFirstJet
  dsimp only
  rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact,
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
    fixedGravityTailCompatibleBase_coframe_eq_one,
    compatibleEC_actionTorsion_eq_seed,
    ← fixedGravityTailCompatibleBase_actualTorsion_eq_generated]
  fin_cases derivativeDirection <;> fin_cases internal <;>
    fin_cases coordinate <;>
    simp [orderedCartanTorsionComponent,
      actualPointwiseCartanTorsionTwoForm,
      pointwiseCartanTorsion, pointwiseCoframeCovariantDerivative,
      holonomicCoframeFirstJetAt, coframeConnectionAction,
      fixedGravityTailCompatibleBase_coframe_eq_one,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_six,
      Matrix.one_apply] <;>
    ring

/-- For the fixed source/current-generated restart, the complete contact jet is
holonomic exactly when its generated connection has the remaining
form-slot/coframe-coordinate cross antisymmetry. -/
theorem fixedGravityTailCompatibleBase_contactJet_eq_holonomic_iff_connection_crossAntisymmetric
    (point : BasePoint) :
    diracDualFormNativeCartanECSynchronizedCoframeFirstJet
        Source fixedSourceGeneratedCompatibleGravityTailBase point =
      holonomicCoframeFirstJetAt fixedSourceGeneratedCompatibleGravityTailBase.coframe point ↔
    ∀ first internal second,
      fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point first internal second =
        -fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection point second internal first := by
  constructor
  · intro contactEq first internal second
    have componentEq := congrArg
      (fun jet : PointwiseLorentzianCoframeJet =>
        jet.derivative first internal second)
      contactEq
    rw [fixedGravityTailCompatibleBase_contactJet_derivative_normalForm,
      fixedGravityTailCompatibleBase_holonomicCoframeFirstJet_eq_identity] at componentEq
    simp [identityCoframeMatterGeometry] at componentEq
    linarith
  · intro cross
    apply coframeJet_eq_of_fields_eq
    · unfold diracDualFormNativeCartanECSynchronizedCoframeFirstJet
      dsimp only
      rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe]
      rfl
    · funext first internal second
      rw [fixedGravityTailCompatibleBase_contactJet_derivative_normalForm,
        fixedGravityTailCompatibleBase_holonomicCoframeFirstJet_eq_identity]
      simp [identityCoframeMatterGeometry, cross first internal second]

theorem fixedGravityTailCompatibleBase_contactJet_zeroSlice_eq_holonomic
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source fixedSourceGeneratedCompatibleGravityTailBase
        (canonicalCauchySlicePoint 0 space) =
      holonomicCoframeFirstJetAt fixedSourceGeneratedCompatibleGravityTailBase.coframe
        (canonicalCauchySlicePoint 0 space) := by
  exact
    (fixedGravityTailCompatibleBase_contactJet_eq_holonomic_iff_connection_crossAntisymmetric
      (canonicalCauchySlicePoint 0 space)).2
      (fixedGravityTailCompatibleBase_connection_zeroSlice_crossAntisymmetric space)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailCompatibleRestart
