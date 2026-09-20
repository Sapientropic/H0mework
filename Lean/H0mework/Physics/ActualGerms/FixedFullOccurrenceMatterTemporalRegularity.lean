import H0mework.Physics.JointVariation.TemporalDevelopmentOperator
import H0mework.Physics.FixedJoint.FixedCartanRestartCurvatureSpatialRegularity
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

/-!
# Fixed P506/L0 full-occurrence matter temporal regularity

The complete-joint occurrence operator recenters the fixed P506/L0 current,
recomputes its Cartan response from the same source, and reads the
action-generated matter temporal correction.  This module proves local smooth
regularity of that full-occurrence correction at the distinguished common
occurrence.

The proof consumes only the fixed source/current lineage and the existing
action-owned temporal-principal inverse.  It accepts no residual coordinate,
target derivative, regularity receipt, time-independence premise, or branch
choice.  The terminal derivative theorem is an analytic readout of the
already generated canonical time primitive.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FullOccurrenceMatterTemporalRegularity

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanAlgebraicSmoothness
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActualVariationRegularity
open StageNineP286ActionCauchySplit
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fullOccurrenceMatterRegularityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance fullOccurrenceMatterRegularityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance fullOccurrenceMatterRegularityP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private def InputCartanActual : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource InputActual

private theorem canonicalZeroSliceOrigin :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem inputActual_coframe_contDiff :
    ContDiff ℝ ∞ InputActual.coframe := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
      internal coordinate

private def inputActualCoframeJetCarrier
    (point : BasePoint) : IdentityECCoframeJetCarrier :=
  (InputActual.coframe point,
    (holonomicCoframeFirstJetAt InputActual.coframe point).derivative)

private theorem inputActualCoframeJetCarrier_contDiff :
    ContDiff ℝ ∞ inputActualCoframeJetCarrier := by
  refine inputActual_coframe_contDiff.prodMk ?_
  apply contDiff_pi'
  intro derivativeDirection
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  let component : BasePoint → ℝ := fun point =>
    InputActual.coframe point internal coordinate
  have componentSmooth : ContDiff ℝ ∞ component :=
    contDiff_pi.mp (contDiff_pi.mp inputActual_coframe_contDiff internal)
      coordinate
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => component)) :=
    componentSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ component point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  change ContDiff ℝ ∞
    (fun point =>
      fderiv ℝ component point
        (coordinateDirection derivativeDirection))
  exact derivativeSmooth.clm_apply contDiff_const

private theorem inputActualCoframeJetCarrier_origin :
    inputActualCoframeJetCarrier 0 =
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)) := by
  unfold inputActualCoframeJetCarrier
  have jet :
      holonomicCoframeFirstJetAt InputActual.coframe
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet) := by
    rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
      fixedP506JointActionSuccessor_coframe,
      fixedGlobalMatterDualP286Complete_coframe,
      fixedGlobalMatterDualFullCauchy_coframe,
      fixedGlobalFullCauchy_coframe]
    exact fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice 0
  rw [canonicalZeroSliceOrigin] at jet
  exact congrArg (fun actual => (actual.coframe, actual.derivative)) jet

private theorem inputActualSpinResponse_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponseAt
        positiveSmoothUnifiedSource InputActual) 0 := by
  have coframeOne : InputActual.coframe 0 = 1 := by
    have actual :=
      congrArg Prod.fst inputActualCoframeJetCarrier_origin
    simpa [inputActualCoframeJetCarrier] using actual
  have outer : ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponsePointCoframe
        positiveSmoothUnifiedSource InputActual)
      (0, InputActual.coframe 0) := by
    exact
      diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
        positiveSmoothUnifiedSource InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        0 (InputActual.coframe 0)
        (by rw [coframeOne]; simp)
  have inner : ContDiffAt ℝ ∞
      (fun point : BasePoint => (point, InputActual.coframe point)) 0 :=
    contDiffAt_id.prodMk inputActual_coframe_contDiff.contDiffAt
  have composed := outer.comp 0 inner
  rw [show
    diracDualFormNativeActionSpinResponseAt
        positiveSmoothUnifiedSource InputActual =
      fun point =>
        diracDualFormNativeActionSpinResponsePointCoframe
          positiveSmoothUnifiedSource InputActual
          (point, InputActual.coframe point) by
    funext point
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      positiveSmoothUnifiedSource InputActual point]
  exact composed

private def inputActualCoframeSpinResponseCarrier
    (point : BasePoint) :
    LorentzianCoframe × PhysicalBivectorThreeForm :=
  (InputActual.coframe point,
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      InputActual point)

private theorem inputActualCoframeSpinResponseCarrier_contDiffAt_origin :
    ContDiffAt ℝ ∞ inputActualCoframeSpinResponseCarrier 0 :=
  inputActual_coframe_contDiff.contDiffAt.prodMk
    inputActualSpinResponse_contDiffAt_origin

private theorem inputActualCartanContorsion_component_contDiffAt_origin
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt
          positiveSmoothUnifiedSource InputActual point
          formDirection internalPair) 0 := by
  let response :=
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      InputActual 0
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have coframeOne : InputActual.coframe 0 = 1 := by
    have actual :=
      congrArg Prod.fst inputActualCoframeJetCarrier_origin
    simpa [inputActualCoframeJetCarrier] using actual
  have carrierAt :
      inputActualCoframeSpinResponseCarrier 0 =
        ((1 : LorentzianCoframe), response) := by
    unfold inputActualCoframeSpinResponseCarrier response
    rw [coframeOne]
  have outerAt : ContDiffAt ℝ ∞ outer
      (inputActualCoframeSpinResponseCarrier 0) := by
    rw [carrierAt]
    exact
      cartanContorsionCoframeResponseComponent_contDiffAt
        (1 : LorentzianCoframe) response (by simp)
        formDirection internalPair
  rw [show
    (fun point : BasePoint =>
      diracDualFormNativeActionCartanContorsionAt
        positiveSmoothUnifiedSource InputActual point
        formDirection internalPair) =
      outer ∘ inputActualCoframeSpinResponseCarrier by rfl]
  exact outerAt.comp 0
    inputActualCoframeSpinResponseCarrier_contDiffAt_origin

private theorem inputActualLeviCivita_component_contDiffAt_origin
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        (holonomicCoframeFirstJetAt InputActual.coframe point)
          |>.lorentzSpinConnection
            formDirection internalOut internalIn) 0 := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : ContDiffAt ℝ ∞ outer
      (inputActualCoframeJetCarrier 0) := by
    rw [inputActualCoframeJetCarrier_origin]
    exact
      identityECSpinConnectionComponentOfCarrier_contDiffAt
        formDirection internalOut internalIn
  rw [show
    (fun point : BasePoint =>
      (holonomicCoframeFirstJetAt InputActual.coframe point)
        |>.lorentzSpinConnection
          formDirection internalOut internalIn) =
      outer ∘ inputActualCoframeJetCarrier by rfl]
  exact outerAt.comp 0 inputActualCoframeJetCarrier_contDiff.contDiffAt

private theorem inputCartanActual_connection_component_contDiffAt_origin
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        InputCartanActual.gravityConnection point
          formDirection internalOut internalIn) 0 := by
  have levi :=
    inputActualLeviCivita_component_contDiffAt_origin
      formDirection internalOut internalIn
  have contorsionSum : ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        ∑ internalPair : Fin 6,
          diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource InputActual point
              formDirection internalPair *
            orientedLorentzBivectorBasisCoefficient internalPair
              internalOut internalIn) 0 := by
    apply ContDiffAt.sum
    intro internalPair _
    exact
      (inputActualCartanContorsion_component_contDiffAt_origin
        formDirection internalPair).mul contDiffAt_const
  unfold InputCartanActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  exact levi.add (contDiffAt_const.mul contorsionSum)

private theorem
    inputCartanActual_matterCovariantDerivative_coordinate_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (holonomicMatterCovariantDerivative InputCartanActual point
          direction)) 0 := by
  have derivativeSmooth : ContDiffAt ℝ ∞ (fun point =>
      fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv
          (InputActual.matter candidate)) point direction) 0 :=
    (holonomicMatterCoordinateDerivative_contDiff_local InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth direction
      ).contDiffAt
  have matterSmooth : ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv (InputActual.matter point)) 0 :=
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1.contDiffAt
  have gaugeSmooth : ContDiffAt ℝ ∞ (fun point =>
      p286CoordinateEquiv
        (InputActual.gaugeConnection point direction)) 0 :=
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.1
      direction).contDiffAt
  have spinMatrixSmooth : ContDiffAt ℝ ∞ (fun point =>
      diracSpinConnectionLift
        (InputCartanActual.gravityConnection point) direction) 0 := by
    apply contDiffAt_pi'
    intro row
    apply contDiffAt_pi'
    intro column
    unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply ContDiffAt.sum
    intro pair _
    have realCoefficientSmooth : ContDiffAt ℝ ∞ (fun point =>
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          InputCartanActual.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair)) 0 :=
      contDiffAt_const.mul
        (inputCartanActual_connection_component_contDiffAt_origin direction
          (lorentzBivectorFirst pair) (lorentzBivectorSecond pair))
    have complexCoefficientSmooth : ContDiffAt ℝ ∞ (fun point =>
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          InputCartanActual.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ)) 0 :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp 0 realCoefficientSmooth
    exact (contDiffAt_const.mul complexCoefficientSmooth).mul contDiffAt_const
  have spinActionSmooth : ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (InputCartanActual.gravityConnection point) direction)
          (InputActual.matter point))) 0 := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 spinMatrixSmooth).clm_apply matterSmooth
    change ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (InputCartanActual.gravityConnection point) direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (InputActual.matter point))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeActionSmooth : ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (InputActual.gaugeConnection point direction))
          (InputActual.matter point))) 0 := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 gaugeSmooth).clm_apply matterSmooth
    change ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (InputActual.gaugeConnection point direction))))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (InputActual.matter point))))) 0 at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold InputCartanActual holonomicMatterCovariantDerivative
  simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
  exact derivativeSmooth.add spinActionSmooth |>.add gaugeActionSmooth

private theorem inputCartanActual_knownVector_coordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (holonomicDiracDualCurrentCoframeMatterKnownVector
          InputCartanActual point)) 0 := by
  have coframeSmooth : ContDiffAt ℝ ∞
      (fun point => InputCartanActual.coframe point) 0 := by
    simpa [InputCartanActual] using inputActual_coframe_contDiff.contDiffAt
  have coframeOrigin : InputCartanActual.coframe 0 = 1 := by
    have actual :=
      congrArg Prod.fst inputActualCoframeJetCarrier_origin
    change InputActual.coframe 0 = 1 at actual
    simpa [InputCartanActual] using actual
  have inverseGammaSmooth : ∀ direction : Fin 3,
      ContDiffAt ℝ ∞ (fun point =>
        inverseCoframeDiracGamma
          { coframe := InputCartanActual.coframe point, derivative := 0 }
          direction.succ) 0 := by
    intro direction
    have outer :=
      inverseCoframeDiracGamma_contDiffAt
        (1 : LorentzianCoframe) (by simp) direction.succ
    rw [← coframeOrigin] at outer
    exact outer.comp 0 coframeSmooth
  have kineticDirectionSmooth : ∀ direction : Fin 3,
      ContDiffAt ℝ ∞ (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := InputCartanActual.coframe point, derivative := 0 }
              direction.succ)
            (holonomicMatterCovariantDerivative InputCartanActual point
              direction.succ))) 0 := by
    intro direction
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 (inverseGammaSmooth direction)).clm_apply
          (inputCartanActual_matterCovariantDerivative_coordinate_contDiffAt_origin
            direction.succ)
    change ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := InputCartanActual.coframe point, derivative := 0 }
            direction.succ)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicMatterCovariantDerivative InputCartanActual point
                direction.succ))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have kineticSumSmooth : ContDiffAt ℝ ∞ (fun point =>
      ∑ direction : Fin 3,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := InputCartanActual.coframe point, derivative := 0 }
              direction.succ)
            (holonomicMatterCovariantDerivative InputCartanActual point
              direction.succ))) 0 :=
    ContDiffAt.sum fun direction _ => kineticDirectionSmooth direction
  have kineticSmooth : ContDiffAt ℝ ∞ (fun point =>
      Complex.I •
        ∑ direction : Fin 3,
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := InputCartanActual.coframe point, derivative := 0 }
                direction.succ)
              (holonomicMatterCovariantDerivative InputCartanActual point
                direction.succ))) 0 :=
    (contDiffAt_const :
      ContDiffAt ℝ ∞ (fun _ : BasePoint => (Complex.I : ℂ)) 0).smul
        kineticSumSmooth
  have scalarSmooth : ContDiffAt ℝ ∞ (fun point =>
      InputCartanActual.scalar point) 0 := by
    simpa [InputCartanActual] using
      fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1.contDiffAt
  have matterSmooth : ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv (InputCartanActual.matter point)) 0 := by
    simpa [InputCartanActual] using
      fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1.contDiffAt
  have yukawaSmooth : ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (InputCartanActual.scalar point))
          (InputCartanActual.matter point))) 0 := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 scalarSmooth).clm_apply matterSmooth
    change ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (InputCartanActual.scalar point))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (InputCartanActual.matter point))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  simp only [map_add, map_smul, map_sum]
  exact kineticSmooth.add yukawaSmooth

private theorem
    inputCartanActual_temporalPrincipalScalar_contDiffAt_origin :
    ContDiffAt ℝ ∞ (fun point =>
      coframeTemporalPrincipalScalar (InputCartanActual.coframe point)) 0 := by
  have coframeSmooth : ContDiffAt ℝ ∞
      (fun point => InputCartanActual.coframe point) 0 := by
    simpa [InputCartanActual] using inputActual_coframe_contDiff.contDiffAt
  have coframeOrigin : InputCartanActual.coframe 0 = 1 := by
    have actual :=
      congrArg Prod.fst inputActualCoframeJetCarrier_origin
    change InputActual.coframe 0 = 1 at actual
    simpa [InputCartanActual] using actual
  have inverseSmooth : ContDiffAt ℝ ∞
      (fun point => (InputCartanActual.coframe point)⁻¹) 0 := by
    have outer :=
      StageNineCoframeVariation.coframe_inv_contDiffAt
        (1 : LorentzianCoframe) (by simp)
    rw [← coframeOrigin] at outer
    exact outer.comp 0 coframeSmooth
  unfold coframeTemporalPrincipalScalar
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro internal _
  have inverseEntrySmooth : ContDiffAt ℝ ∞ (fun point =>
      (InputCartanActual.coframe point)⁻¹
        (0 : LorentzianIndex) internal) 0 :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp inverseSmooth (0 : LorentzianIndex)) internal
  exact
    (contDiffAt_const.mul (inverseEntrySmooth.pow 2))

private theorem
    inputCartanActual_generatedTimeCovariantDerivative_coordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          InputCartanActual point)) 0 := by
  have coframeOrigin : InputCartanActual.coframe 0 = 1 := by
    have actual :=
      congrArg Prod.fst inputActualCoframeJetCarrier_origin
    change InputActual.coframe 0 = 1 at actual
    simpa [InputCartanActual] using actual
  have qComplexSmooth : ContDiffAt ℝ ∞ (fun point =>
      ((coframeTemporalPrincipalScalar
        (InputCartanActual.coframe point) : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0
      inputCartanActual_temporalPrincipalScalar_contDiffAt_origin
  have qComplexOrigin : ((coframeTemporalPrincipalScalar
      (InputCartanActual.coframe 0) : ℝ) : ℂ) ≠ 0 := by
    rw [coframeOrigin, coframeTemporalPrincipalScalar_one]
    norm_num
  have qInverseSmooth : ContDiffAt ℝ ∞ (fun point =>
      (((coframeTemporalPrincipalScalar
        (InputCartanActual.coframe point) : ℝ) : ℂ)⁻¹)) 0 :=
    qComplexSmooth.inv qComplexOrigin
  have coframeSmooth : ContDiffAt ℝ ∞
      (fun point => InputCartanActual.coframe point) 0 := by
    simpa [InputCartanActual] using inputActual_coframe_contDiff.contDiffAt
  have gammaTimeSmooth : ContDiffAt ℝ ∞ (fun point =>
      inverseCoframeDiracGamma
        { coframe := InputCartanActual.coframe point, derivative := 0 }
        (0 : LorentzianIndex)) 0 := by
    have outer :=
      inverseCoframeDiracGamma_contDiffAt
        (1 : LorentzianCoframe) (by simp) (0 : LorentzianIndex)
    rw [← coframeOrigin] at outer
    exact outer.comp 0 coframeSmooth
  have gammaKnownActionSmooth : ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := InputCartanActual.coframe point, derivative := 0 }
            (0 : LorentzianIndex))
          (holonomicDiracDualCurrentCoframeMatterKnownVector
            InputCartanActual point))) 0 := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 gammaTimeSmooth).clm_apply
          inputCartanActual_knownVector_coordinate_contDiffAt_origin
    change ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := InputCartanActual.coframe point, derivative := 0 }
            (0 : LorentzianIndex))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicDiracDualCurrentCoframeMatterKnownVector
                InputCartanActual point))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have iSmooth :
      ContDiffAt ℝ ∞ (fun _ : BasePoint => (Complex.I : ℂ)) 0 :=
    contDiffAt_const
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
    currentCoframeMatterTemporalPrincipalInverse
    currentCoframeMatterTemporalPrincipal
  simp only [LinearMap.smul_apply, map_neg, map_smul]
  exact (qInverseSmooth.smul (iSmooth.smul gammaKnownActionSmooth)).neg

private theorem
    inputCartanActual_matterConnectionAction_coordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (holonomicMatterConnectionAction InputCartanActual point
          canonicalLorentzianTimeDirection)) 0 := by
  rw [show
    (fun point =>
      matterCoordinateEquiv
        (holonomicMatterConnectionAction InputCartanActual point
          canonicalLorentzianTimeDirection)) =
    fun point =>
      matterCoordinateEquiv
          (holonomicMatterCovariantDerivative InputCartanActual point
            canonicalLorentzianTimeDirection) -
        fieldDirectionalDerivative
          (fun candidate =>
            matterCoordinateEquiv (InputCartanActual.matter candidate))
          point canonicalLorentzianTimeDirection by
    funext point
    unfold holonomicMatterConnectionAction holonomicMatterCovariantDerivative
    simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
    module]
  have derivativeSmooth : ContDiffAt ℝ ∞ (fun point =>
      fieldDirectionalDerivative
        (fun candidate =>
          matterCoordinateEquiv (InputCartanActual.matter candidate))
        point canonicalLorentzianTimeDirection) 0 := by
    simpa [InputCartanActual] using
      (holonomicMatterCoordinateDerivative_contDiff_local InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        canonicalLorentzianTimeDirection).contDiffAt
  exact
    (inputCartanActual_matterCovariantDerivative_coordinate_contDiffAt_origin
      canonicalLorentzianTimeDirection).sub derivativeSmooth

private theorem inputCartanActual_rawTimeVelocity_coordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          InputCartanActual point)) 0 := by
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
  simp only [map_sub]
  exact
    inputCartanActual_generatedTimeCovariantDerivative_coordinate_contDiffAt_origin.sub
      inputCartanActual_matterConnectionAction_coordinate_contDiffAt_origin

private theorem recenteredInput_coframeFirstJet_origin
    (contact : BasePoint) :
    holonomicCoframeFirstJetAt
        (fullyRecenterHolonomicConfiguration InputActual contact).coframe 0 =
      holonomicCoframeFirstJetAt InputActual.coframe contact := by
  apply coframeJet_eq_of_fields_eq
  · change
      (fullyRecenterHolonomicConfiguration InputActual contact).coframe 0 =
        InputActual.coframe contact
    exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · funext derivativeDirection internal coordinate
    change
      fieldDirectionalDerivative
          ((fun point => InputActual.coframe point internal coordinate) ∘
            canonicalSpacetimeContactTranslation contact)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (fun point => InputActual.coframe point internal coordinate)
          contact derivativeDirection
    simpa [canonicalSpacetimeContactTranslation] using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun point => InputActual.coframe point internal coordinate)
        contact 0 derivativeDirection

private theorem recenteredInput_spinResponse_origin
    (contact : BasePoint) :
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        (fullyRecenterHolonomicConfiguration InputActual contact) 0 =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        InputActual contact := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  · exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · exact fullyRecenterHolonomicConfiguration_matter_origin _ _
  · exact fullyRecenterHolonomicConfiguration_conjugateMatter_origin _ _

private theorem recenteredInput_actionCartanConnection_origin
    (contact : BasePoint) :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fullyRecenterHolonomicConfiguration InputActual contact) 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        InputActual contact := by
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [recenteredInput_coframeFirstJet_origin,
    fullyRecenterHolonomicConfiguration_coframe_origin,
    recenteredInput_spinResponse_origin]

private theorem restart_connection_origin
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent
        positiveSmoothUnifiedSource InputActual contact).gravityConnection 0 =
      InputCartanActual.gravityConnection contact := by
  change
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fullyRecenterHolonomicConfiguration InputActual contact) 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        InputActual contact
  exact recenteredInput_actionCartanConnection_origin contact

private theorem restart_matterCovariantDerivative_origin
    (contact : BasePoint) :
    holonomicMatterCovariantDerivative
        (completeJointGeneratedProfileRestartCurrent
          positiveSmoothUnifiedSource InputActual contact) 0 =
      holonomicMatterCovariantDerivative InputCartanActual contact := by
  funext direction
  unfold completeJointGeneratedProfileRestartCurrent
  unfold InputCartanActual
  unfold holonomicMatterCovariantDerivative
  change
    matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            ((fun point => matterCoordinateEquiv (InputActual.matter point)) ∘
              canonicalSpacetimeContactTranslation contact)
            0 direction) +
        diracMatrixMatterAction
            (diracSpinConnectionLift
              ((completeJointGeneratedProfileRestartCurrent
                positiveSmoothUnifiedSource InputActual contact
                ).gravityConnection 0) direction)
          (InputActual.matter
            (canonicalSpacetimeContactTranslation contact 0)) +
      diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (InputActual.gaugeConnection
              (canonicalSpacetimeContactTranslation contact 0) direction))
        (InputActual.matter
          (canonicalSpacetimeContactTranslation contact 0)) =
      matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun point => matterCoordinateEquiv (InputActual.matter point))
            contact direction) +
        diracMatrixMatterAction
            (diracSpinConnectionLift
              (InputCartanActual.gravityConnection contact) direction)
          (InputActual.matter contact) +
      diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (InputActual.gaugeConnection contact direction))
        (InputActual.matter contact)
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation,
    restart_connection_origin]
  simp [canonicalSpacetimeContactTranslation]

private theorem restart_rawTimeVelocity_origin
    (contact : BasePoint) :
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (completeJointGeneratedProfileRestartCurrent
          positiveSmoothUnifiedSource InputActual contact) 0 =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        InputCartanActual contact := by
  unfold completeJointGeneratedProfileRestartCurrent
  unfold InputCartanActual
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicMatterConnectionAction
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
  simp only [fullyRecenterHolonomicConfiguration_coframe_origin,
    fullyRecenterHolonomicConfiguration_scalar_origin,
    fullyRecenterHolonomicConfiguration_matter_origin,
    fullyRecenterHolonomicConfiguration_gaugeConnection_origin]
  have covariantDerivativeEq :=
    restart_matterCovariantDerivative_origin contact
  unfold completeJointGeneratedProfileRestartCurrent InputCartanActual at covariantDerivativeEq
  rw [recenteredInput_actionCartanConnection_origin, covariantDerivativeEq]

private theorem correction_normalForm
    (contact : BasePoint) :
    completeJointMatterTemporalCoordinateCorrection
        positiveSmoothUnifiedSource InputActual contact =
      matterCoordinateEquiv
          (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
            InputCartanActual contact) -
        fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (InputActual.matter point))
          contact canonicalLorentzianTimeDirection := by
  unfold completeJointMatterTemporalCoordinateCorrection
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    restart_rawTimeVelocity_origin]

theorem
    fixedP506L0FullOccurrenceMatterTemporalCoordinateCorrection_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (completeJointMatterTemporalCoordinateCorrection
        positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor) 0 := by
  rw [show
    completeJointMatterTemporalCoordinateCorrection
        positiveSmoothUnifiedSource InputActual =
      fun contact =>
        matterCoordinateEquiv
            (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
              InputCartanActual contact) -
          fieldDirectionalDerivative
            (fun point => matterCoordinateEquiv (InputActual.matter point))
            contact canonicalLorentzianTimeDirection by
    funext contact
    exact correction_normalForm contact]
  exact
    inputCartanActual_rawTimeVelocity_coordinate_contDiffAt_origin.sub
      (holonomicMatterCoordinateDerivative_contDiff_local InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        canonicalLorentzianTimeDirection).contDiffAt

theorem
    fixedP506L0FullOccurrenceMatterTemporalCoordinateCorrection_continuousAt_origin :
    ContinuousAt
      (completeJointMatterTemporalCoordinateCorrection
        positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor) 0 :=
  fixedP506L0FullOccurrenceMatterTemporalCoordinateCorrection_contDiffAt_origin.continuousAt

/-- The fixed full-occurrence correction generates the expected derivative
of its canonical source-free time primitive at the common occurrence. -/
theorem
    fixedP506L0FullOccurrenceMatterTemporalPrimitive_hasFDerivAt_origin :
    HasFDerivAt
      (canonicalTimePrimitive
        (completeJointMatterTemporalCoordinateCorrection
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor))
      (canonicalTimeProjection.smulRight
        (completeJointMatterTemporalCoordinateCorrection
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0)) 0 :=
  canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt
    (completeJointMatterTemporalCoordinateCorrection
      positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor)
    (fixedP506L0FullOccurrenceMatterTemporalCoordinateCorrection_contDiffAt_origin.of_le
      (by simp))

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FullOccurrenceMatterTemporalRegularity
