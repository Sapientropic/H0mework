import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermStructural
import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermStress

/-!
# C3h197: frozen-path adjoint temporal-germ decision

This module decides whether the C3h196 frozen-input affine path is already an
integral curve of the state-dependent adjoint matter action vector field.  It
does not manufacture a second jet to cancel the temporal first germ.  A
nonzero result is therefore a diagnostic of the frozen path, not a new
independent Cauchy constraint and not a premise for a repair constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermDecision

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open StageNineBlockwiseConstitutive
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeVariation
open StageNineCanonicalCauchyState
open StageNineCanonicalLocalFullActionResponseOperator
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeSectorStress
open StageNineCurrentCanonicalFullActionLorentzAdjointCauchyUpdate
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineDynamicBreakingVacuum
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionVariation
open StageNineMatterPointwiseEquation
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermStructural
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalGravityPreservingLorentzDualResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzActualFirstJetLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzP286SpatialCauchyClosure
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzOriginProvenance
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzScalarConstraint
open StageNineSourceActionGeneratedP506MatterCurrentCompleteFirstGermCanonicalPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullSynchronizedActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterTemporalFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSimpArgs false

/-! ## Representation-faithful elimination of the inner Yukawa cross term -/

private def DegreeTwoZero (field : DiracExteriorMatterCarrier) : Prop :=
  ∀ spin, (field spin).2.1 = 0

private theorem degreeTwoZero_diracMatrix
    {field : DiracExteriorMatterCarrier}
    (h : DegreeTwoZero field)
    (matrixValue : DiracMatrix) :
    DegreeTwoZero (diracMatrixMatterAction matrixValue field) := by
  intro spin
  change (∑ column, matrixValue spin column • (field column).2.1) = 0
  apply Finset.sum_eq_zero
  intro column _
  rw [h column]
  simp

private theorem degreeTwoZero_smul
    {field : DiracExteriorMatterCarrier}
    (h : DegreeTwoZero field)
    (coefficient : ℂ) :
    DegreeTwoZero (coefficient • field) := by
  intro spin
  change coefficient • (field spin).2.1 = 0
  rw [h spin]
  simp

private theorem degreeTwoZero_add
    {first second : DiracExteriorMatterCarrier}
    (hFirst : DegreeTwoZero first)
    (hSecond : DegreeTwoZero second) :
    DegreeTwoZero (first + second) := by
  intro spin
  change (first spin).2.1 + (second spin).2.1 = 0
  rw [hFirst spin, hSecond spin]
  simp

private theorem degreeTwoZero_sum
    {ι : Type} [Fintype ι]
    (field : ι → DiracExteriorMatterCarrier)
    (h : ∀ index, DegreeTwoZero (field index)) :
    DegreeTwoZero (∑ index, field index) := by
  exact Finset.sum_induction field DegreeTwoZero
    (fun _ _ => degreeTwoZero_add)
    (by intro spin; rfl)
    (fun index _ => h index)

private theorem degreeTwoZero_coordinate
    {field : DiracExteriorMatterCarrier}
    (h : DegreeTwoZero field) :
    diracSpinZeroMatterCoordinate field = 0 := by
  unfold diracSpinZeroMatterCoordinate hyperchargeDegreeTwoMatterCoordinate
  change
    ((su7ExteriorBasis 2).repr ((field 0).2.1))
      hyperchargeDegreeTwoIndex = 0
  rw [h 0]
  simp

private theorem degreeTwoZero_principal
    (direction : LorentzianIndex)
    {field : DiracExteriorMatterCarrier}
    (h : DegreeTwoZero field) :
    DegreeTwoZero (c3h196Principal direction field) := by
  rw [c3h196Principal_apply,
    identityCoframeMatterPrincipal_apply]
  exact degreeTwoZero_smul (degreeTwoZero_diracMatrix h _) _

private theorem degreeTwoZero_originOperator
    {field : DiracExteriorMatterCarrier}
    (h : DegreeTwoZero field) :
    DegreeTwoZero (c3h196AlgebraicOperator 0 field) := by
  rw [c3h196AlgebraicOperator_origin_apply_normalForm]
  apply degreeTwoZero_add
  · apply degreeTwoZero_smul
    apply degreeTwoZero_sum
    intro direction
    exact degreeTwoZero_diracMatrix
      (degreeTwoZero_diracMatrix h _) _
  · exact chiralExteriorYukawaAction_degreeTwo_eq_zero _ _

/-- The origin connection square contributes one in the selected adjoint
coordinate.  Only the represented degree-two zero fiber of the inner Yukawa
output is discarded; the whole Yukawa vector is not asserted to vanish. -/
theorem c3h196_K0P0K0_pairing_re :
    (diracSpinZeroMatterCoordinate
      (c3h196AlgebraicOperator 0
        (c3h196Principal canonicalLorentzianTimeDirection
          (c3h196AlgebraicOperator 0 c3h196Probe)))).re = 1 := by
  let scalar :=
    scalarCoordinateEquiv.symm
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  let connectionProbe : DiracExteriorMatterCarrier :=
    Complex.I •
      ∑ direction : LorentzianIndex,
        diracMatrixMatterAction (diracGamma direction)
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (lorentzSkewConnectionOfBivectorOneForm
                positiveP506MatterCurrentEinsteinCartanContorsionCoordinates)
              direction)
            c3h196Probe)
  have innerNormalForm :
      c3h196AlgebraicOperator 0 c3h196Probe =
        connectionProbe + chiralExteriorYukawaAction scalar c3h196Probe := by
    simpa [scalar, connectionProbe] using
      c3h196AlgebraicOperator_origin_apply_normalForm c3h196Probe
  have crossZero :
      diracSpinZeroMatterCoordinate
        (c3h196AlgebraicOperator 0
          (c3h196Principal canonicalLorentzianTimeDirection
            (chiralExteriorYukawaAction scalar c3h196Probe))) = 0 := by
    apply degreeTwoZero_coordinate
    apply degreeTwoZero_originOperator
    apply degreeTwoZero_principal
    exact chiralExteriorYukawaAction_degreeTwo_eq_zero _ _
  have probeCoordinate :
      ((su7ExteriorBasis 2).repr p286HyperchargeMatterProbe.2.1)
          hyperchargeDegreeTwoIndex = (1 : ℂ) := by
    simpa [hyperchargeDegreeTwoMatterCoordinate] using
      hyperchargeDegreeTwoMatterCoordinate_probe
  rw [innerNormalForm, map_add, map_add, map_add, crossZero]
  simp only [add_zero]
  rw [c3h196AlgebraicOperator_origin_apply_normalForm]
  simp only [map_add, map_smul,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero,
    add_zero]
  dsimp [connectionProbe]
  rw [show
      positiveP506MatterCurrentEinsteinCartanContorsionCoordinates =
        einsteinCartanSpinContorsionCoordinates
          positiveP506MatterCurrentEinsteinCartanSpinCoordinates by rfl,
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates_eq_normalForm]
  simp [c3h196Principal, c3h196Probe,
    identityCoframeMatterPrincipal,
    canonicalLorentzianTimeDirection,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    einsteinCartanSpinContorsionCoordinates,
    positiveP506MatterCurrentSpinCoordinatesNormalForm,
    diracMatrixMatterAction, diracSpinTwoMatterProbe,
    diracSpinZeroMatterCoordinate,
    hyperchargeDegreeTwoMatterCoordinate,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
    lorentzBivectorFirst, lorentzBivectorSecond,
    Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  rw [probeCoordinate]
  norm_num

/-! ## Finite coordinate decomposition of the frozen-path first germ -/

/-- Exact temporal P286 curvature coordinates consumed by the C3h196 Lorentz
jet.  This is a local readout of the fresh C3h187 Cauchy state; it does not
replace that state by the older synchronized actual. -/
private theorem c3h196ActionGeneratedP286Curvature_origin_coordinate
    (pair : Fin 6) :
    p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          c3h196SeedState 0 pair) =
      c3h181FullCurvatureCoordinateNormalForm 0 pair := by
  calc
    _ = holonomicP286GaugeCurvatureCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          0 pair := by
      unfold c3h196SeedState actionGeneratedP286Curvature
      rw [p286CoordinateEquiv_liftGaugeTwoFormOperator]
      rw [show
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.coframe
              0 =
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
              0 by
        rw [positiveP506MatterCurrentCompleteFirstGermCanonicalGeneratedZeroResponseState_coframe_one,
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_one]]
      rw [show
        (fun input =>
          p286CoordinateEquiv
            (positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.gaugeAuxiliary
              0 input)) =
            holonomicP286GaugeAuxiliaryCoordinate
              positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
              0 by
        funext input
        unfold holonomicP286GaugeAuxiliaryCoordinate
        rw [positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeAuxiliary]
        change
          p286CoordinateEquiv
              (positiveP506MatterCurrentCompleteFirstGermResponseActual.gaugeAuxiliary
                (canonicalCauchySlicePoint 0 0) input) =
            _
        rw [canonicalCauchySlicePoint_zero_zero,
          positiveP506MatterCurrentCompleteFirstGermResponseActual_gaugeAuxiliary,
          positiveP506MatterCurrentTemporalFirstGermResponseActual_gaugeAuxiliary]]
      exact (congrFun
        (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation_coordinate
          0) pair).symm
    _ = _ := congrFun
      (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureCoordinate_normalForm
        0) pair

private theorem c3h196ActionGeneratedP286Curvature_origin
    (pair : Fin 6) :
    actionGeneratedP286Curvature positiveSmoothUnifiedSource
        c3h196SeedState 0 pair =
      p286CoordinateEquiv.symm
        (c3h181FullCurvatureCoordinateNormalForm 0 pair) := by
  apply p286CoordinateEquiv.injective
  rw [c3h196ActionGeneratedP286Curvature_origin_coordinate,
    p286CoordinateEquiv.apply_symm_apply]

private theorem c3h196ActionGeneratedP286Curvature_origin_normalForm
    (pair : Fin 6) :
    actionGeneratedP286Curvature positiveSmoothUnifiedSource
        c3h196SeedState 0 pair =
      ![p286CoordinateEquiv.symm
          ((1 / 6 : ℝ) •
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge),
        0, 0, 0, 0, 0] pair := by
  rw [c3h196ActionGeneratedP286Curvature_origin]
  apply p286CoordinateEquiv.injective
  fin_cases pair <;>
    simp [c3h181FullCurvatureCoordinateNormalForm,
      c3h181StrongCouplingSquared,
      StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half] <;>
    congr 1 <;> norm_num

/-- The time-direction algebraic jet, read in the selected adjoint
coordinate.  The formula exposes the complete coframe response consumed by
the action-generated Lorentz jet; it does not introduce a response premise. -/
theorem c3h196_Kt_pairing_re :
    (diracSpinZeroMatterCoordinate
      (c3h196AlgebraicTimeDerivative c3h196Probe)).re =
      -(9 / 8 : ℝ) +
        (3 / 2 : ℝ) * c3h196SeedCoframeResponse 0 0 0 +
        (1 / 2 : ℝ) *
          (c3h196SeedCoframeResponse 0 1 1 +
           c3h196SeedCoframeResponse 0 2 2 +
           c3h196SeedCoframeResponse 0 3 3) +
        c3h196SeedCoframeResponse 0 3 0 := by
  have probeCoordinate :
      ((su7ExteriorBasis 2).repr p286HyperchargeMatterProbe.2.1)
          hyperchargeDegreeTwoIndex = (1 : ℂ) := by
    simpa [hyperchargeDegreeTwoMatterCoordinate] using
      hyperchargeDegreeTwoMatterCoordinate_probe
  rw [c3h196AlgebraicTimeDerivative_eq_jet]
  unfold c3h196AlgebraicOperatorJet c3h196ConnectionOperatorJet
  simp [Fin.sum_univ_four, c3h196GravityConnectionJet,
    c3h196GaugeConnectionJet,
    linearPlebanskiActionGeneratedLorentzLocalConnectionJet,
    linearPlebanskiActionGeneratedLorentzSpatialConnectionVelocity,
    linearPlebanskiActionGeneratedGravityCurvature,
    actionGeneratedGravityAuxiliary,
    c3h196SeedState_gravityAuxiliary_simple,
    c3h196SeedState_gravitySpatialDerivative_zero,
    c3h196SeedState_gravitySimplicityMultiplier_eq_freshActionResponse,
    c3h196SeedGravityMultiplier, gravityCoupledLinearPlebanskiMultiplier,
    linearPlebanskiMultiplierOfCoframeResponse,
    sourceGeneratedP286ActionLocalConnectionJet,
    sourceGeneratedP286SpatialConnectionVelocity_coordinate,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_connectionSpatialCauchyDerivative_zero,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gravityConnection_contorsion,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection_origin_zero,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_gaugeConnection_origin_zero,
    c3h196ActionGeneratedP286Curvature_origin_normalForm,
    cauchyLoweredLorentzConnectionBracketCoordinate,
    c3h196SeedState,
    c3h196Probe, canonicalLorentzianTimeDirection, temporalSpatialPair,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction, diracSpinTwoMatterProbe,
    diracSpinZeroMatterCoordinate, hyperchargeDegreeTwoMatterCoordinate,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_six,
    lorentzBivectorFirst, lorentzBivectorSecond,
    Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod,
    probeCoordinate]
  rw [show
      positiveP506MatterCurrentEinsteinCartanContorsionCoordinates =
        einsteinCartanSpinContorsionCoordinates
          positiveP506MatterCurrentEinsteinCartanSpinCoordinates by rfl,
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates_eq_normalForm]
  simp [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    einsteinCartanSpinContorsionCoordinates,
    positiveP506MatterCurrentSpinCoordinatesNormalForm,
    gravityInternalDualEquiv, gravityInternalDualLinear,
    physicalIIPlusBivector, physicalIIPlusCoframeTangent,
    coframeWedge, coframeWedgeTangent, internalBivectorDual,
    lorentzianCoframeHodge, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond,
    orientedLorentzBivectorBasisCoefficient,
    diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction, diracSpinTwoMatterProbe,
    p286HyperchargeMatterProbe,
    Matrix.one_apply, Fin.sum_univ_six]
  ring

/-- Sum of the three spatial principal-square contributions in the selected
adjoint coordinate.  As for `c3h196_Kt_pairing_re`, every connection jet is
read from the C3h196 seed state; no spatial residual is supplied as a
premise. -/
theorem c3h196_sum_KiP0Pi_pairing_re :
    (∑ axis : Fin 3,
      diracSpinZeroMatterCoordinate
        (c3h196AlgebraicSpatialDerivative axis
          (c3h196Principal canonicalLorentzianTimeDirection
            (c3h196Principal axis.succ c3h196Probe)))).re =
      -(23 / 16 : ℝ) +
        c3h196SeedCoframeResponse 0 1 1 +
        c3h196SeedCoframeResponse 0 2 2 +
        c3h196SeedCoframeResponse 0 3 3 := by
  simp_rw [c3h196AlgebraicSpatialDerivative_eq_jet]
  rw [Fin.sum_univ_three]
  have probeCoordinate :
      ((su7ExteriorBasis 2).repr p286HyperchargeMatterProbe.2.1)
          hyperchargeDegreeTwoIndex = (1 : ℂ) := by
    simpa [hyperchargeDegreeTwoMatterCoordinate] using
      hyperchargeDegreeTwoMatterCoordinate_probe
  unfold c3h196AlgebraicOperatorJet c3h196ConnectionOperatorJet
  simp [Fin.sum_univ_four, c3h196GravityConnectionJet,
    c3h196GaugeConnectionJet,
    linearPlebanskiActionGeneratedLorentzLocalConnectionJet,
    linearPlebanskiActionGeneratedLorentzSpatialConnectionVelocity,
    linearPlebanskiActionGeneratedLorentzExteriorDerivativeCoordinate,
    linearPlebanskiActionGeneratedGravityCurvature,
    actionGeneratedGravityAuxiliary,
    actionGeneratedP286ExteriorDerivativeCoordinate,
    c3h196SeedState_gravityAuxiliary_simple,
    c3h196SeedState_gravitySpatialDerivative_zero,
    c3h196SeedState_gravitySimplicityMultiplier_eq_freshActionResponse,
    c3h196SeedGravityMultiplier, gravityCoupledLinearPlebanskiMultiplier,
    linearPlebanskiMultiplierOfCoframeResponse,
    sourceGeneratedP286ActionLocalConnectionJet,
    sourceGeneratedP286SpatialConnectionVelocity_coordinate,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_connectionSpatialCauchyDerivative_zero,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gravityConnection_contorsion,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection_origin_zero,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_gaugeConnection_origin_zero,
    c3h196ActionGeneratedP286Curvature_origin_normalForm,
    cauchyLoweredLorentzConnectionBracketCoordinate,
    c3h196SeedState, c3h196Principal,
    identityCoframeMatterPrincipal,
    c3h196Probe, canonicalLorentzianTimeDirection, temporalSpatialPair,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction, diracSpinTwoMatterProbe,
    diracSpinZeroMatterCoordinate, hyperchargeDegreeTwoMatterCoordinate,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_six,
    lorentzBivectorFirst, lorentzBivectorSecond,
    Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod,
    probeCoordinate]
  rw [show
      positiveP506MatterCurrentEinsteinCartanContorsionCoordinates =
        einsteinCartanSpinContorsionCoordinates
          positiveP506MatterCurrentEinsteinCartanSpinCoordinates by rfl,
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates_eq_normalForm]
  simp [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    einsteinCartanSpinContorsionCoordinates,
    positiveP506MatterCurrentSpinCoordinatesNormalForm,
    gravityInternalDualEquiv, gravityInternalDualLinear,
    physicalIIPlusBivector, physicalIIPlusCoframeTangent,
    coframeWedge, coframeWedgeTangent, internalBivectorDual,
    lorentzianCoframeHodge, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond,
    orientedLorentzBivectorBasisCoefficient,
    diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction, diracSpinTwoMatterProbe,
    p286HyperchargeMatterProbe,
    Matrix.one_apply, Fin.sum_univ_six]
  ring

/-- Symbolic decision formula for the C3h196 frozen-path adjoint temporal
first germ.  This combines the actual temporal jet, the origin connection
square, and all three spatial principal-square jets.  It deliberately stops
at the fresh C3h187 coframe response: a numerical specialization requires a
separate, lineage-faithful fresh-response projection theorem. -/
theorem c3h196TemporalAdjointELFirstGerm_eq_freshCoframeResponse :
    c3h196TemporalAdjointELFirstGerm =
      (21 / 16 : ℝ) +
        c3h196SeedCoframeResponse 0 3 0 +
        (3 / 2 : ℝ) * c3h196SeedCoframeResponse 0 0 0 -
        (1 / 2 : ℝ) *
          (c3h196SeedCoframeResponse 0 1 1 +
           c3h196SeedCoframeResponse 0 2 2 +
           c3h196SeedCoframeResponse 0 3 3) := by
  have spatialReal := c3h196_sum_KiP0Pi_pairing_re
  rw [Complex.re_sum] at spatialReal
  rw [c3h196TemporalAdjointELFirstGerm_eq_holonomic_Kt_K0P0K0_KiP0Pi]
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum]
  rw [c3h196_Kt_pairing_re, c3h196_K0P0K0_pairing_re, spatialReal]
  ring

/-! ## Coframe-response readout -/

theorem gravityCoupledResponse_diagonalCombination_eq_stress_temporalTracefree
    (stress : LorentzianCoframe →L[ℝ] ℝ) :
    (3 / 2 : ℝ) *
          gravityCoupledLinearPlebanskiCoframeResponseOfStress stress 0 0 -
        (1 / 2 : ℝ) *
          (gravityCoupledLinearPlebanskiCoframeResponseOfStress stress 1 1 +
           gravityCoupledLinearPlebanskiCoframeResponseOfStress stress 2 2 +
           gravityCoupledLinearPlebanskiCoframeResponseOfStress stress 3 3) =
      stress temporalTracefreeCoframeVariation := by
  rw [coframe_eq_sum_coordinateDirections
    temporalTracefreeCoframeVariation]
  simp only [map_sum, map_smul]
  simp [gravityCoupledLinearPlebanskiCoframeResponseOfStress,
    coframeCovectorCoordinates, temporalTracefreeCoframeVariation,
    coframeCoordinateDirection, Matrix.trace, Fin.sum_univ_four]
  ring

/-- The `(3,0)` response coordinate consumes the `(0,3)` stress direction.
This transpose is the orientation-sensitive readout needed below. -/
theorem gravityCoupledResponse_temporalSpatial30_eq_half_stress_temporalSpatial03
    (stress : LorentzianCoframe →L[ℝ] ℝ) :
    gravityCoupledLinearPlebanskiCoframeResponseOfStress stress 3 0 =
      (1 / 2 : ℝ) * stress temporalSpatial03CoframeVariation := by
  simp [gravityCoupledLinearPlebanskiCoframeResponseOfStress,
    coframeCovectorCoordinates, temporalSpatial03CoframeVariation,
    coframeCoordinateDirection, Matrix.trace, Fin.sum_univ_four]

theorem
    positiveP506MatterCurrentFullCoframeResponse_diagonalCombination_eq_stress :
    (3 / 2 : ℝ) * positiveP506MatterCurrentFullCoframeResponse 0 0 -
        (1 / 2 : ℝ) *
          (positiveP506MatterCurrentFullCoframeResponse 1 1 +
           positiveP506MatterCurrentFullCoframeResponse 2 2 +
           positiveP506MatterCurrentFullCoframeResponse 3 3) =
      positiveP506MatterCurrentFullNonGravityCoframeStress
        temporalTracefreeCoframeVariation := by
  unfold positiveP506MatterCurrentFullCoframeResponse
  exact
    gravityCoupledResponse_diagonalCombination_eq_stress_temporalTracefree
      positiveP506MatterCurrentFullNonGravityCoframeStress

theorem
    positiveP506MatterCurrentFullCoframeResponse_diagonalCombination_eq_125_div_216 :
    (3 / 2 : ℝ) * positiveP506MatterCurrentFullCoframeResponse 0 0 -
        (1 / 2 : ℝ) *
          (positiveP506MatterCurrentFullCoframeResponse 1 1 +
           positiveP506MatterCurrentFullCoframeResponse 2 2 +
           positiveP506MatterCurrentFullCoframeResponse 3 3) =
      (125 / 216 : ℝ) := by
  rw [positiveP506MatterCurrentFullCoframeResponse_diagonalCombination_eq_stress,
    positiveP506MatterCurrentFullNonGravityCoframeStress_temporalTracefree]

theorem positiveP506MatterCurrentFullCoframeResponse_temporalSpatial30_eq_5_div_16 :
    positiveP506MatterCurrentFullCoframeResponse 3 0 = (5 / 16 : ℝ) := by
  unfold positiveP506MatterCurrentFullCoframeResponse
  rw [gravityCoupledResponse_temporalSpatial30_eq_half_stress_temporalSpatial03,
    positiveP506MatterCurrentFullNonGravityCoframeStress_temporalSpatial03]
  norm_num

end

end
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermDecision
