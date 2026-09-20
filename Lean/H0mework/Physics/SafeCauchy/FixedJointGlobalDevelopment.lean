import H0mework.Physics.JointVariation.CauchySafeScalarTemporalDevelopment
import H0mework.Physics.JointVariation.P286LiveElectricCauchyOperator
import H0mework.Physics.ConstitutiveAction.ResponseOperator
import H0mework.Physics.CoframeVariation.CoframeECContactLocalActualLift
import H0mework.Physics.SafeCauchy.FixedGlobalOperator
import H0mework.Physics.DualVariation.PointwiseActionJetCarrier
import H0mework.Physics.Coframe.CoframeNativeMatterDualGlobalRadialActionWrite
import H0mework.Physics.Exterior.GravityReactionInstallation
import H0mework.Physics.Holonomic.HolonomicGaugeCurvatureTransport
import H0mework.Physics.Jets.RadialCurveIntegralFirstJet

/-!
# Fixed P506/L0 Cauchy-safe joint global development

This module composes the existing mother-action writers into one concrete
whole-spacetime occurrence.  The EC leg integrates the connection first jets
emitted by the already-developed temporal/constitutive/P286 current, then the
reaction is recomputed on that exact global connection.  No residual,
assembly seam, target field, closedness receipt, or branch is an input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCoframeNativeMatterDualGlobalRadialActionWrite
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeGravityReactionInstallation
open StageNineGlobalIntegratedAction
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineRadialCurveIntegralFirstJet
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance cauchySafeJointGlobalP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance cauchySafeJointGlobalP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## The one dependency-ordered whole-field write -/

def cauchySafeJointGlobalTemporalCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
    source current

def cauchySafeJointGlobalConstitutiveCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeConstitutiveWrittenCurrent source
    (cauchySafeJointGlobalTemporalCurrent source current)

/-- The full P286 first jet emitted by the same mother-action occurrence at
one spacetime contact.  Unlike the older time-only Cauchy primitive, this
carrier includes the spatial `123` leg before integration. -/
def cauchySafeJointGlobalP286JetCLM
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (contact : BasePoint) : BasePoint →L[ℝ] P286GaugeTwoForm :=
  formNativeP286CanonicalAuxiliaryIncrement
    (completeJointP286RequiredExteriorProfile source preP286 contact)

theorem cauchySafeJointGlobalP286JetCLM_coordinate
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (direction : LorentzianIndex) :
    cauchySafeJointGlobalP286JetCLM source preP286 contact
        (coordinateDirection direction) =
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
        (completeJointP286RequiredExteriorProfile source preP286 contact)
        direction := by
  fin_cases direction <;>
    simp [cauchySafeJointGlobalP286JetCLM,
      formNativeP286CanonicalAuxiliaryIncrement, localBaseCoordinate,
      coordinateDirection, Fin.sum_univ_four]

private def cauchySafeJointGlobalP286DerivativeLinear
    (direction : LorentzianIndex) :
    P286GaugeThreeForm →ₗ[ℝ] P286GaugeTwoForm where
  toFun := fun target =>
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm target direction
  map_add' := by
    intro first second
    funext pair
    fin_cases direction <;> fin_cases pair <;>
      simp [formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm]
    all_goals module
  map_smul' := by
    intro parameter target
    funext pair
    fin_cases direction <;> fin_cases pair <;>
      simp [formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm]
    all_goals module

private def cauchySafeJointGlobalP286JetCompilerLinear :
    P286GaugeThreeForm →ₗ[ℝ] (BasePoint →L[ℝ] P286GaugeTwoForm) where
  toFun := formNativeP286CanonicalAuxiliaryIncrement
  map_add' := by
    intro first second
    unfold formNativeP286CanonicalAuxiliaryIncrement
    simp_rw [show ∀ direction,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
          (first + second) direction =
        formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
            first direction +
          formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
            second direction from fun direction =>
      (cauchySafeJointGlobalP286DerivativeLinear direction).map_add
        first second]
    ext point pair coordinate
    simp
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro parameter target
    unfold formNativeP286CanonicalAuxiliaryIncrement
    simp_rw [show ∀ direction,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
          (parameter • target) direction =
        parameter •
          formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
            target direction from fun direction =>
      (cauchySafeJointGlobalP286DerivativeLinear direction).map_smul
        parameter target]
    ext point pair coordinate
    simp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro direction _
    ring

private def cauchySafeJointGlobalP286JetCompilerCLM :
    P286GaugeThreeForm →L[ℝ] (BasePoint →L[ℝ] P286GaugeTwoForm) :=
  cauchySafeJointGlobalP286JetCompilerLinear.toContinuousLinearMap

theorem cauchySafeJointGlobalP286JetCLM_contDiffAt_of_required
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (requiredRegular : ContDiffAt ℝ 0
      (completeJointP286RequiredExteriorProfile source preP286) point) :
    ContDiffAt ℝ 0
      (cauchySafeJointGlobalP286JetCLM source preP286) point := by
  rw [show
    cauchySafeJointGlobalP286JetCLM source preP286 =
      fun contact => cauchySafeJointGlobalP286JetCompilerCLM
        (completeJointP286RequiredExteriorProfile source preP286 contact) by
    rfl]
  exact cauchySafeJointGlobalP286JetCompilerCLM.contDiff.contDiffAt.comp
    point requiredRegular

theorem cauchySafeJointGlobalP286JetCLM_contDiff_of_required
    {n : WithTop ℕ∞}
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (requiredRegular : ContDiff ℝ n
      (completeJointP286RequiredExteriorProfile source preP286)) :
    ContDiff ℝ n
      (cauchySafeJointGlobalP286JetCLM source preP286) := by
  rw [show
    cauchySafeJointGlobalP286JetCLM source preP286 =
      fun contact => cauchySafeJointGlobalP286JetCompilerCLM
        (completeJointP286RequiredExteriorProfile source preP286 contact) by
    rfl]
  exact cauchySafeJointGlobalP286JetCompilerCLM.contDiff.comp requiredRegular

/-- Radial whole-field descent of the complete action-owned P286 first jet.
Closedness is deliberately not a constructor premise. -/
def cauchySafeJointGlobalP286RadialIncrement
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  ∫ᶜ contact in Path.segment (0 : BasePoint) point,
    cauchySafeJointGlobalP286JetCLM source preP286 contact

@[simp] theorem cauchySafeJointGlobalP286RadialIncrement_zero
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration) :
    cauchySafeJointGlobalP286RadialIncrement source preP286 0 = 0 := by
  funext pair
  simp [cauchySafeJointGlobalP286RadialIncrement]

def cauchySafeJointGlobalP286CoordinateField
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  holonomicP286GaugeAuxiliaryCoordinate preP286 0 +
    cauchySafeJointGlobalP286RadialIncrement source preP286 point

/-- One source/current-only global P286 write.  The action profile emits the
jet; its radial primitive emits the field.  No residual or support coordinate
is read by this constructor. -/
def sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { preP286 with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        (cauchySafeJointGlobalP286CoordinateField
          source preP286 point pair) }

theorem sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_coordinate
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          source preP286) point =
      cauchySafeJointGlobalP286CoordinateField source preP286 point := by
  funext pair
  exact p286CoordinateEquiv.apply_symm_apply _

@[simp] theorem
    sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_coordinate_zero
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          source preP286) 0 =
      holonomicP286GaugeAuxiliaryCoordinate preP286 0 := by
  rw [sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_coordinate]
  simp [cauchySafeJointGlobalP286CoordinateField]

theorem cauchySafeJointGlobalP286RadialIncrement_hasFDerivAt_zero
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cauchySafeJointGlobalP286JetCLM source preP286) 0) :
    HasFDerivAt
      (cauchySafeJointGlobalP286RadialIncrement source preP286)
      (cauchySafeJointGlobalP286JetCLM source preP286 0) 0 :=
  radialCurveIntegral_hasFDerivAt_zero_of_contDiffAt
    (cauchySafeJointGlobalP286JetCLM source preP286) regular

theorem cauchySafeJointGlobalP286CoordinateField_hasFDerivAt_zero
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cauchySafeJointGlobalP286JetCLM source preP286) 0) :
    HasFDerivAt (cauchySafeJointGlobalP286CoordinateField source preP286)
      (cauchySafeJointGlobalP286JetCLM source preP286 0) 0 := by
  exact (cauchySafeJointGlobalP286RadialIncrement_hasFDerivAt_zero
    source preP286 regular).const_add
      (holonomicP286GaugeAuxiliaryCoordinate preP286 0)

theorem
    sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_auxiliaryDerivative_origin
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cauchySafeJointGlobalP286JetCLM source preP286) 0)
    (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          source preP286) 0 direction =
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
        (completeJointP286RequiredExteriorProfile source preP286 0)
        direction := by
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          source preP286) =
      cauchySafeJointGlobalP286CoordinateField source preP286 by
    funext point
    exact
      sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_coordinate
        source preP286 point]
  rw [(cauchySafeJointGlobalP286CoordinateField_hasFDerivAt_zero
    source preP286 regular).fderiv]
  exact cauchySafeJointGlobalP286JetCLM_coordinate
    source preP286 0 direction

theorem
    sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_exteriorDerivative_origin
    (source : SmoothUnifiedSource)
    (preP286 : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cauchySafeJointGlobalP286JetCLM source preP286) 0) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          source preP286) 0 =
      completeJointP286RequiredExteriorProfile source preP286 0 := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  rw [show
    p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          source preP286) 0 =
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
        (completeJointP286RequiredExteriorProfile source preP286 0) by
    funext direction
    exact
      sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_auxiliaryDerivative_origin
        source preP286 regular direction]
  exact pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_canonical _

def cauchySafeJointGlobalP286Current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite source
    (cauchySafeJointGlobalConstitutiveCurrent source current)

/-- The EC contact producer is recomputed from the already developed
temporal/constitutive/P286 current at the actual global contact. -/
def cauchySafeJointGlobalECProfileContact
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
    source preEC contact

theorem cauchySafeJointGlobalECProfileContact_connection_contact
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (cauchySafeJointGlobalECProfileContact source preEC contact
      ).gravityConnection contact = preEC.gravityConnection contact := by
  exact
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact
      source preEC contact

theorem cauchySafeJointGlobalECProfileContact_curvature_contact
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicGravityCurvature
        (cauchySafeJointGlobalECProfileContact source preEC contact) contact =
      diracDualFormNativeCoframeECContactCurvatureTarget
        source preEC contact := by
  exact
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_curvature_contact
      source preEC contact

def cauchySafeJointGlobalECLoweredConnectionFirstJet
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) : ℝ :=
  minkowskiInternalSign (pairFirst internalPair) *
    gravityConnectionDerivative
      (cauchySafeJointGlobalECProfileContact source preEC contact)
      contact derivativeDirection formDirection
      (pairFirst internalPair) (pairSecond internalPair)

def cauchySafeJointGlobalECJetOneForm
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection : LorentzianIndex) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    cauchySafeJointGlobalECLoweredConnectionFirstJet source preEC contact
      derivativeDirection formDirection internalPair

def cauchySafeJointGlobalECJetCLM
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (contact : BasePoint) : BasePoint →L[ℝ] LorentzBivectorOneForm :=
  ∑ derivativeDirection : LorentzianIndex,
    (baseCoordinate derivativeDirection).smulRight
      (cauchySafeJointGlobalECJetOneForm source preEC contact
        derivativeDirection)

theorem cauchySafeJointGlobalECJetCLM_coordinate
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection : LorentzianIndex) :
    cauchySafeJointGlobalECJetCLM source preEC contact
        (coordinateDirection derivativeDirection) =
      cauchySafeJointGlobalECJetOneForm source preEC contact
        derivativeDirection := by
  fin_cases derivativeDirection <;>
    ext formDirection internalPair <;>
    simp [cauchySafeJointGlobalECJetCLM, baseCoordinate,
      coordinateDirection, Fin.sum_univ_four]

def cauchySafeJointGlobalECRadialIncrement
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (point : BasePoint) : LorentzBivectorOneForm :=
  ∫ᶜ contact in Path.segment (0 : BasePoint) point,
    cauchySafeJointGlobalECJetCLM source preEC contact

@[simp] theorem cauchySafeJointGlobalECRadialIncrement_zero
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration) :
    cauchySafeJointGlobalECRadialIncrement source preEC 0 = 0 := by
  funext formDirection internalPair
  simp [cauchySafeJointGlobalECRadialIncrement]

def cauchySafeJointGlobalECConnectionField
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration) : LorentzConnectionField :=
  fun point =>
    preEC.gravityConnection 0 +
      lorentzSkewConnectionOfBivectorOneForm
        (cauchySafeJointGlobalECRadialIncrement source preEC point)

@[simp] theorem cauchySafeJointGlobalECConnectionField_zero
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration) :
    cauchySafeJointGlobalECConnectionField source preEC 0 =
      preEC.gravityConnection 0 := by
  funext formDirection internalOut internalIn
  simp [cauchySafeJointGlobalECConnectionField]

/-- The EC descent writes one global primitive connection and recomputes
`B = II+(e)` on that same output. -/
def sourceActionGeneratedDiracDualCauchySafeGlobalECPathWrite
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { preEC with
    gravityConnection := cauchySafeJointGlobalECConnectionField source preEC
    gravityAuxiliary := fun point =>
      physicalIIPlusBivector (preEC.coframe point) }

def cauchySafeJointGlobalECPathCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCauchySafeGlobalECPathWrite source
    (cauchySafeJointGlobalP286Current source current)

/-- Recompute the ordered primal/adjoint frame laws on the exact emitted EC
path actual before the gravity reaction is read again. -/
def cauchySafeJointGlobalMatterDualCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  actionGeneratedGlobalFrameMatterDualActual
    (cauchySafeJointGlobalECPathCurrent source current)

theorem cauchySafeJointGlobalECRadialIncrement_hasFDerivAt_zero
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cauchySafeJointGlobalECJetCLM source preEC) 0) :
    HasFDerivAt (cauchySafeJointGlobalECRadialIncrement source preEC)
      (cauchySafeJointGlobalECJetCLM source preEC 0) 0 := by
  exact radialCurveIntegral_hasFDerivAt_zero_of_contDiffAt
    (cauchySafeJointGlobalECJetCLM source preEC) regular

theorem cauchySafeJointGlobalECConnectionField_hasFDerivAt_zero
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cauchySafeJointGlobalECJetCLM source preEC) 0) :
    HasFDerivAt (cauchySafeJointGlobalECConnectionField source preEC)
      (radialLorentzConnectionLiftCLM.comp
        (cauchySafeJointGlobalECJetCLM source preEC 0)) 0 := by
  change HasFDerivAt
    (fun endpoint =>
      preEC.gravityConnection 0 +
        radialLorentzConnectionLiftCLM
          (cauchySafeJointGlobalECRadialIncrement source preEC endpoint)) _ 0
  have lifted :=
    radialLorentzConnectionLiftCLM.hasFDerivAt.comp 0
      (cauchySafeJointGlobalECRadialIncrement_hasFDerivAt_zero
        source preEC regular)
  convert lifted.const_add (preEC.gravityConnection 0) using 1 <;> rfl

theorem
    sourceActionGeneratedDiracDualCauchySafeGlobalECPathWrite_loweredConnectionFirstJet_eq_profile
    (source : SmoothUnifiedSource)
    (preEC : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cauchySafeJointGlobalECJetCLM source preEC) 0)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (sourceActionGeneratedDiracDualCauchySafeGlobalECPathWrite
            source preEC)
          0 derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      cauchySafeJointGlobalECLoweredConnectionFirstJet source preEC 0
        derivativeDirection formDirection internalPair := by
  unfold gravityConnectionDerivative
  change
    minkowskiInternalSign (pairFirst internalPair) *
        fderiv ℝ
          (fun endpoint =>
            cauchySafeJointGlobalECConnectionField source preEC endpoint
              formDirection (pairFirst internalPair) (pairSecond internalPair))
          0 (coordinateDirection derivativeDirection) = _
  have coordinateDerivative :
      HasFDerivAt
        (fun endpoint =>
          cauchySafeJointGlobalECConnectionField source preEC endpoint
            formDirection (pairFirst internalPair) (pairSecond internalPair))
        ((radialLorentzConnectionCoordinateCLM formDirection
          (pairFirst internalPair) (pairSecond internalPair)).comp
            (radialLorentzConnectionLiftCLM.comp
              (cauchySafeJointGlobalECJetCLM source preEC 0))) 0 := by
    exact
      (radialLorentzConnectionCoordinateCLM formDirection
        (pairFirst internalPair) (pairSecond internalPair)).hasFDerivAt.comp 0
        (cauchySafeJointGlobalECConnectionField_hasFDerivAt_zero
          source preEC regular)
  rw [coordinateDerivative.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    cauchySafeJointGlobalECJetCLM_coordinate]
  exact loweredLorentzConnectionCoefficient_ofBivectorOneForm
    (cauchySafeJointGlobalECJetOneForm source preEC 0 derivativeDirection)
    formDirection internalPair

inductive CauchySafeJointGlobalWriteLeg where
  | temporal
  | constitutive
  | p286
  | ecPath
  | matterDual
  | reaction
  deriving DecidableEq

def cauchySafeJointGlobalActionWrite
    (source : SmoothUnifiedSource)
    (leg : CauchySafeJointGlobalWriteLeg)
    (before : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  match leg with
  | .temporal =>
      sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
        source before
  | .constitutive =>
      diracDualFormNativeConstitutiveWrittenCurrent source before
  | .p286 =>
      sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
        source before
  | .ecPath =>
      sourceActionGeneratedDiracDualCauchySafeGlobalECPathWrite source before
  | .matterDual => actionGeneratedGlobalFrameMatterDualActual before
  | .reaction => installFormNativeGravityReaction before

inductive CauchySafeJointGlobalOccurrence
    (_source : SmoothUnifiedSource)
    (_current : StageNineHolonomicConfiguration) where
  | generated

namespace CauchySafeJointGlobalOccurrence

def before
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (_occurrence : CauchySafeJointGlobalOccurrence source current) :
    CauchySafeJointGlobalWriteLeg → StageNineHolonomicConfiguration
  | .temporal => current
  | .constitutive => cauchySafeJointGlobalTemporalCurrent source current
  | .p286 => cauchySafeJointGlobalConstitutiveCurrent source current
  | .ecPath => cauchySafeJointGlobalP286Current source current
  | .matterDual => cauchySafeJointGlobalECPathCurrent source current
  | .reaction => cauchySafeJointGlobalMatterDualCurrent source current

def after
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CauchySafeJointGlobalOccurrence source current)
    (leg : CauchySafeJointGlobalWriteLeg) : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalActionWrite source leg (occurrence.before leg)

theorem after_eq_actionWrite
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CauchySafeJointGlobalOccurrence source current)
    (leg : CauchySafeJointGlobalWriteLeg) :
    occurrence.after leg =
      cauchySafeJointGlobalActionWrite source leg (occurrence.before leg) :=
  rfl

abbrev finalActual
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CauchySafeJointGlobalOccurrence source current) :
    StageNineHolonomicConfiguration :=
  occurrence.after .reaction

end CauchySafeJointGlobalOccurrence

def sourceActionGeneratedCauchySafeJointGlobalOccurrence
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    CauchySafeJointGlobalOccurrence source current :=
  .generated

def sourceActionGeneratedDiracDualCauchySafeJointGlobalOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  (sourceActionGeneratedCauchySafeJointGlobalOccurrence source current
    ).finalActual

/-! ## Fixed P506/L0 specialization -/

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source
    fixedP506L0CartanECConstraintCauchySafePreparedActual

def fixedP506L0CartanECConstraintCauchySafeJointGlobalOccurrence :
    CauchySafeJointGlobalOccurrence Source Current :=
  sourceActionGeneratedCauchySafeJointGlobalOccurrence Source Current

def fixedP506L0CartanECConstraintCauchySafeJointGlobalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCauchySafeJointGlobalOperator Source Current

/-- The exact EC contact read by the global EC leg at one spacetime point. -/
def fixedP506L0CartanECConstraintCauchySafeJointGlobalECProfileContact
    (point : BasePoint) : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalECProfileContact Source
    (cauchySafeJointGlobalP286Current Source Current) point

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_eq_occurrence :
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual =
      fixedP506L0CartanECConstraintCauchySafeJointGlobalOccurrence.finalActual :=
  rfl

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe :
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.coframe =
      Current.coframe :=
  rfl

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_nondegenerate :
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.Nondegenerate := by
  intro point
  rw [fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe]
  change Matrix.det
      (fixedP506L0CartanECConstraintCauchySafePreparedActual.coframe point) ≠ 0
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate point

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_noncharacteristic
    (point : BasePoint) :
    coframeTemporalPrincipalScalar
        (fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.coframe point) ≠
      0 := by
  rw [fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe]
  change coframeTemporalPrincipalScalar
      (fixedP506L0CartanECConstraintCauchySafePreparedActual.coframe point) ≠ 0
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_noncharacteristic
      point

/-- The single common global occurrence retains the source-generated strict
positive coordinate-time coefficient used by the exact evolution law. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coordinateTimeEvolutionPrincipal_posDef
    (point : BasePoint) :
    (coframeCoordinateDiracEvolutionPrincipal
      (fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.coframe point)
      0).PosDef := by
  rw [fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe]
  change
    (coframeCoordinateDiracEvolutionPrincipal
      (fixedP506L0CartanECConstraintCauchySafePreparedActual.coframe point)
      0).PosDef
  simpa only [fixedP506L0CartanECConstraintCauchySafeGlobalActual_coframe]
    using
      fixedP506L0CartanECConstraintCauchySafeGlobalActual_coordinateTimeEvolutionPrincipal_posDef
        point

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_simplicity :
    FormNativeGravitySimplicityEquation
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual := by
  intro point
  rfl

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_reactionSelfGenerated :
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.gravitySimplicityMultiplier =
      formNativeGravityReactionField
        fixedP506L0CartanECConstraintCauchySafeJointGlobalActual := by
  exact installFormNativeGravityReaction_reactionSelfGenerated _

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_auxiliaryEquation :
    FormNativeGravityAuxiliaryEquation
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual := by
  exact installFormNativeGravityReaction_auxiliaryEquation _

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_fieldInventory :
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.coframe =
        Current.coframe ∧
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.gravityConnection =
        cauchySafeJointGlobalECConnectionField Source
          (cauchySafeJointGlobalP286Current Source Current) ∧
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.gravityAuxiliary =
        (fun point => physicalIIPlusBivector (Current.coframe point)) ∧
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.gravitySimplicityMultiplier =
        formNativeGravityReactionField
          fixedP506L0CartanECConstraintCauchySafeJointGlobalActual ∧
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.gaugeConnection =
        (cauchySafeJointGlobalP286Current Source Current).gaugeConnection ∧
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.gaugeAuxiliary =
        (cauchySafeJointGlobalP286Current Source Current).gaugeAuxiliary ∧
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.scalar =
        (cauchySafeJointGlobalTemporalCurrent Source Current).scalar ∧
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.matter =
        (actionGeneratedGlobalFrameTimeMatterActual
          (cauchySafeJointGlobalECPathCurrent Source Current)).matter ∧
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.conjugateMatter =
        (cauchySafeJointGlobalMatterDualCurrent Source Current
          ).conjugateMatter := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_reactionSelfGenerated

/-! ## Exhaustive whole-action-jet changed-read -/

/-- Replace exactly the gravity--matter reads that the global EC path and
live-reaction legs can change relative to their matching EC contact.  This is
an action-jet readout, not a state constructor or residual-built write. -/
def pointwiseActionJetWithCauchySafeJointChangedReads
    (contactJet actualJet : DiracDualFormNativePointwiseActionJetCarrier) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  { contactJet with
    pointField :=
      { contactJet.pointField with
        gravityCurvature := actualJet.pointField.gravityCurvature
        gravitySimplicityMultiplier :=
          actualJet.pointField.gravitySimplicityMultiplier
        matter := actualJet.pointField.matter
        matterCovariantDerivative :=
          actualJet.pointField.matterCovariantDerivative
        conjugateMatter := actualJet.pointField.conjugateMatter }
    gravityConnection := actualJet.gravityConnection
    gravityAuxiliaryExteriorCovariantDerivative :=
      actualJet.gravityAuxiliaryExteriorCovariantDerivative
    matterDifferentialMomentumDivergence :=
      actualJet.matterDifferentialMomentumDivergence }

private abbrev PreEC : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalP286Current Source Current

private abbrev Final : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual

private abbrev Contact (point : BasePoint) : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalECProfileContact point

private theorem preEC_coframe_eq_current :
    PreEC.coframe = Current.coframe :=
  rfl

private theorem final_coframe_eq_contact (point : BasePoint) :
    Final.coframe = (Contact point).coframe := by
  rw [fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe]
  change Current.coframe =
    (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
      Source PreEC point).coframe
  rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
    preEC_coframe_eq_current]

private theorem final_gravityAuxiliary_eq_contact (point : BasePoint) :
    Final.gravityAuxiliary = (Contact point).gravityAuxiliary :=
  rfl

private theorem final_gaugeConnection_eq_contact (point : BasePoint) :
    Final.gaugeConnection = (Contact point).gaugeConnection :=
  rfl

private theorem final_gaugeAuxiliary_eq_contact (point : BasePoint) :
    Final.gaugeAuxiliary = (Contact point).gaugeAuxiliary :=
  rfl

private theorem final_scalar_eq_contact (point : BasePoint) :
    Final.scalar = (Contact point).scalar :=
  rfl

private theorem final_scalarCovariantDerivative_eq_contact
    (point : BasePoint) :
    holonomicScalarCovariantDerivative Final =
      holonomicScalarCovariantDerivative (Contact point) := by
  funext candidate direction
  unfold holonomicScalarCovariantDerivative
  rw [final_scalar_eq_contact point,
    final_gaugeConnection_eq_contact point]

private theorem final_p286GaugeAuxiliaryExterior_eq_contact
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Final =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (Contact point) := by
  funext candidate
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    StageNineP286GaugeConnectionVariation.holonomicP286GaugeConnectionCoordinate
    StageNineP286GaugeAuxiliaryVariation.holonomicP286GaugeAuxiliaryCoordinate
  rw [final_gaugeConnection_eq_contact point,
    final_gaugeAuxiliary_eq_contact point]

private theorem final_scalarDifferentialMomentum_eq_contact
    (point : BasePoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum Source Final direction derivativeDirection =
      scalarDifferentialMomentum Source (Contact point) direction
        derivativeDirection := by
  funext candidate
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [final_coframe_eq_contact point,
    final_scalarCovariantDerivative_eq_contact point]

private theorem final_scalarDifferentialMomentumDivergence_eq_contact
    (point : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source Final direction =
      scalarDifferentialMomentumDivergence Source (Contact point) direction := by
  funext candidate
  unfold scalarDifferentialMomentumDivergence
  simp_rw [final_scalarDifferentialMomentum_eq_contact point]

/-- The six replaced slots exhaust the changed reads of the one global
joint write at every spacetime occurrence. -/
theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_actionJet_eq_jointChangedReadout
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet Source Final point =
      pointwiseActionJetWithCauchySafeJointChangedReads
        (generatedDiracDualFormNativePointwiseActionJet Source
          (Contact point) point)
        (generatedDiracDualFormNativePointwiseActionJet Source Final point) := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext
    · exact congrFun (final_coframe_eq_contact point) point
    · rfl
    · exact congrFun (final_gravityAuxiliary_eq_contact point) point
    · rfl
    · exact holonomicGaugeCurvature_eq_of_connection_eq Final (Contact point)
        (final_gaugeConnection_eq_contact point) point
    · exact congrFun (final_gaugeAuxiliary_eq_contact point) point
    · exact congrFun (final_scalar_eq_contact point) point
    · exact congrFun (final_scalarCovariantDerivative_eq_contact point) point
    · rfl
    · rfl
    · rfl
  · rfl
  · exact congrFun (final_gaugeConnection_eq_contact point) point
  · rfl
  · exact congrFun (final_p286GaugeAuxiliaryExterior_eq_contact point) point
  · funext direction
    exact congrFun
      (final_scalarDifferentialMomentumDivergence_eq_contact point direction)
      point
  · rfl

/-- The complete nine-coordinate residual is one deterministic readout of
the matching EC contact jet plus the exhaustive joint changed-read carrier. -/
theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_residual_eq_jointChangedReadout
    (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual Source Final point =
      diracDualFormNativeJointResidualOfActionJet Source point
        (pointwiseActionJetWithCauchySafeJointChangedReads
          (generatedDiracDualFormNativePointwiseActionJet Source
            (Contact point) point)
          (generatedDiracDualFormNativePointwiseActionJet Source Final
            point)) := by
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout]
  exact congrArg (diracDualFormNativeJointResidualOfActionJet Source point)
    (fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_actionJet_eq_jointChangedReadout
      point)

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_exactLineage :
    Source.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506L0CartanECConstraintCauchySafeGlobalActual_exactLineage

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
