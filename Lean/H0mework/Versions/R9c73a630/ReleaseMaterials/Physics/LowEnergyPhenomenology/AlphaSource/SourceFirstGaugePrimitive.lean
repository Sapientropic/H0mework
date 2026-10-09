import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugeScalarOrbit

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstGaugeBackgroundReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationVacuumNativeFieldInjection
open PreparationVacuumNativeLocalWard PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumLowerClassical PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open SourceQuantumScalarChart SourceQuantumFockGauge GaussNativeMatter GaussHistoryHilbert
open StageNineHolonomicField StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource
open StageNineP286InfinitesimalGaugeTransformation StageNineCoframeGravityGaugeRegularity
open StageNineP286GaugeAuxiliaryVariation StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariation StageNineCompactSupportIntegrationByParts
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction StageNineDiracDualYukawaSpinJurisdiction
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open Filter Set
open scoped BigOperators Matrix Topology Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : Fintype P286CoordinateIndex:=StageNineP286InfinitesimalGaugeTransformation.p286CoordinateIndexFintype
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

/-- The same generated temporal Lie element supplies the actual local-gauge parameter. -/
def sourceFirstGaugeParameter : BasePoint→P286CoordinateCarrier :=
  fun _=>show P286CoordinateCarrier from sourceFirstTemporalLie

theorem sourceFirstGaugeParameter_derivative (x : BasePoint) (mu : Fin 4) :
    p286GaugeParameterDerivative sourceFirstGaugeParameter x mu=0 := by
  change (fderiv ℝ (fun _ : BasePoint=>show P286CoordinateCarrier from sourceFirstTemporalLie) x)
    (coordinateDirection mu)=0
  simp only [fderiv_const_apply,zero_apply]

/-- All nine original configuration fields remain explicit, including independent conjugate matter and gauge auxiliary. -/
def sourceFirstGaugePrimitive (c : StageNineHolonomicConfiguration) : StageNineHolonomicConfiguration where
  coframe:=0
  gravityConnection:=0
  gravityAuxiliary:=0
  gravitySimplicityMultiplier:=0
  gaugeConnection x mu:=p286CoordinateEquiv.symm
    (nativeGaugeDirection sourceFirstTemporalLie 0 (actualConnection c x) mu)
  gaugeAuxiliary x pair:=p286LieBracket (p286CoordinateEquiv.symm sourceFirstTemporalLie) (c.gaugeAuxiliary x pair)
  scalar x:=action (c.scalar x) sourceFirstTemporalLie
  matter x:=sourceFirstTemporalGenerator (c.matter x)
  conjugateMatter x:=-(c.conjugateMatter x).comp sourceFirstTemporalGenerator

/-- The connection component is the original gauge transformation, with its actual parameter derivative generated above. -/
theorem sourceFirstGaugePrimitive_connection (c : StageNineHolonomicConfiguration) (x : BasePoint) (mu : Fin 4) :
    p286CoordinateEquiv ((sourceFirstGaugePrimitive c).gaugeConnection x mu)=
      p286InfinitesimalGaugeConnectionDirection c sourceFirstGaugeParameter x mu := by
  change p286CoordinateEquiv (p286CoordinateEquiv.symm
    (nativeGaugeDirection sourceFirstTemporalLie 0 (actualConnection c x) mu))=_
  rw [LinearEquiv.apply_symm_apply,p286InfinitesimalGaugeConnectionDirection,
    sourceFirstGaugeParameter_derivative]
  rfl

theorem sourceFirstGaugePrimitive_scalar (x : BasePoint) :
    (sourceFirstGaugePrimitive actual).scalar x=fieldScalar sourceFirstScalarField := by
  rw [sourceFirstScalarField_return]
  change action (actual.scalar x) sourceFirstTemporalLie=sourceFirstVacuumOrbit
  rw [actual_scalar]
  rfl

theorem sourceFirstGaugePrimitive_independent_pair (c : StageNineHolonomicConfiguration) (x : BasePoint) :
    (sourceFirstGaugePrimitive c).conjugateMatter x (c.matter x)+
      c.conjugateMatter x ((sourceFirstGaugePrimitive c).matter x)=0 := by
  change -c.conjugateMatter x (sourceFirstTemporalGenerator (c.matter x))+
    c.conjugateMatter x (sourceFirstTemporalGenerator (c.matter x))=0
  exact neg_add_cancel _

/-- The actual nonzero scalar orbit and the two independent endpoint variations are consumed together by the original repaired Yukawa Ward identity. -/
theorem sourceFirstGaugePrimitive_scalarWard (c : StageNineHolonomicConfiguration) (x : BasePoint) :
    c.conjugateMatter x (diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm ((sourceFirstGaugePrimitive c).scalar x)) (c.matter x))+
    c.conjugateMatter x (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (c.scalar x))
      ((sourceFirstGaugePrimitive c).matter x))+
    (sourceFirstGaugePrimitive c).conjugateMatter x
      (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (c.scalar x)) (c.matter x))=0 := by
  change c.conjugateMatter x (diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (action (c.scalar x) sourceFirstTemporalLie)) (c.matter x))+
    c.conjugateMatter x (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (c.scalar x))
      (sourceFirstTemporalGenerator (c.matter x)))+
    (-(c.conjugateMatter x).comp sourceFirstTemporalGenerator)
      (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (c.scalar x)) (c.matter x))=0
  rw [scalarAction_mother]
  exact independent_dual_scalar_ward (nativeMother sourceFirstTemporalLie)
    (scalarCoordinateEquiv.symm (c.scalar x)) (c.matter x) (c.conjugateMatter x)

/-- This state tangent is a restriction of the original full configuration variation. -/
def sourceFirstGaugeState : ActionState→ₗ[ℝ]ActionState where
  toFun s:=(0,(fun mu=>nativePrimal sourceFirstTemporalLie*s.2.1 mu-s.2.1 mu*nativePrimal sourceFirstTemporalLie),
    nativePrimal sourceFirstTemporalLie*s.2.2-s.2.2*nativePrimal sourceFirstTemporalLie)
  map_add' a b:=by
    let G:=nativePrimal sourceFirstTemporalLie
    apply Prod.ext
    · simp
    apply Prod.ext
    · funext mu
      change G*(a.2.1 mu+b.2.1 mu)-(a.2.1 mu+b.2.1 mu)*G=
        (G*a.2.1 mu-a.2.1 mu*G)+(G*b.2.1 mu-b.2.1 mu*G)
      noncomm_ring
    · change G*(a.2.2+b.2.2)-(a.2.2+b.2.2)*G=
        (G*a.2.2-a.2.2*G)+(G*b.2.2-b.2.2*G)
      noncomm_ring
  map_smul' r a:=by
    let G:=nativePrimal sourceFirstTemporalLie
    apply Prod.ext
    · simp
    apply Prod.ext
    · funext mu
      change G*(r • a.2.1 mu)-(r • a.2.1 mu)*G=r • (G*a.2.1 mu-a.2.1 mu*G)
      rw [mul_smul_comm,smul_mul_assoc,smul_sub]
    · change G*(r • a.2.2)-(r • a.2.2)*G=r • (G*a.2.2-a.2.2*G)
      rw [mul_smul_comm,smul_mul_assoc,smul_sub]

theorem sourceFirstGaugePrimitive_state (c : StageNineHolonomicConfiguration) (x : BasePoint) :
    configurationState (sourceFirstGaugePrimitive c) x=sourceFirstGaugeState (configurationState c x) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext mu
    change Quantum.operatorMatrix (FullQuantum.connection (sourceFirstGaugePrimitive c) x mu)=
      nativePrimal sourceFirstTemporalLie*Quantum.operatorMatrix (FullQuantum.connection c x mu)-
        Quantum.operatorMatrix (FullQuantum.connection c x mu)*nativePrimal sourceFirstTemporalLie
    rw [originalConnection_source,originalConnection_source]
    change spinCoordinates (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift 0 mu)+
      nativePrimal (show NativeLie from p286CoordinateEquiv (p286CoordinateEquiv.symm
        (nativeGaugeDirection sourceFirstTemporalLie 0 (actualConnection c x) mu)))=_
    rw [LinearEquiv.apply_symm_apply]
    have spinzero : PointwiseDiracSpinConnectionLift.diracSpinConnectionLift 0 mu=0 :=
      (PointwiseDiracSpinConnectionLift.diracSpinConnectionLiftLinear mu).map_zero
    simp only [spinzero,map_zero,zero_add,nativeGaugeDirection,Pi.zero_apply,sub_zero]
    have original:=originalGauge_commutator sourceFirstTemporalLie
      (show NativeLie from p286CoordinateEquiv (c.gaugeConnection x mu))
    change nativePrimal (lie sourceFirstTemporalLie (actualConnection c x mu))=_ at original
    rw [original,mul_add,add_mul,originalSpin_internal_commute]
    abel
  · exact originalScalar_commutator sourceFirstTemporalLie (c.scalar x)

/-- The same full nine-field affine occurrence supplies the original action-state line for every real parameter. -/
theorem sourceFirstGaugePrimitive_ray (c : StageNineHolonomicConfiguration) (x : BasePoint) (r : ℝ) :
    configurationState (configurationRay c (sourceFirstGaugePrimitive c) r) x=
      configurationState c x+r • sourceFirstGaugeState (configurationState c x) := by
  rw [configurationState_ray,sourceFirstGaugePrimitive_state]

/-- The field-dependent contact is generated on the same original configuration line, rather than set to zero. -/
theorem sourceFirstGaugePrimitive_contact (c d : StageNineHolonomicConfiguration) (x : BasePoint) :
    HasDerivAt (fun r : ℝ=>configurationState (sourceFirstGaugePrimitive (configurationRay c d r)) x)
      (sourceFirstGaugeState (configurationState d x)) 0 := by
  have generated:=state_line (sourceFirstGaugeState (configurationState c x))
    (sourceFirstGaugeState (configurationState d x))
  simpa only [sourceFirstGaugePrimitive_state,configurationState_ray,map_add,map_smul] using generated

/-- Both original curvature legs survive the actual constant-parameter gauge Jacobi identity. -/
theorem sourceFirstGaugePrimitive_curvature (c : StageNineHolonomicConfiguration)
    (f : BasePoint→P286GaugeOneForm) (x : BasePoint) (pair : Fin 6) :
    curvatureSecond (actualForce f x)
        (fun mu=>show NativeLie from p286CoordinateEquiv ((sourceFirstGaugePrimitive c).gaugeConnection x mu)) pair+
      curvatureFirst (actualConnection c x)
        (nativeGaugeContact sourceFirstTemporalLie (actualForce f x))
        (nativeGaugeContactDerivative sourceFirstTemporalLie 0 (actualForce f x) (actualForceDerivative f x)) pair=
      lie sourceFirstTemporalLie
        (show NativeLie from p286GaugeConnectionLinearCurvatureVariation c f x pair) := by
  have original:=nativeCurvature_mixed sourceFirstTemporalLie 0 (actualConnection c x)
    (actualForce f x) (actualForceDerivative f x) pair
  simpa only [sourceFirstGaugePrimitive,LinearEquiv.apply_symm_apply,
    curvatureFirst_original] using original

end LowEnergy.PreparationPhysicalFirstGaugeBackgroundReturn
