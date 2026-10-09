import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeScalarEulerIdentification
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationMotherConnectionDirections

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeLorentzConnectionVariation
open StageNineFormNativeLorentzConnectionLocalVariation StageNineLorentzConnectionActualVariationCore StageNineLorentzConnectionVariation
open StageNineFormNativeLorentzDerivativeIntegrationByParts StageNineFormNativeP286GaugeDerivativeIntegrationByParts
open StageNineTopologicalGravityCurvatureVariancePairing StageNineTopologicalFourFormPairing
open StageNineFormNativeGravityMultiplierAuxiliaryVariation StageNineMatterCovariantDerivativeAffine
open StageNineDynamicBreakingVacuum StageNineCompactSupportIntegrationByParts
open StageNineDiracDualFormNativeJointResidualCarrier StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics StageNineTopologicalLorentzThreeFormDuality
open StageNineP286GaugeConnectionVariation StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineTopologicalP286GaugeThreeFormDuality StageNineP286GaugeAuxiliaryVariation
open StageNineGravityBianchi Filter Stage9C.Material.SpinPair
open StageNineFormNativeP286GaugeConnectionLocalVariation StageNineP286GaugeConnectionActionVariation
open StageNineFormNativeGaugeWedge SU7MotherLieAlgebra StageNineFormNativeMotherAction
open StageNineDiracMatterCoordinateCalculus PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeSourceRestriction PreparationVacuumLowerClassical
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd:=inferInstance
  toContinuousNeg:=inferInstance
attribute [local irreducible] nativeJetDensity nativePoint nativeConfiguration nativeDensity
  SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual

def nativeConnectionSlopeShift (jet : NativeFirstJet) (force : Field289) (mu : Fin 4) (a : ℝ) : NativeFirstJet :=
  (jet.1,jet.2+a • (Pi.single mu force : Fin 4→Field289))

private theorem connectionSlope_derivative (jet : NativeFirstJet) (force : Field289) (mu : Fin 4)
    (inside : jet∈nativeEulerSourceDomain) :
    HasDerivAt (fun a : ℝ=>nativeJetDensity (nativeConnectionSlopeShift jet force mu a))
      (fderiv ℝ nativeJetDensity jet (0,Pi.single mu force)) 0 := by
  have regular : ContDiffAt ℝ 2 nativeJetDensity jet := inside
  have ray : HasDerivAt (fun a : ℝ=>nativeConnectionSlopeShift jet force mu a) (0,Pi.single mu force) 0 := by
    have source:=((hasDerivAt_id (0 : ℝ)).smul_const (0,Pi.single mu force)).const_add jet
    convert! source using 1
    · funext a
      apply Prod.ext
      · simp [nativeConnectionSlopeShift]
      · rfl
    · simp only [one_smul]
  exact (regular.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ray
    (by simp [nativeConnectionSlopeShift])

/-- The original lowered curvature direction keeps COV-1 inside the source BF coefficient exactly once. -/
theorem nativeLorentzCurvatureCurve_generated (point : BasePoint) (field : StageNineContinuumPointField)
    (mu : Fin 4) (direction : LorentzBivectorOneForm) :
    HasDerivAt (fun a : ℝ=>motherDensityAt point (withLorentzConnectionJets field
      (field.gravityCurvature+a • loweredLorentzExteriorDerivativeDirection mu direction)
      field.matterCovariantDerivative))
      (gravityExteriorPrincipalBilinear mu field.gravityAuxiliary direction) 0 := by
  have formula : (fun a : ℝ=>motherDensityAt point (withLorentzConnectionJets field
      (field.gravityCurvature+a • loweredLorentzExteriorDerivativeDirection mu direction) field.matterCovariantDerivative))=
      fun a : ℝ=>motherDensityAt point field+a*gravityTopologicalBFCoefficient field.gravityAuxiliary
        (loweredLorentzExteriorDerivativeDirection mu direction) := by
    funext a
    have matterZero : matterCovariantDerivativeFirstVariationDensity positiveSmoothUnifiedSource 0 point field 0=0 := by
      have additive:=matterCovariantDerivativeFirstVariationDensity_add positiveSmoothUnifiedSource 0 point field 0 0
      simp only [add_zero] at additive
      linarith
    have bfZero : gravityTopologicalBFCoefficient field.gravityAuxiliary 0=0 := by
      have additive:=gravityTopologicalBFCoefficient_add_right field.gravityAuxiliary 0 0
      simp only [add_zero] at additive
      linarith
    have law:=generatedDiracDualFormNativeUnifiedLocalDensity_lorentzConnectionJets_quadratic positiveSmoothUnifiedSource
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) 0 point field
      (loweredLorentzExteriorDerivativeDirection mu direction) 0 0 a
    have matterSmulZero : a • (0 : Fin 4→DiracExteriorMatterCarrier)=0 := by
      funext nu
      change (a : ℂ) • (0 : DiracExteriorMatterCarrier)=0
      exact smul_zero (a : ℂ)
    simpa only [motherDensityAt,smul_zero,matterSmulZero,add_zero,formNativeLorentzConnectionFirstVariationDensity,
      formNativeLorentzConnectionSecondVariationDensity,matterZero,bfZero,mul_zero] using law
  rw [formula]
  convert! ((hasDerivAt_id (0 : ℝ)).mul_const (gravityTopologicalBFCoefficient field.gravityAuxiliary
    (loweredLorentzExteriorDerivativeDirection mu direction))).const_add (motherDensityAt point field) using 1
  simp only [one_mul,gravityExteriorPrincipalBilinear_apply]

def lorentzSupported (force : Field289) : Prop := ∀ field : Fin 289,
  ¬(121≤field.val ∧ field.val<145)→force field=0

private theorem lorentzSupported_gauge (force : Field289) (supported : lorentzSupported force) (nu : Fin 4) :
    fieldGauge force nu=0 := by
  unfold fieldGauge
  have each (a : Fin 12) : force (gaugeSlot nu a)=0 := supported _ (by simp only [gaugeSlot];omega)
  simp only [each,zero_smul,Finset.sum_const_zero]

private theorem lorentzSupported_scalar (force : Field289) (supported : lorentzSupported force) : fieldScalar force=0 := by
  unfold fieldScalar
  have each (a : Fin 9) : force (scalarSlot a)=0 := supported _ (by simp only [scalarSlot];omega)
  simp only [each,zero_smul,Finset.sum_const_zero]

private theorem lorentzSupported_primal (force : Field289) (supported : lorentzSupported force) (spin : Fin 4) (color : Fin 3) :
    primalCoefficientCLM spin color force=0 := by
  have each (part : Fin 2) : fieldPrimal force part spin color=0 := supported _ (by simp only [primalSlot];omega)
  change fieldPrimalComplex force spin color=0
  simp only [fieldPrimalComplex,each,Complex.ofReal_zero,mul_zero,add_zero]

private theorem lorentzSlope_gauge (jet : NativeFirstJet) (force : Field289) (supported : lorentzSupported force)
    (mu : Fin 4) (a : ℝ) (nu rho : Fin 4) :
    fieldGauge (jet.2 nu+a • (Pi.single mu force : Fin 4→Field289) nu) rho=fieldGauge (jet.2 nu) rho := by
  by_cases same : nu=mu
  · simp only [Pi.single_apply,if_pos same,fieldGauge_add,fieldGauge_smul,lorentzSupported_gauge force supported,smul_zero,add_zero]
  · simp only [Pi.single_apply,if_neg same,smul_zero,add_zero]

private theorem lorentzSlope_scalar (jet : NativeFirstJet) (force : Field289) (supported : lorentzSupported force)
    (mu : Fin 4) (a : ℝ) (nu : Fin 4) :
    fieldScalar (jet.2 nu+a • (Pi.single mu force : Fin 4→Field289) nu)=fieldScalar (jet.2 nu) := by
  by_cases same : nu=mu
  · simp only [Pi.single_apply,if_pos same,fieldScalar_add,fieldScalar_smul,lorentzSupported_scalar force supported,smul_zero,add_zero]
  · simp only [Pi.single_apply,if_neg same,smul_zero,add_zero]

private theorem lorentzSlope_primal (jet : NativeFirstJet) (force : Field289) (supported : lorentzSupported force)
    (mu : Fin 4) (a : ℝ) (nu spin : Fin 4) (color : Fin 3) :
    fieldPrimalComplex (jet.2 nu+a • (Pi.single mu force : Fin 4→Field289) nu) spin color=
      fieldPrimalComplex (jet.2 nu) spin color := by
  change primalCoefficientCLM spin color (jet.2 nu+a • (Pi.single mu force : Fin 4→Field289) nu)=
    primalCoefficientCLM spin color (jet.2 nu)
  by_cases same : nu=mu
  · simp only [Pi.single_apply,if_pos same,map_add,map_smul,lorentzSupported_primal force supported,smul_zero,add_zero]
  · simp only [Pi.single_apply,if_neg same,smul_zero,add_zero]

private theorem loweredInsertion (force : Field289) (nu : Fin 4) (internal : Fin 6) :
    minkowskiInternalSign (pairFirst internal)*lorentzInsertionCLM force nu (pairFirst internal) (pairSecond internal)=
      fieldLorentz force nu internal := by
  have source:=loweredLorentzConnectionCoefficient_ofBivectorOneForm (fieldLorentz force) nu internal
  exact source

theorem nativeLorentzSlopeShift_curvature (jet : NativeFirstJet) (force : Field289) (mu : Fin 4) (a : ℝ) :
    SourcePropagationNativeActionHessian.nativeGravityCurvature (nativeConnectionSlopeShift jet force mu a)=
      SourcePropagationNativeActionHessian.nativeGravityCurvature jet+
        a • loweredLorentzExteriorDerivativeDirection mu (fieldLorentz force) := by
  funext internal pair
  unfold SourcePropagationNativeActionHessian.nativeGravityCurvature nativeConnectionSlopeShift
  simp only [Pi.add_apply,Pi.smul_apply,map_add,map_smul,loweredLorentzExteriorDerivativeDirection]
  have first : minkowskiInternalSign (pairFirst internal)*lorentzInsertionCLM
      ((Pi.single mu force : Fin 4→Field289) (pairFirst pair)) (pairSecond pair) (pairFirst internal) (pairSecond internal)=
      if mu=pairFirst pair then fieldLorentz force (pairSecond pair) internal else 0 := by
    by_cases same : mu=pairFirst pair
    · simp only [Pi.single_apply,if_pos same.symm,loweredInsertion,if_pos same]
    · simp only [Pi.single_apply,if_neg (Ne.symm same),map_zero,Pi.zero_apply,mul_zero,if_neg same]
  have second : minkowskiInternalSign (pairFirst internal)*lorentzInsertionCLM
      ((Pi.single mu force : Fin 4→Field289) (pairSecond pair)) (pairFirst pair) (pairFirst internal) (pairSecond internal)=
      if mu=pairSecond pair then fieldLorentz force (pairFirst pair) internal else 0 := by
    by_cases same : mu=pairSecond pair
    · simp only [Pi.single_apply,if_pos same.symm,loweredInsertion,if_pos same]
    · simp only [Pi.single_apply,if_neg (Ne.symm same),map_zero,Pi.zero_apply,mul_zero,if_neg same]
  linear_combination a*first-a*second

theorem nativeLorentzSlopeShift_point (jet : NativeFirstJet) (force : Field289) (supported : lorentzSupported force)
    (mu : Fin 4) (a : ℝ) :
    nativeJetPoint (nativeConnectionSlopeShift jet force mu a)=withLorentzConnectionJets (nativeJetPoint jet)
      ((nativeJetPoint jet).gravityCurvature+a • loweredLorentzExteriorDerivativeDirection mu (fieldLorentz force))
      (nativeJetPoint jet).matterCovariantDerivative := by
  apply StageNineContinuumPointField.ext
  · rfl
  · exact nativeLorentzSlopeShift_curvature jet force mu a
  · rfl
  · rfl
  · funext pair
    simp only [nativeJetPoint,withLorentzConnectionJets,nativeGaugeCurvature,nativeConnectionSlopeShift,Pi.add_apply,Pi.smul_apply,
      lorentzSlope_gauge jet force supported]
  · rfl
  · rfl
  · funext nu
    simp only [nativeJetPoint,withLorentzConnectionJets,nativeScalarCovariant,nativeConnectionSlopeShift,Pi.add_apply,Pi.smul_apply,
      lorentzSlope_scalar jet force supported]
  · rfl
  · funext nu
    simp only [nativeJetPoint,withLorentzConnectionJets,nativeMatterCovariant,nativeMatterValue,rotatedPrimalDerivative,
      nativeConnectionSlopeShift,Pi.add_apply,Pi.smul_apply,lorentzSlope_primal jet force supported]
  · rfl

theorem nativeLocalLorentzSlopeShift_point (point : BasePoint) (jet : NativeFirstJet) (force : Field289)
    (supported : lorentzSupported force) (mu : Fin 4) (a : ℝ) :
    nativeLocalPoint point (nativeConnectionSlopeShift jet force mu a)=withLorentzConnectionJets (nativeLocalPoint point jet)
      ((nativeLocalPoint point jet).gravityCurvature+a • loweredLorentzExteriorDerivativeDirection mu (fieldLorentz force))
      (nativeLocalPoint point jet).matterCovariantDerivative := by
  rw [nativeLocalPoint_common,nativeLorentzSlopeShift_point jet force supported,nativeLocalPoint_common]
  rfl

theorem nativeLorentzSlopeShift_density (point : BasePoint) (jet : NativeFirstJet) (force : Field289)
    (supported : lorentzSupported force) (mu : Fin 4) (a : ℝ) :
    nativeJetDensity (nativeConnectionSlopeShift jet force mu a)=motherDensityAt point
      (withLorentzConnectionJets (nativeLocalPoint point jet)
        ((nativeLocalPoint point jet).gravityCurvature+a • loweredLorentzExteriorDerivativeDirection mu (fieldLorentz force))
        (nativeLocalPoint point jet).matterCovariantDerivative) := by
  rw [←nativeLocalAction_pointfree point (nativeConnectionSlopeShift jet force mu a),nativeLocalAction_original,
    nativeLocalLorentzSlopeShift_point point jet force supported]
  rfl

theorem nativeLorentzMomentumCoefficient_atPoint (point : BasePoint) (jet : NativeFirstJet) (force : Field289)
    (supported : lorentzSupported force) (inside : jet∈nativeEulerSourceDomain) (mu : Fin 4) :
    fderiv ℝ nativeJetDensity jet (0,Pi.single mu force)=
      gravityExteriorPrincipalBilinear mu (nativeLocalPoint point jet).gravityAuxiliary (fieldLorentz force) := by
  have derivative:=connectionSlope_derivative jet force mu inside
  have law : (fun a : ℝ=>nativeJetDensity (nativeConnectionSlopeShift jet force mu a))=
      fun a=>motherDensityAt point (withLorentzConnectionJets (nativeLocalPoint point jet)
        ((nativeLocalPoint point jet).gravityCurvature+a • loweredLorentzExteriorDerivativeDirection mu (fieldLorentz force))
        (nativeLocalPoint point jet).matterCovariantDerivative) := funext (nativeLorentzSlopeShift_density point jet force supported mu)
  rw [law] at derivative
  exact derivative.unique (nativeLorentzCurvatureCurve_generated point (nativeLocalPoint point jet) mu (fieldLorentz force))

theorem nativeLorentzMomentumCoefficient_signal (signal : BasePoint→Field289) (point : BasePoint) (force : Field289)
    (supported : lorentzSupported force) (differentiable : DifferentiableAt ℝ signal point)
    (inside : signalFirstJet signal point∈nativeEulerSourceDomain) (mu : Fin 4) :
    fderiv ℝ nativeJetDensity (signalFirstJet signal point) (0,Pi.single mu force)=
      gravityExteriorPrincipalBilinear mu ((nativeConfiguration signal).gravityAuxiliary point) (fieldLorentz force) := by
  rw [nativeLorentzMomentumCoefficient_atPoint point (signalFirstJet signal point) force supported inside mu,
    ←nativePoint_signalFirstJet signal point differentiable]
  unfold nativePoint toContinuumPointField
  rfl


private def connectionSupported (force : Field289) : Prop := ∀ field : Fin 289,
  ¬((9≤field.val ∧ field.val<57) ∨ (121≤field.val ∧ field.val<145))→force field=0

private theorem connectionScalarZero (force : Field289) (supported : connectionSupported force) : fieldScalar force=0 := by
  unfold fieldScalar
  have each (a : Fin 9) : force (scalarSlot a)=0 := supported _ (by simp only [scalarSlot];omega)
  simp only [each,zero_smul,Finset.sum_const_zero]

private theorem connectionPrimalZero (force : Field289) (supported : connectionSupported force) (spin : Fin 4) (color : Fin 3) :
    fieldPrimalComplex force spin color=0 := by
  have each (part : Fin 2) : fieldPrimal force part spin color=0 := supported _ (by simp only [primalSlot];omega)
  simp only [fieldPrimalComplex,each,Complex.ofReal_zero,mul_zero,add_zero]

private theorem connectionDualZero (force : Field289) (supported : connectionSupported force) (spin : Fin 4) (color : Fin 3) :
    fieldDualComplex force spin color=0 := by
  have each (part : Fin 2) : fieldDual force part spin color=0 := supported _ (by simp only [dualSlot];omega)
  simp only [fieldDualComplex,each,Complex.ofReal_zero,mul_zero,add_zero]

private theorem connectionConfigurationShift (signal variation : BasePoint→Field289)
    (supported : ∀ x,connectionSupported (variation x)) (r : ℝ) :
    nativeConfiguration (fun x=>signal x+r • variation x)=
      {nativeConfiguration signal with
        gravityConnection:=fun x=>(nativeConfiguration signal).gravityConnection x+r • lorentzInsertionCLM (variation x),
        gaugeConnection:=fun x mu=>(nativeConfiguration signal).gaugeConnection x mu+
          r • p286CoordinateEquiv.symm (fieldGauge (variation x) mu)} := by
  apply StageNineHolonomicConfiguration.ext
  · funext x a mu
    unfold nativeConfiguration
    change actual.coframe x a mu+(signal x+r • variation x) (coframeSlot a mu)=
      actual.coframe x a mu+signal x (coframeSlot a mu)
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [supported x _ (by simp only [coframeSlot];omega),mul_zero,add_zero]
  · funext x
    unfold nativeConfiguration
    dsimp only
    change actual.gravityConnection x+lorentzInsertionCLM (signal x+r • variation x)=
      actual.gravityConnection x+lorentzInsertionCLM (signal x)+r • lorentzInsertionCLM (variation x)
    rw [map_add,map_smul,add_assoc]
  · funext x a mu
    unfold nativeConfiguration
    change actual.gravityAuxiliary x a mu+(signal x+r • variation x) (gravitySlot a mu)=
      actual.gravityAuxiliary x a mu+signal x (gravitySlot a mu)
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [supported x _ (by simp only [gravitySlot];omega),mul_zero,add_zero]
  · funext x a mu
    unfold nativeConfiguration
    change actual.gravitySimplicityMultiplier x a mu+(signal x+r • variation x) (multiplierSlot a mu)=
      actual.gravitySimplicityMultiplier x a mu+signal x (multiplierSlot a mu)
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [supported x _ (by simp only [multiplierSlot];omega),mul_zero,add_zero]
  · funext x mu
    unfold nativeConfiguration
    dsimp only
    rw [fieldGauge_add,fieldGauge_smul,map_add,map_smul,add_assoc]
  · funext x pair
    unfold nativeConfiguration
    dsimp only
    have same : gaugeBInsertion (signal x+r • variation x) pair=gaugeBInsertion (signal x) pair := by
      unfold gaugeBInsertion fieldGaugeB
      apply congrArg p286CoordinateEquiv.symm
      apply Finset.sum_congr rfl
      intro a _
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      rw [supported x _ (by simp only [gaugeBSlot];omega),mul_zero,add_zero]
    rw [same]
  · funext x
    unfold nativeConfiguration
    dsimp only
    rw [fieldScalar_add,fieldScalar_smul,connectionScalarZero _ (supported x),smul_zero,add_zero]
  · funext x
    unfold nativeConfiguration
    dsimp only
    have same : primalInsertion (signal x+r • variation x)=primalInsertion (signal x) := by
      apply matterCoordinateEquiv.injective
      change primalInsertionCLM (signal x+r • variation x)=primalInsertionCLM (signal x)
      have zero : primalInsertionCLM (variation x)=0 := by
        change matterCoordinateEquiv (primalInsertion (variation x))=0
        have empty : primalInsertion (variation x)=0 := by
          simp only [primalInsertion,connectionPrimalZero _ (supported x),zero_smul,Finset.sum_const_zero]
        rw [empty,map_zero]
      rw [map_add,map_smul,zero,smul_zero,add_zero]
    rw [same]
  · funext x
    unfold nativeConfiguration
    dsimp only
    have same : dualInsertion (signal x+r • variation x)=dualInsertion (signal x) := by
      apply LinearMap.ext
      intro v
      have each (spin : Fin 4) (color : Fin 3) :
          fieldDualComplex (signal x+r • variation x) spin color=fieldDualComplex (signal x) spin color := by
        change dualCoefficientCLM spin color (signal x+r • variation x)=dualCoefficientCLM spin color (signal x)
        rw [map_add,map_smul,show dualCoefficientCLM spin color (variation x)=0 from connectionDualZero _ (supported x) spin color,
          smul_zero,add_zero]
      simp only [dualInsertion,each]
    rw [same]

private def connectionBump (point : BasePoint) : ContDiffBump point := ⟨1,2,by norm_num,by norm_num⟩
private def connectionFieldVariation (point : BasePoint) (force : Field289) (x : BasePoint) : Field289 :=
  connectionBump point x • force

private theorem connectionFieldVariation_smooth (point : BasePoint) (force : Field289) :
    ContDiff ℝ ∞ (connectionFieldVariation point force) := (connectionBump point).contDiff.smul contDiff_const

private theorem connectionFieldVariation_value (point : BasePoint) (force : Field289) :
    connectionFieldVariation point force point=force := by
  have center : connectionBump point point=1 := (connectionBump point).one_of_mem_closedBall
    (Metric.mem_closedBall_self (connectionBump point).rIn_pos.le)
  simp only [connectionFieldVariation,center,one_smul]

private def connectionLorentzVariation (point : BasePoint) (force : Field289) :
    CompactlySupportedSmoothVariation LorentzBivectorOneForm where
  toFun x:=connectionBump point x • fieldLorentz force
  smooth:=(connectionBump point).contDiff.smul contDiff_const
  compactSupport:=(connectionBump point).hasCompactSupport.smul_right

private theorem connectionLorentzCurve (signal : BasePoint→Field289) (point : BasePoint) (force : Field289)
    (supported : lorentzSupported force) (r : ℝ) :
    nativeConfiguration (fun x=>signal x+r • connectionFieldVariation point force x)=
      varyLorentzConnection (nativeConfiguration signal) (connectionLorentzVariation point force) r := by
  have support : ∀ x,connectionSupported (connectionFieldVariation point force x) := by
    intro x entry outside
    simp only [connectionFieldVariation,Pi.smul_apply,smul_eq_mul]
    rw [supported _ (by intro h;exact outside (Or.inr h)),mul_zero]
  rw [connectionConfigurationShift signal _ support]
  apply StageNineHolonomicConfiguration.ext
  all_goals try rfl
  funext x mu
  change (nativeConfiguration signal).gaugeConnection x mu+
      r • p286CoordinateEquiv.symm (fieldGauge (connectionBump point x • force) mu)=
    (nativeConfiguration signal).gaugeConnection x mu
  rw [fieldGauge_smul,lorentzSupported_gauge force supported,smul_zero,map_zero,smul_zero,add_zero]

private theorem connectionFlux_direction (signal variation : BasePoint→Field289) (point : BasePoint) (mu : Fin 4) :
    nativeVariationFlux signal variation mu point=
      fderiv ℝ nativeJetDensity (signalFirstJet signal point) (0,Pi.single mu (variation point)) := by
  have reconstruction : (0,Pi.single mu (variation point))=
      ∑ field : Fin 289,variation point field • nativeJetBasis (some mu,field) := by
    apply Prod.ext
    · simp [nativeJetBasis,Prod.fst_sum]
    · funext nu field
      by_cases same : nu=mu
      · subst nu
        simp [nativeJetBasis,Prod.snd_sum,Finset.sum_apply,Pi.single_apply,mul_ite]
      · simp [nativeJetBasis,Prod.snd_sum,Finset.sum_apply,same]
  rw [reconstruction]
  simp only [map_sum,map_smul,smul_eq_mul,nativeVariationFlux,nativeSignalMomentum]
  apply Finset.sum_congr rfl
  intro field _
  exact mul_comm _ _

private theorem connectionSignal_near (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (inside : signalFirstJet signal point∈nativeEulerSourceDomain) :
    ∀ᶠ position in 𝓝 point,DifferentiableAt ℝ signal position ∧ signalFirstJet signal position∈nativeEulerSourceDomain := by
  have signalNear:=smooth.eventually (by simp)
  have regular : ContDiffAt ℝ 2 nativeJetDensity (signalFirstJet signal point) := inside
  have domainNear : nativeEulerSourceDomain∈𝓝 (signalFirstJet signal point) := regular.eventually (by simp)
  have sourceNear:=((signalFirstJet_source_smooth signal point smooth).continuousAt).eventually_mem domainNear
  filter_upwards [signalNear,sourceNear] with position hs hi
  exact ⟨hs.differentiableAt (by norm_num),hi⟩

/-- Both sides are generated by the identical original primitive connection path. -/
theorem nativeLorentzEuler_identification (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (configurationSmooth : (nativeConfiguration signal).Smooth)
    (admissible : GravityConnectionLorentzAdmissible (nativeConfiguration signal))
    (inside : signalFirstJet signal point∈nativeEulerSourceDomain)
    (field : Fin 289) (range : 121≤field.val ∧ field.val<145) :
    nativeHolonomicEuler signal point field=
      lorentzOneFormThreeFormWedgeCoefficient (fieldLorentz (Pi.single field 1))
        (nativeEuler signal point).lorentzConnection := by
  let force : Field289:=Pi.single field 1
  have supported : lorentzSupported force := by
    intro entry outside
    have different : entry≠field := by intro same;subst entry;exact outside range
    simp [force,different]
  let variation:=connectionFieldVariation point force
  let lorentz:=connectionLorentzVariation point force
  have derivative:=nativeDensity_variation_euler signal variation point smooth
    ((connectionFieldVariation_smooth point force).differentiable (by simp) |>.differentiableAt) inside
  have curve : (fun r : ℝ=>nativeDensity (fun x=>signal x+r • variation x) point)=
      fun r=>sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 point
        (toContinuumPointField (varyLorentzConnection (nativeConfiguration signal) lorentz r) point) := by
    funext r
    unfold nativeDensity nativePoint
    rw [connectionLorentzCurve signal point force supported r]
  have mother:=nativeMotherLorentz_direction signal configurationSmooth admissible lorentz point
  rw [curve,mother.deriv] at derivative
  have flux (mu : Fin 4) : nativeVariationFlux signal variation mu =ᶠ[𝓝 point]
      motherLorentzBoundaryCurrent (nativeConfiguration signal) lorentz mu := by
    filter_upwards [connectionSignal_near signal point smooth inside] with position regular
    rw [connectionFlux_direction]
    have support : lorentzSupported (variation position) := by
      intro entry outside
      change connectionBump point position*force entry=0
      rw [supported entry outside,mul_zero]
    rw [nativeLorentzMomentumCoefficient_signal signal position (variation position) support regular.1 regular.2 mu]
    change gravityExteriorPrincipalBilinear mu ((nativeConfiguration signal).gravityAuxiliary position)
        (fieldLorentz (connectionBump point position • force))=
      gravityExteriorPrincipalContinuousBilinear mu ((nativeConfiguration signal).gravityAuxiliary position)
        (connectionBump point position • fieldLorentz force)
    rw [gravityExteriorPrincipalContinuousBilinear_apply]
    rfl
  have divergence : (∑ mu : Fin 4,fieldDirectionalDerivative (nativeVariationFlux signal variation mu) point mu)=
      motherLorentzBoundaryDivergence (nativeConfiguration signal) lorentz point := by
    unfold motherLorentzBoundaryDivergence
    apply Finset.sum_congr rfl
    intro mu _
    unfold fieldDirectionalDerivative
    rw [(flux mu).fderiv_eq]
  rw [show variation point=force from connectionFieldVariation_value point force,divergence] at derivative
  have value : lorentz point=fieldLorentz force := by
    change connectionBump point point • fieldLorentz force=fieldLorentz force
    have center : connectionBump point point=1 := (connectionBump point).one_of_mem_closedBall
      (Metric.mem_closedBall_self (connectionBump point).rIn_pos.le)
    rw [center,one_smul]
  rw [value] at derivative
  simp only [force,Pi.single_apply,ite_mul,one_mul,zero_mul,Fintype.sum_ite_eq'] at derivative
  linarith


def gaugeSupported (force : Field289) : Prop := ∀ field : Fin 289,
  ¬(9≤field.val ∧ field.val<57)→force field=0

private theorem gaugeSupported_scalar (force : Field289) (supported : gaugeSupported force) : fieldScalar force=0 := by
  unfold fieldScalar
  have each (a : Fin 9) : force (scalarSlot a)=0 := supported _ (by simp only [scalarSlot];omega)
  simp only [each,zero_smul,Finset.sum_const_zero]

private theorem gaugeSupported_lorentz (force : Field289) (supported : gaugeSupported force) : fieldLorentz force=0 := by
  funext nu a
  exact supported _ (by simp only [lorentzSlot];omega)

private theorem gaugeSupported_primal (force : Field289) (supported : gaugeSupported force) (spin : Fin 4) (color : Fin 3) :
    primalCoefficientCLM spin color force=0 := by
  have each (part : Fin 2) : fieldPrimal force part spin color=0 := supported _ (by simp only [primalSlot];omega)
  change fieldPrimalComplex force spin color=0
  simp only [fieldPrimalComplex,each,Complex.ofReal_zero,mul_zero,add_zero]

private theorem gaugeSlope_scalar (jet : NativeFirstJet) (force : Field289) (supported : gaugeSupported force)
    (mu : Fin 4) (a : ℝ) (nu : Fin 4) :
    fieldScalar (jet.2 nu+a • (Pi.single mu force : Fin 4→Field289) nu)=fieldScalar (jet.2 nu) := by
  by_cases same : nu=mu
  · simp only [Pi.single_apply,if_pos same,fieldScalar_add,fieldScalar_smul,gaugeSupported_scalar force supported,smul_zero,add_zero]
  · simp only [Pi.single_apply,if_neg same,smul_zero,add_zero]

private theorem gaugeSlope_primal (jet : NativeFirstJet) (force : Field289) (supported : gaugeSupported force)
    (mu : Fin 4) (a : ℝ) (nu spin : Fin 4) (color : Fin 3) :
    fieldPrimalComplex (jet.2 nu+a • (Pi.single mu force : Fin 4→Field289) nu) spin color=fieldPrimalComplex (jet.2 nu) spin color := by
  change primalCoefficientCLM spin color (jet.2 nu+a • (Pi.single mu force : Fin 4→Field289) nu)=
    primalCoefficientCLM spin color (jet.2 nu)
  by_cases same : nu=mu
  · simp only [Pi.single_apply,if_pos same,map_add,map_smul,gaugeSupported_primal force supported,smul_zero,add_zero]
  · simp only [Pi.single_apply,if_neg same,smul_zero,add_zero]

theorem nativeGaugeSlopeShift_curvature (jet : NativeFirstJet) (force : Field289) (mu : Fin 4) (a : ℝ) :
    nativeGaugeCurvature (nativeConnectionSlopeShift jet force mu a)=
      fun pair=>nativeGaugeCurvature jet pair+a • p286CoordinateEquiv.symm
        (p286GaugeExteriorDerivativeDirection mu (fieldGauge force) pair) := by
  funext pair
  unfold nativeGaugeCurvature nativeConnectionSlopeShift p286GaugeExteriorDerivativeDirection
  simp only [Pi.add_apply,Pi.smul_apply,fieldGauge_add,fieldGauge_smul]
  have projected (nu rho : Fin 4) : fieldGauge ((Pi.single mu force : Fin 4→Field289) nu) rho=
      if mu=nu then fieldGauge force rho else 0 := by
    by_cases same : mu=nu
    · simp only [Pi.single_apply,if_pos same.symm,if_pos same]
    · simp only [Pi.single_apply,if_neg (Ne.symm same),if_neg same]
      simp only [fieldGauge,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
  rw [add_sub_add_comm,←smul_sub,projected,projected,map_add,map_smul]
  abel

theorem nativeGaugeSlopeShift_point (jet : NativeFirstJet) (force : Field289) (supported : gaugeSupported force)
    (mu : Fin 4) (a : ℝ) :
    nativeJetPoint (nativeConnectionSlopeShift jet force mu a)=withP286GaugeConnectionJets (nativeJetPoint jet)
      (p286CurvatureCoordinate (nativeJetPoint jet)+a • p286GaugeExteriorDerivativeDirection mu (fieldGauge force))
      (nativeJetPoint jet).scalarCovariantDerivative (nativeJetPoint jet).matterCovariantDerivative := by
  apply StageNineContinuumPointField.ext
  · rfl
  · have law:=nativeLorentzSlopeShift_curvature jet force mu a
    rw [gaugeSupported_lorentz force supported] at law
    have zero : loweredLorentzExteriorDerivativeDirection mu 0=0 := by
      funext internal pair
      simp only [loweredLorentzExteriorDerivativeDirection,Pi.zero_apply,ite_self,sub_self]
    rw [zero,smul_zero,add_zero] at law
    exact law
  · rfl
  · rfl
  · funext pair
    simp only [nativeJetPoint,withP286GaugeConnectionJets,Pi.add_apply,Pi.smul_apply,
      nativeGaugeSlopeShift_curvature,p286CurvatureCoordinate,map_add,map_smul,LinearEquiv.symm_apply_apply]
  · rfl
  · rfl
  · funext nu
    simp only [nativeJetPoint,withP286GaugeConnectionJets,nativeScalarCovariant,nativeConnectionSlopeShift,Pi.add_apply,Pi.smul_apply,
      gaugeSlope_scalar jet force supported]
  · rfl
  · funext nu
    simp only [nativeJetPoint,withP286GaugeConnectionJets,nativeMatterCovariant,nativeMatterValue,rotatedPrimalDerivative,
      nativeConnectionSlopeShift,Pi.add_apply,Pi.smul_apply,gaugeSlope_primal jet force supported]
  · rfl

theorem nativeLocalGaugeSlopeShift_point (point : BasePoint) (jet : NativeFirstJet) (force : Field289)
    (supported : gaugeSupported force) (mu : Fin 4) (a : ℝ) :
    nativeLocalPoint point (nativeConnectionSlopeShift jet force mu a)=withP286GaugeConnectionJets (nativeLocalPoint point jet)
      (p286CurvatureCoordinate (nativeLocalPoint point jet)+a • p286GaugeExteriorDerivativeDirection mu (fieldGauge force))
      (nativeLocalPoint point jet).scalarCovariantDerivative (nativeLocalPoint point jet).matterCovariantDerivative := by
  rw [nativeLocalPoint_common,nativeGaugeSlopeShift_point jet force supported,nativeLocalPoint_common]
  rfl

theorem nativeP286CurvatureCurve_generated (point : BasePoint) (field : StageNineContinuumPointField)
    (mu : Fin 4) (direction : P286GaugeOneForm) :
    HasDerivAt (fun a : ℝ=>motherDensityAt point (withP286GaugeConnectionJets field
      (p286CurvatureCoordinate field+a • p286GaugeExteriorDerivativeDirection mu direction)
      field.scalarCovariantDerivative field.matterCovariantDerivative))
      (p286GaugeExteriorPrincipalBilinear mu (p286AuxiliaryCoordinate field) direction) 0 := by
  have law : (fun a : ℝ=>motherDensityAt point (withP286GaugeConnectionJets field
      (p286CurvatureCoordinate field+a • p286GaugeExteriorDerivativeDirection mu direction)
      field.scalarCovariantDerivative field.matterCovariantDerivative))=
      fun a=>motherDensityAt point field+a*formNativeP286GaugeConnectionBFFirstVariationDensity field
        (p286GaugeExteriorDerivativeDirection mu direction) := by
    funext a
    have gauge:=generatedFormNativeGaugeDensityAtBoundary_connectionJets_quadratic
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) field
      (p286GaugeExteriorDerivativeDirection mu direction) 0 field.scalarCovariantDerivative field.matterCovariantDerivative a
    simp only [smul_zero,add_zero,formNativeP286GaugeConnectionBFFirstVariationDensity,
      formNativeP286GaugeCurvatureCoordinateToActual_zero,formNativeP286GaugeWedgeCoefficient_zero_right,mul_zero] at gauge
    change generatedFormNativeGravityBFDensity field+generatedFormNativeGravityConstraintDensity field+
        generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (withP286GaugeConnectionJets field
            (p286CurvatureCoordinate field+a • p286GaugeExteriorDerivativeDirection mu direction)
            field.scalarCovariantDerivative field.matterCovariantDerivative)+
        generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 point field = _
    rw [gauge]
    change generatedFormNativeGravityBFDensity field+generatedFormNativeGravityConstraintDensity field+
        (generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) field+
          a*formNativeP286GaugeConnectionBFFirstVariationDensity field (p286GaugeExteriorDerivativeDirection mu direction))+
        generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 point field =
      generatedFormNativeGravityBFDensity field+generatedFormNativeGravityConstraintDensity field+
        generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) field+
        generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 point field+
        a*formNativeP286GaugeConnectionBFFirstVariationDensity field (p286GaugeExteriorDerivativeDirection mu direction)
    abel
  rw [law]
  convert! ((hasDerivAt_id (0 : ℝ)).mul_const (formNativeP286GaugeConnectionBFFirstVariationDensity field
    (p286GaugeExteriorDerivativeDirection mu direction))).const_add (motherDensityAt point field) using 1
  simp only [one_mul,formNativeP286GaugeConnectionBFFirstVariationDensity_eq_coordinate,p286GaugeExteriorPrincipalBilinear_apply]

theorem nativeGaugeMomentumCoefficient_atPoint (point : BasePoint) (jet : NativeFirstJet) (force : Field289)
    (supported : gaugeSupported force) (inside : jet∈nativeEulerSourceDomain) (mu : Fin 4) :
    fderiv ℝ nativeJetDensity jet (0,Pi.single mu force)=
      p286GaugeExteriorPrincipalBilinear mu (p286AuxiliaryCoordinate (nativeLocalPoint point jet)) (fieldGauge force) := by
  have derivative:=connectionSlope_derivative jet force mu inside
  have law : (fun a : ℝ=>nativeJetDensity (nativeConnectionSlopeShift jet force mu a))=
      fun a=>motherDensityAt point (withP286GaugeConnectionJets (nativeLocalPoint point jet)
        (p286CurvatureCoordinate (nativeLocalPoint point jet)+a • p286GaugeExteriorDerivativeDirection mu (fieldGauge force))
        (nativeLocalPoint point jet).scalarCovariantDerivative (nativeLocalPoint point jet).matterCovariantDerivative) := by
    funext a
    rw [←nativeLocalAction_pointfree point (nativeConnectionSlopeShift jet force mu a),nativeLocalAction_original,
      nativeLocalGaugeSlopeShift_point point jet force supported]
    rfl
  rw [law] at derivative
  exact derivative.unique (nativeP286CurvatureCurve_generated point (nativeLocalPoint point jet) mu (fieldGauge force))

theorem nativeGaugeMomentumCoefficient_signal (signal : BasePoint→Field289) (point : BasePoint) (force : Field289)
    (supported : gaugeSupported force) (differentiable : DifferentiableAt ℝ signal point)
    (inside : signalFirstJet signal point∈nativeEulerSourceDomain) (mu : Fin 4) :
    fderiv ℝ nativeJetDensity (signalFirstJet signal point) (0,Pi.single mu force)=
      p286GaugeExteriorPrincipalBilinear mu (holonomicP286GaugeAuxiliaryCoordinate (nativeConfiguration signal) point) (fieldGauge force) := by
  rw [nativeGaugeMomentumCoefficient_atPoint point (signalFirstJet signal point) force supported inside mu,
    ←nativePoint_signalFirstJet signal point differentiable]
  unfold nativePoint toContinuumPointField p286AuxiliaryCoordinate holonomicP286GaugeAuxiliaryCoordinate
  rfl

private def connectionGaugeVariation (point : BasePoint) (force : Field289) :
    CompactlySupportedSmoothVariation P286GaugeOneForm where
  toFun x:=connectionBump point x • fieldGauge force
  smooth:=(connectionBump point).contDiff.smul contDiff_const
  compactSupport:=(connectionBump point).hasCompactSupport.smul_right

private theorem connectionGaugeCurve (signal : BasePoint→Field289) (point : BasePoint) (force : Field289)
    (supported : gaugeSupported force) (r : ℝ) :
    nativeConfiguration (fun x=>signal x+r • connectionFieldVariation point force x)=
      varyP286GaugeConnectionCoordinate (nativeConfiguration signal) (connectionGaugeVariation point force) r := by
  have support : ∀ x,connectionSupported (connectionFieldVariation point force x) := by
    intro x entry outside
    simp only [connectionFieldVariation,Pi.smul_apply,smul_eq_mul]
    rw [supported _ (by intro h;exact outside (Or.inl h)),mul_zero]
  rw [connectionConfigurationShift signal _ support]
  apply StageNineHolonomicConfiguration.ext
  all_goals try rfl
  · funext x
    change (nativeConfiguration signal).gravityConnection x+r • lorentzInsertionCLM
        (connectionBump point x • force)=(nativeConfiguration signal).gravityConnection x
    have zero : lorentzInsertionCLM force=0 := by
      change lorentzSkewConnectionOfBivectorOneForm (fieldLorentz force)=0
      rw [gaugeSupported_lorentz force supported]
      exact map_zero lorentzInsertionCLM
    rw [map_smul,zero,smul_zero,smul_zero,add_zero]
  · funext x mu
    change (nativeConfiguration signal).gaugeConnection x mu+
        r • p286CoordinateEquiv.symm (fieldGauge (connectionBump point x • force) mu)=
      p286CoordinateEquiv.symm (holonomicP286GaugeConnectionCoordinate (nativeConfiguration signal) x mu+
        r • (connectionGaugeVariation point force).toFun x mu)
    rw [map_add,map_smul]
    simp only [holonomicP286GaugeConnectionCoordinate,LinearEquiv.symm_apply_apply]
    have scaling : fieldGauge (connectionBump point x • force) mu=(connectionGaugeVariation point force).toFun x mu :=
      fieldGauge_smul _ _ mu
    rw [scaling]

theorem nativeGaugeEuler_identification (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (configurationSmooth : (nativeConfiguration signal).Smooth)
    (inside : signalFirstJet signal point∈nativeEulerSourceDomain)
    (field : Fin 289) (range : 9≤field.val ∧ field.val<57) :
    nativeHolonomicEuler signal point field=
      p286GaugeOneFormThreeFormWedgeCoefficient (fieldGauge (Pi.single field 1))
        (nativeEuler signal point).p286GaugeConnection := by
  let force : Field289:=Pi.single field 1
  have supported : gaugeSupported force := by
    intro entry outside
    have different : entry≠field := by intro same;subst entry;exact outside range
    simp [force,different]
  let variation:=connectionFieldVariation point force
  let gauge:=connectionGaugeVariation point force
  have derivative:=nativeDensity_variation_euler signal variation point smooth
    ((connectionFieldVariation_smooth point force).differentiable (by simp) |>.differentiableAt) inside
  have curve : (fun r : ℝ=>nativeDensity (fun x=>signal x+r • variation x) point)=
      fun r=>sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 point
        (toContinuumPointField (varyP286GaugeConnectionCoordinate (nativeConfiguration signal) gauge r) point) := by
    funext r
    unfold nativeDensity nativePoint
    rw [connectionGaugeCurve signal point force supported r]
  have mother:=nativeMotherP286_direction signal configurationSmooth gauge point
  rw [curve,mother.deriv] at derivative
  have flux (mu : Fin 4) : nativeVariationFlux signal variation mu =ᶠ[𝓝 point]
      motherP286BoundaryCurrent (nativeConfiguration signal) gauge mu := by
    filter_upwards [connectionSignal_near signal point smooth inside] with position regular
    rw [connectionFlux_direction]
    have support : gaugeSupported (variation position) := by
      intro entry outside
      change connectionBump point position*force entry=0
      rw [supported entry outside,mul_zero]
    rw [nativeGaugeMomentumCoefficient_signal signal position (variation position) support regular.1 regular.2 mu]
    change p286GaugeExteriorPrincipalBilinear mu (holonomicP286GaugeAuxiliaryCoordinate (nativeConfiguration signal) position)
        (fieldGauge (connectionBump point position • force))=
      p286GaugeExteriorPrincipalContinuousBilinear mu (holonomicP286GaugeAuxiliaryCoordinate (nativeConfiguration signal) position)
        (connectionBump point position • fieldGauge force)
    have scaling : fieldGauge (connectionBump point position • force)=connectionBump point position • fieldGauge force := by
      funext nu
      exact fieldGauge_smul _ _ nu
    rw [scaling,p286GaugeExteriorPrincipalContinuousBilinear_apply,p286GaugeExteriorPrincipalBilinear_apply]
  have divergence : (∑ mu : Fin 4,fieldDirectionalDerivative (nativeVariationFlux signal variation mu) point mu)=
      motherP286BoundaryDivergence (nativeConfiguration signal) gauge point := by
    unfold motherP286BoundaryDivergence
    apply Finset.sum_congr rfl
    intro mu _
    unfold fieldDirectionalDerivative
    rw [(flux mu).fderiv_eq]
  rw [show variation point=force from connectionFieldVariation_value point force,divergence] at derivative
  have value : gauge point=fieldGauge force := by
    change connectionBump point point • fieldGauge force=fieldGauge force
    have center : connectionBump point point=1 := (connectionBump point).one_of_mem_closedBall
      (Metric.mem_closedBall_self (connectionBump point).rIn_pos.le)
    rw [center,one_smul]
  rw [value] at derivative
  simp only [force,Pi.single_apply,ite_mul,one_mul,zero_mul,Fintype.sum_ite_eq'] at derivative
  linarith


theorem nativeConfiguration_lorentzAdmissible (signal : BasePoint→Field289) :
    GravityConnectionLorentzAdmissible (nativeConfiguration signal) := by
  intro point
  unfold nativeConfiguration
  change LorentzSkew (actual.gravityConnection point+lorentzSkewConnectionOfBivectorOneForm (fieldLorentz (signal point)))
  exact StageNineCartanAffineConnectionActualization.lorentzSkew_add
    (actual_lorentzAdmissible point) (lorentzSkewConnectionOfBivectorOneForm_lorentzSkew _)


/-- Ordinary configuration regularity is generated by the original finite insertions and actual phase. -/
theorem nativeConfiguration_source_smooth (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) :
    (nativeConfiguration signal).Smooth := by
  rcases actual_smooth with ⟨coframe,connection,auxiliary,multiplier,gauge,gaugeAuxiliary,scalar,matter,dual⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro row column
    unfold nativeConfiguration
    change ContDiff ℝ ∞ (fun point=>actual.coframe point row column+signal point (coframeSlot row column))
    exact (coframe row column).add ((ContinuousLinearMap.proj _ : Field289→L[ℝ] ℝ).contDiff.comp smooth)
  · intro direction internalOut internalIn
    have insertion : ContDiff ℝ ∞ (fun point=>lorentzInsertionCLM (signal point)) := lorentzInsertionCLM.contDiff.comp smooth
    unfold nativeConfiguration
    change ContDiff ℝ ∞ (fun point=>actual.gravityConnection point direction internalOut internalIn+
      lorentzInsertionCLM (signal point) direction internalOut internalIn)
    exact (connection direction internalOut internalIn).add
      ((contDiff_pi.1 ((contDiff_pi.1 ((contDiff_pi.1 insertion) direction)) internalOut)) internalIn)
  · intro internalPair spacetimePair
    unfold nativeConfiguration
    change ContDiff ℝ ∞ (fun point=>actual.gravityAuxiliary point internalPair spacetimePair+
      signal point (gravitySlot internalPair spacetimePair))
    exact (auxiliary internalPair spacetimePair).add ((ContinuousLinearMap.proj _ : Field289→L[ℝ] ℝ).contDiff.comp smooth)
  · intro internalPair spacetimePair
    unfold nativeConfiguration
    change ContDiff ℝ ∞ (fun point=>actual.gravitySimplicityMultiplier point internalPair spacetimePair+
      signal point (multiplierSlot internalPair spacetimePair))
    exact (multiplier internalPair spacetimePair).add ((ContinuousLinearMap.proj _ : Field289→L[ℝ] ℝ).contDiff.comp smooth)
  · intro direction
    have values : (fun point=>p286CoordinateEquiv ((nativeConfiguration signal).gaugeConnection point direction))=
        fun point=>p286CoordinateEquiv (actual.gaugeConnection point direction)+gaugeCoordinateCLM direction (signal point) := by
      funext point
      unfold nativeConfiguration
      simp only [map_add,LinearEquiv.apply_symm_apply]
      rfl
    rw [values]
    exact (gauge direction).add ((gaugeCoordinateCLM direction).contDiff.comp smooth)
  · intro pair
    have values : (fun point=>p286CoordinateEquiv ((nativeConfiguration signal).gaugeAuxiliary point pair))=
        fun point=>p286CoordinateEquiv (actual.gaugeAuxiliary point pair)+
          (∑ a : Fin 12,signal point (gaugeBSlot pair a) • originalUnit a : P286CoordinateCarrier) := by
      funext point
      unfold nativeConfiguration gaugeBInsertion
      simp only [map_add,LinearEquiv.apply_symm_apply]
      rfl
    rw [values]
    refine (gaugeAuxiliary pair).add ?_
    apply ContDiff.sum
    intro a _
    exact ((ContinuousLinearMap.proj (gaugeBSlot pair a) : Field289→L[ℝ] ℝ).contDiff.comp smooth).smul contDiff_const
  · unfold nativeConfiguration
    change ContDiff ℝ ∞ (fun point=>actual.scalar point+scalarInsertionCLM (signal point))
    exact scalar.add (scalarInsertionCLM.contDiff.comp smooth)
  · have values : (fun point=>matterCoordinateEquiv ((nativeConfiguration signal).matter point))=
        fun point=>diracMatrixMatterCoordinateRealBilinear (ActiveGauge.rotation point)
          (matterCoordinateEquiv (actual.matter 0)+primalInsertionCLM (signal point)) := by
      funext point
      rw [nativeMatter_family_rotated,diracMatrixMatterCoordinateRealBilinear_apply]
      have sum : matterCoordinateEquiv (actual.matter 0)+primalInsertionCLM (signal point)=
          matterCoordinateEquiv (actual.matter 0+primalInsertion (signal point)) := by rw [map_add];rfl
      rw [sum,LinearEquiv.symm_apply_apply]
    rw [values]
    exact (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp rotation_source_smooth).clm_apply
      (contDiff_const.add (primalInsertionCLM.contDiff.comp smooth))
  · intro index
    let v:=matterCoordinateEquiv.symm (EuclideanSpace.single index 1)
    have rotated : ContDiff ℝ ∞ (fun point=>matterCoordinateEquiv (diracMatrixMatterAction (ActiveGauge.rotation point) v)) := by
      have law : (fun point=>matterCoordinateEquiv (diracMatrixMatterAction (ActiveGauge.rotation point) v))=
          fun point=>diracMatrixMatterCoordinateRealBilinear (ActiveGauge.rotation point) (matterCoordinateEquiv v) := by
        funext point
        rw [diracMatrixMatterCoordinateRealBilinear_apply,LinearEquiv.symm_apply_apply]
      rw [law]
      exact (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp rotation_source_smooth).clm_apply contDiff_const
    have values : (fun point=>(nativeConfiguration signal).conjugateMatter point v)=
        fun point=>actual.conjugateMatter point v+∑ spin : Fin 4,∑ color : Fin 3,
          dualCoefficientCLM spin color (signal point)*matterReadCLM spin color
            (matterCoordinateEquiv (diracMatrixMatterAction (ActiveGauge.rotation point) v)) := by
      funext point
      unfold nativeConfiguration dualInsertion
      simp only [LinearMap.add_apply,LinearMap.comp_apply,matterReadCLM,matterReadLinear,
        dualCoefficientCLM,dualCoefficientLinear,LinearMap.coe_toContinuousLinearMap',
        LinearMap.coe_mk,AddHom.coe_mk,LinearEquiv.symm_apply_apply]
    change ContDiff ℝ ∞ (fun point=>(nativeConfiguration signal).conjugateMatter point v)
    rw [values]
    refine (dual index).add ?_
    apply ContDiff.sum
    intro spin _
    apply ContDiff.sum
    intro color _
    exact ((dualCoefficientCLM spin color).contDiff.comp smooth).mul ((matterReadCLM spin color).contDiff.comp rotated)

end LowEnergy.SourcePropagationMotherResidualDirections
