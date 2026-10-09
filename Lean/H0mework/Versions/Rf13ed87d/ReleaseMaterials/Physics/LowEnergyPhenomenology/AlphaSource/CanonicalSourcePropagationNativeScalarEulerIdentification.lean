import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeVariationDirections

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDynamicBreakingVacuum StageNineScalarVariation StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeScalarVariation
open DiracExteriorMatterAction SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeSourceRestriction
open Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
attribute [local irreducible] nativeJetDensity nativeDensity nativePoint nativeConfiguration
  SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual

/-- The original nine real scalar-orbit coordinates, in the existing full field carrier. -/
def nativeScalarDirection (coefficients : Fin 9→ℝ) : Field289 := fun field=>
  if h : field.val<9 then coefficients ⟨field.val,h⟩ else 0

theorem nativeScalarDirection_off (coefficients : Fin 9→ℝ) (field : Fin 289) (off : 9≤field.val) :
    nativeScalarDirection coefficients field=0 := by
  simp only [nativeScalarDirection,dif_neg (not_lt.mpr off)]

private theorem scalarDirection_gauge (coefficients : Fin 9→ℝ) (mu : Fin 4) :
    fieldGauge (nativeScalarDirection coefficients) mu=0 := by
  unfold fieldGauge
  have each (a : Fin 12) : nativeScalarDirection coefficients (gaugeSlot mu a)=0 :=
    nativeScalarDirection_off coefficients _ (by simp only [gaugeSlot];omega)
  simp only [each,zero_smul,Finset.sum_const_zero]

private theorem scalarDirection_coframe (coefficients : Fin 9→ℝ) :
    fieldCoframe (nativeScalarDirection coefficients)=0 := by
  funext a mu
  exact nativeScalarDirection_off coefficients _ (by simp only [coframeSlot];omega)

private theorem scalarDirection_lorentz (coefficients : Fin 9→ℝ) :
    fieldLorentz (nativeScalarDirection coefficients)=0 := by
  funext mu a
  exact nativeScalarDirection_off coefficients _ (by simp only [lorentzSlot];omega)

private theorem scalarDirection_primal (coefficients : Fin 9→ℝ) (spin : Fin 4) (color : Fin 3) :
    fieldPrimalComplex (nativeScalarDirection coefficients) spin color=0 := by
  have each (part : Fin 2) : fieldPrimal (nativeScalarDirection coefficients) part spin color=0 :=
    nativeScalarDirection_off coefficients _ (by simp only [primalSlot];omega)
  simp only [fieldPrimalComplex,each,Complex.ofReal_zero,mul_zero,add_zero]

private theorem scalarDirection_dual (coefficients : Fin 9→ℝ) (spin : Fin 4) (color : Fin 3) :
    fieldDualComplex (nativeScalarDirection coefficients) spin color=0 := by
  have each (part : Fin 2) : fieldDual (nativeScalarDirection coefficients) part spin color=0 :=
    nativeScalarDirection_off coefficients _ (by simp only [dualSlot];omega)
  simp only [fieldDualComplex,each,Complex.ofReal_zero,mul_zero,add_zero]

def nativeScalarValueShift (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (a : ℝ) : NativeFirstJet :=
  (jet.1+a • nativeScalarDirection coefficients,jet.2)

private theorem scalarShift_gauge (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (a : ℝ) (mu : Fin 4) :
    fieldGauge (jet.1+a • nativeScalarDirection coefficients) mu=fieldGauge jet.1 mu := by
  simp only [nativeScalarValueShift,fieldGauge_add,fieldGauge_smul,scalarDirection_gauge,smul_zero,add_zero]

private theorem scalarShift_lorentz (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (a : ℝ) :
    lorentzInsertionCLM (jet.1+a • nativeScalarDirection coefficients)=lorentzInsertionCLM jet.1 := by
  have vanishes : lorentzInsertionCLM (nativeScalarDirection coefficients)=0 := by
    change lorentzSkewConnectionOfBivectorOneForm (fieldLorentz (nativeScalarDirection coefficients))=0
    rw [scalarDirection_lorentz]
    simp [lorentzSkewConnectionOfBivectorOneForm,loweredLorentzBivectorMatrix]
  simp only [nativeScalarValueShift,map_add,map_smul,vanishes,smul_zero,add_zero]

private theorem scalarShift_primal (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (a : ℝ) (spin : Fin 4) (color : Fin 3) :
    fieldPrimalComplex (jet.1+a • nativeScalarDirection coefficients) spin color=fieldPrimalComplex jet.1 spin color := by
  have linear : primalCoefficientCLM spin color (nativeScalarDirection coefficients)=0 := scalarDirection_primal coefficients spin color
  change primalCoefficientCLM spin color (jet.1+a • nativeScalarDirection coefficients)=primalCoefficientCLM spin color jet.1
  rw [map_add,map_smul,linear,smul_zero,add_zero]

private theorem scalarShift_dual (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (a : ℝ) (spin : Fin 4) (color : Fin 3) :
    fieldDualComplex (jet.1+a • nativeScalarDirection coefficients) spin color=fieldDualComplex jet.1 spin color := by
  have linear : dualCoefficientCLM spin color (nativeScalarDirection coefficients)=0 := scalarDirection_dual coefficients spin color
  change dualCoefficientCLM spin color (jet.1+a • nativeScalarDirection coefficients)=dualCoefficientCLM spin color jet.1
  rw [map_add,map_smul,linear,smul_zero,add_zero]

theorem nativeScalarValueShift_point (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (a : ℝ) :
    nativeJetPoint (nativeScalarValueShift jet coefficients a)=
      withScalarJets (nativeJetPoint jet)
        ((nativeJetPoint jet).scalar+a • fieldScalar (nativeScalarDirection coefficients))
        ((nativeJetPoint jet).scalarCovariantDerivative+a • pointwiseScalarVariationAlgebraicDirection
          ((nativeConfiguration (affineSignal jet)).gaugeConnection 0) (fieldScalar (nativeScalarDirection coefficients))) := by
  apply StageNineContinuumPointField.ext
  · funext internal mu
    change SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual.coframe 0 internal mu+
      (jet.1 (coframeSlot internal mu)+a*nativeScalarDirection coefficients (coframeSlot internal mu))=
      SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual.coframe 0 internal mu+jet.1 (coframeSlot internal mu)
    rw [nativeScalarDirection_off coefficients _ (by simp only [coframeSlot];omega)]
    ring
  · change SourcePropagationNativeActionHessian.nativeGravityCurvature (nativeScalarValueShift jet coefficients a)=
      SourcePropagationNativeActionHessian.nativeGravityCurvature jet
    unfold SourcePropagationNativeActionHessian.nativeGravityCurvature
    simp only [nativeScalarValueShift,scalarShift_lorentz]
  · funext pair internal
    simp only [nativeJetPoint,nativeScalarValueShift,withScalarJets,fieldGravityB,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [nativeScalarDirection_off coefficients _ (by simp only [gravitySlot];omega)]
    ring
  · funext pair internal
    simp only [nativeJetPoint,nativeScalarValueShift,withScalarJets,fieldMultiplier,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [nativeScalarDirection_off coefficients _ (by simp only [multiplierSlot];omega)]
    ring
  · funext pair
    simp only [nativeJetPoint,withScalarJets,nativeGaugeCurvature,nativeScalarValueShift,scalarShift_gauge]
  · funext pair
    simp only [nativeJetPoint,withScalarJets,gaugeBInsertion,nativeScalarValueShift,fieldGaugeB,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    congr 2
    apply Finset.sum_congr rfl
    intro internal _
    rw [nativeScalarDirection_off coefficients _ (by simp only [gaugeBSlot];omega)]
    simp
  · simp only [nativeJetPoint,withScalarJets,nativeScalarValueShift,fieldScalar_add,fieldScalar_smul]
    module
  · funext mu
    have gaugeAt : (nativeConfiguration (affineSignal jet)).gaugeConnection 0 mu=
        SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual.gaugeConnection 0 mu+
          p286CoordinateEquiv.symm (fieldGauge jet.1 mu) := by
      unfold SourcePropagationNativeActionHessian.nativeConfiguration
      dsimp only
      rw [affineSignal_zero]
    change nativeScalarCovariant (nativeScalarValueShift jet coefficients a) mu=nativeScalarCovariant jet mu+
      a • scalarMotherLieAction (SU7MotherLieAlgebra.p286LieBlockEmbed
        ((nativeConfiguration (affineSignal jet)).gaugeConnection 0 mu)) (fieldScalar (nativeScalarDirection coefficients))
    rw [gaugeAt]
    unfold nativeScalarCovariant
    simp only [nativeScalarValueShift,scalarShift_gauge,fieldScalar_add,fieldScalar_smul,scalarMotherLieAction_add_right,
      scalarMotherLieAction_real_smul_right]
    module
  · simp only [nativeJetPoint,withScalarJets,nativeMatterValue,nativeScalarValueShift,primalInsertion,scalarShift_primal]
  · funext mu
    simp only [nativeJetPoint,withScalarJets,nativeMatterCovariant,rotatedPrimalDerivative,
      nativeScalarValueShift,nativeMatterValue,primalInsertion,scalarShift_primal,scalarShift_gauge,scalarShift_lorentz]
  · apply LinearMap.ext
    intro value
    change SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual.conjugateMatter 0 value+
      (∑ spin : Fin 4,∑ color : Fin 3,fieldDualComplex (jet.1+a • nativeScalarDirection coefficients) spin color*
        sourceTripletRead (value spin) color)=
      SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual.conjugateMatter 0 value+
        (∑ spin : Fin 4,∑ color : Fin 3,fieldDualComplex jet.1 spin color*sourceTripletRead (value spin) color)
    simp only [scalarShift_dual]

theorem nativeScalarValueShift_density (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (a : ℝ) :
    nativeJetDensity (nativeScalarValueShift jet coefficients a)=
      motherScalarCurve (affineSignal jet) 0 (fieldScalar (nativeScalarDirection coefficients))
        (pointwiseScalarVariationAlgebraicDirection ((nativeConfiguration (affineSignal jet)).gaugeConnection 0)
          (fieldScalar (nativeScalarDirection coefficients))) a := by
  rw [nativeJetDensity_generated,nativeScalarValueShift_point]
  unfold motherScalarCurve motherDensityAt
  rw [nativeJetPoint_generated]

/-- The source scalar value curve generates the actual full-native value coefficient. -/
theorem nativeScalarValueCoefficient_generated (jet : NativeFirstJet) (coefficients : Fin 9→ℝ)
    (inside : jet∈nativeEulerSourceDomain) :
    fderiv ℝ nativeJetDensity jet (nativeScalarDirection coefficients,0)=
      diracDualScalarFirstVariationDensity positiveSmoothUnifiedSource 0 (nativeJetPoint jet)
        (fieldScalar (nativeScalarDirection coefficients))
        (pointwiseScalarVariationAlgebraicDirection ((nativeConfiguration (affineSignal jet)).gaugeConnection 0)
          (fieldScalar (nativeScalarDirection coefficients))) := by
  have regular : ContDiffAt ℝ 2 nativeJetDensity jet := inside
  have ray : HasDerivAt (fun a : ℝ=>nativeScalarValueShift jet coefficients a)
      (nativeScalarDirection coefficients,0) 0 := by
    have source:=((hasDerivAt_id (0 : ℝ)).smul_const (nativeScalarDirection coefficients,0)).const_add jet
    convert! source using 1
    · funext a
      apply Prod.ext
      · rfl
      · simp [nativeScalarValueShift]
    · simp only [one_smul]
  have derivative := (regular.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ray (by simp [nativeScalarValueShift])
  have source := motherScalarCurve_generated (affineSignal jet) 0 (fieldScalar (nativeScalarDirection coefficients))
    (pointwiseScalarVariationAlgebraicDirection ((nativeConfiguration (affineSignal jet)).gaugeConnection 0)
      (fieldScalar (nativeScalarDirection coefficients)))
  have law : (fun a : ℝ=>nativeJetDensity (nativeScalarValueShift jet coefficients a))=
      motherScalarCurve (affineSignal jet) 0 (fieldScalar (nativeScalarDirection coefficients))
        (pointwiseScalarVariationAlgebraicDirection ((nativeConfiguration (affineSignal jet)).gaugeConnection 0)
          (fieldScalar (nativeScalarDirection coefficients))) := funext (nativeScalarValueShift_density jet coefficients)
  change HasDerivAt (fun a : ℝ=>nativeJetDensity (nativeScalarValueShift jet coefficients a)) _ 0 at derivative
  rw [law] at derivative
  have equality := derivative.unique source
  rw [nativeJetPoint_generated] at equality
  exact equality

def nativeScalarSlopeDirection (coefficients : Fin 9→ℝ) (mu nu : Fin 4) : Field289 :=
  if nu=mu then nativeScalarDirection coefficients else 0

def nativeScalarSlopeShift (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (mu : Fin 4) (a : ℝ) : NativeFirstJet :=
  (jet.1,jet.2+a • nativeScalarSlopeDirection coefficients mu)

private theorem scalarSlope_gauge (coefficients : Fin 9→ℝ) (mu nu rho : Fin 4) :
    fieldGauge (nativeScalarSlopeDirection coefficients mu nu) rho=0 := by
  by_cases h : nu=mu
  · simp only [nativeScalarSlopeDirection,if_pos h,scalarDirection_gauge]
  · simp [nativeScalarSlopeDirection,h,fieldGauge]

private theorem scalarSlope_lorentz (coefficients : Fin 9→ℝ) (mu nu : Fin 4) :
    lorentzInsertionCLM (nativeScalarSlopeDirection coefficients mu nu)=0 := by
  by_cases h : nu=mu
  · simp only [nativeScalarSlopeDirection,if_pos h]
    change lorentzSkewConnectionOfBivectorOneForm (fieldLorentz (nativeScalarDirection coefficients))=0
    rw [scalarDirection_lorentz]
    simp [lorentzSkewConnectionOfBivectorOneForm,loweredLorentzBivectorMatrix]
  · simp only [nativeScalarSlopeDirection,if_neg h,map_zero]

private theorem scalarSlope_primal (coefficients : Fin 9→ℝ) (mu nu : Fin 4) (spin : Fin 4) (color : Fin 3) :
    primalCoefficientCLM spin color (nativeScalarSlopeDirection coefficients mu nu)=0 := by
  by_cases h : nu=mu
  · simp only [nativeScalarSlopeDirection,if_pos h]
    exact scalarDirection_primal coefficients spin color
  · simp only [nativeScalarSlopeDirection,if_neg h,map_zero]

private theorem scalarSlopeShift_gauge (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (mu : Fin 4) (a : ℝ) (nu rho : Fin 4) :
    fieldGauge (jet.2 nu+a • nativeScalarSlopeDirection coefficients mu nu) rho=fieldGauge (jet.2 nu) rho := by
  simp only [nativeScalarSlopeShift,Pi.add_apply,Pi.smul_apply,fieldGauge_add,fieldGauge_smul,scalarSlope_gauge,smul_zero,add_zero]

private theorem scalarSlopeShift_lorentz (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (mu : Fin 4) (a : ℝ) (nu : Fin 4) :
    lorentzInsertionCLM (jet.2 nu+a • nativeScalarSlopeDirection coefficients mu nu)=lorentzInsertionCLM (jet.2 nu) := by
  simp only [nativeScalarSlopeShift,Pi.add_apply,Pi.smul_apply,map_add,map_smul,scalarSlope_lorentz,smul_zero,add_zero]

private theorem scalarSlopeShift_primal (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (mu : Fin 4) (a : ℝ)
    (nu spin : Fin 4) (color : Fin 3) :
    fieldPrimalComplex (jet.2 nu+a • nativeScalarSlopeDirection coefficients mu nu) spin color=fieldPrimalComplex (jet.2 nu) spin color := by
  change primalCoefficientCLM spin color (jet.2 nu+a • nativeScalarSlopeDirection coefficients mu nu)=
    primalCoefficientCLM spin color (jet.2 nu)
  rw [map_add,map_smul,scalarSlope_primal,smul_zero,add_zero]

theorem nativeScalarSlopeShift_point (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (mu : Fin 4) (a : ℝ) :
    nativeJetPoint (nativeScalarSlopeShift jet coefficients mu a)=
      withScalarJets (nativeJetPoint jet) (nativeJetPoint jet).scalar
        ((nativeJetPoint jet).scalarCovariantDerivative+a •
          scalarVariationDifferentialDirection (fieldScalar (nativeScalarDirection coefficients)) mu) := by
  apply StageNineContinuumPointField.ext
  · rfl
  · change SourcePropagationNativeActionHessian.nativeGravityCurvature (nativeScalarSlopeShift jet coefficients mu a)=
      SourcePropagationNativeActionHessian.nativeGravityCurvature jet
    unfold SourcePropagationNativeActionHessian.nativeGravityCurvature
    simp only [nativeScalarSlopeShift,Pi.add_apply,Pi.smul_apply,scalarSlopeShift_lorentz]
  · rfl
  · rfl
  · funext pair
    simp only [nativeJetPoint,withScalarJets,nativeGaugeCurvature,nativeScalarSlopeShift,Pi.add_apply,Pi.smul_apply,
      scalarSlopeShift_gauge]
  · rfl
  · rfl
  · funext nu
    change nativeScalarCovariant (nativeScalarSlopeShift jet coefficients mu a) nu=nativeScalarCovariant jet nu+
      a • scalarVariationDifferentialDirection (fieldScalar (nativeScalarDirection coefficients)) mu nu
    unfold nativeScalarCovariant
    simp only [nativeScalarSlopeShift,Pi.add_apply,Pi.smul_apply,fieldScalar_add,fieldScalar_smul,
      nativeScalarSlopeDirection,scalarVariationDifferentialDirection]
    by_cases h : nu=mu
    · simp only [if_pos h]
      module
    · simp only [if_neg h,fieldScalar,Pi.zero_apply,zero_smul,Finset.sum_const_zero,smul_zero,add_zero]
  · rfl
  · funext nu
    simp only [nativeJetPoint,withScalarJets,nativeMatterCovariant,rotatedPrimalDerivative,nativeMatterValue,
      nativeScalarSlopeShift,Pi.add_apply,Pi.smul_apply,scalarSlopeShift_primal]
  · rfl

theorem nativeScalarSlopeShift_density (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (mu : Fin 4) (a : ℝ) :
    nativeJetDensity (nativeScalarSlopeShift jet coefficients mu a)=
      motherScalarMomentumCurve (affineSignal jet) 0 (fieldScalar (nativeScalarDirection coefficients)) mu a := by
  rw [nativeJetDensity_generated,nativeScalarSlopeShift_point]
  unfold motherScalarMomentumCurve motherScalarCurve motherDensityAt
  rw [nativeJetPoint_generated]
  simp only [smul_zero,add_zero]

theorem nativeScalarMomentumCoefficient_generated (jet : NativeFirstJet) (coefficients : Fin 9→ℝ)
    (inside : jet∈nativeEulerSourceDomain) (mu : Fin 4) :
    fderiv ℝ nativeJetDensity jet (0,nativeScalarSlopeDirection coefficients mu)=
      scalarDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration (affineSignal jet))
        (fieldScalar (nativeScalarDirection coefficients)) mu 0 := by
  have regular : ContDiffAt ℝ 2 nativeJetDensity jet := inside
  have ray : HasDerivAt (fun a : ℝ=>nativeScalarSlopeShift jet coefficients mu a)
      (0,nativeScalarSlopeDirection coefficients mu) 0 := by
    have source:=((hasDerivAt_id (0 : ℝ)).smul_const (0,nativeScalarSlopeDirection coefficients mu)).const_add jet
    convert! source using 1
    · funext a
      apply Prod.ext
      · simp [nativeScalarSlopeShift]
      · rfl
    · simp only [one_smul]
  have derivative := (regular.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ray
    (by simp [nativeScalarSlopeShift])
  have source := motherScalarMomentumCurve_generated (affineSignal jet) 0 (fieldScalar (nativeScalarDirection coefficients)) mu
  have law : (fun a : ℝ=>nativeJetDensity (nativeScalarSlopeShift jet coefficients mu a))=
      motherScalarMomentumCurve (affineSignal jet) 0 (fieldScalar (nativeScalarDirection coefficients)) mu :=
    funext (nativeScalarSlopeShift_density jet coefficients mu)
  change HasDerivAt (fun a : ℝ=>nativeJetDensity (nativeScalarSlopeShift jet coefficients mu a)) _ 0 at derivative
  rw [law] at derivative
  exact derivative.unique source

/-- The common point field keeps all bosonic coordinates and transports both independent matter legs with the actual source rotation. -/
def rotatedMotherPoint (point : BasePoint) (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    matter:=diracMatrixMatterAction (ActiveGauge.rotation point) field.matter
    matterCovariantDerivative:=fun mu=>diracMatrixMatterAction (ActiveGauge.rotation point) (field.matterCovariantDerivative mu)
    conjugateMatter:=field.conjugateMatter.comp (diracMatrixMatterAction (ActiveGauge.rotation point)) }

theorem nativeLocalPoint_common (point : BasePoint) (jet : NativeFirstJet) :
    nativeLocalPoint point jet=rotatedMotherPoint point (nativeJetPoint jet) := by
  apply StageNineContinuumPointField.ext
  · exact nativeLocalCoframe_generated point jet
  · exact nativeLocalGravityCurvature_generated point jet
  · exact nativeLocalGravityAuxiliary_generated point jet
  · exact nativeLocalGravityMultiplier_generated point jet
  · exact nativeLocalGaugeCurvature_generated point jet
  · exact nativeLocalGaugeAuxiliary_generated point jet
  · exact nativeLocalScalar_generated point jet
  · exact nativeLocalScalarCovariant_generated point jet
  · exact nativeLocalMatter_rotated point jet
  · funext mu
    exact nativeLocalMatterCovariant_rotated point jet mu
  · exact nativeLocalDual_rotated point jet

private theorem anchoredGauge_common (point : BasePoint) (jet : NativeFirstJet) :
    (nativeConfiguration (anchoredSignal point jet)).gaugeConnection point=
      (nativeConfiguration (affineSignal jet)).gaugeConnection 0 := by
  funext mu
  unfold nativeConfiguration
  dsimp only
  simp only [anchoredSignal_value,affineSignal_zero,Stage9C.Material.SpinPair.actual_gaugeConnection]

theorem nativeLocalScalarValueShift_point (point : BasePoint) (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (a : ℝ) :
    nativeLocalPoint point (nativeScalarValueShift jet coefficients a)=
      withScalarJets (nativeLocalPoint point jet)
        ((nativeLocalPoint point jet).scalar+a • fieldScalar (nativeScalarDirection coefficients))
        ((nativeLocalPoint point jet).scalarCovariantDerivative+a • pointwiseScalarVariationAlgebraicDirection
          ((nativeConfiguration (anchoredSignal point jet)).gaugeConnection point) (fieldScalar (nativeScalarDirection coefficients))) := by
  rw [nativeLocalPoint_common,nativeScalarValueShift_point,nativeLocalPoint_common,anchoredGauge_common]
  rfl

theorem nativeLocalScalarSlopeShift_point (point : BasePoint) (jet : NativeFirstJet) (coefficients : Fin 9→ℝ)
    (mu : Fin 4) (a : ℝ) :
    nativeLocalPoint point (nativeScalarSlopeShift jet coefficients mu a)=
      withScalarJets (nativeLocalPoint point jet) (nativeLocalPoint point jet).scalar
        ((nativeLocalPoint point jet).scalarCovariantDerivative+a •
          scalarVariationDifferentialDirection (fieldScalar (nativeScalarDirection coefficients)) mu) := by
  rw [nativeLocalPoint_common,nativeScalarSlopeShift_point,nativeLocalPoint_common]
  rfl

theorem nativeLocalScalarValueShift_density (point : BasePoint) (jet : NativeFirstJet) (coefficients : Fin 9→ℝ) (a : ℝ) :
    nativeJetDensity (nativeScalarValueShift jet coefficients a)=
      motherScalarAlgebraicCurve (anchoredSignal point jet) point (fieldScalar (nativeScalarDirection coefficients)) a := by
  rw [←nativeLocalAction_pointfree point (nativeScalarValueShift jet coefficients a),nativeLocalAction_original,
    nativeLocalScalarValueShift_point]
  unfold motherScalarAlgebraicCurve motherScalarCurve motherDensityAt nativeLocalPoint
  unfold nativeActionJet generatedDiracDualFormNativePointwiseActionJet
  rfl

theorem nativeLocalScalarSlopeShift_density (point : BasePoint) (jet : NativeFirstJet) (coefficients : Fin 9→ℝ)
    (mu : Fin 4) (a : ℝ) :
    nativeJetDensity (nativeScalarSlopeShift jet coefficients mu a)=
      motherScalarMomentumCurve (anchoredSignal point jet) point (fieldScalar (nativeScalarDirection coefficients)) mu a := by
  rw [←nativeLocalAction_pointfree point (nativeScalarSlopeShift jet coefficients mu a),nativeLocalAction_original,
    nativeLocalScalarSlopeShift_point]
  unfold motherScalarMomentumCurve motherScalarCurve motherDensityAt nativeLocalPoint
  simp only [smul_zero,add_zero]

private theorem scalarValueShift_derivative (jet : NativeFirstJet) (coefficients : Fin 9→ℝ)
    (inside : jet∈nativeEulerSourceDomain) :
    HasDerivAt (fun a : ℝ=>nativeJetDensity (nativeScalarValueShift jet coefficients a))
      (fderiv ℝ nativeJetDensity jet (nativeScalarDirection coefficients,0)) 0 := by
  have regular : ContDiffAt ℝ 2 nativeJetDensity jet := inside
  have ray : HasDerivAt (fun a : ℝ=>nativeScalarValueShift jet coefficients a)
      (nativeScalarDirection coefficients,0) 0 := by
    have source:=((hasDerivAt_id (0 : ℝ)).smul_const (nativeScalarDirection coefficients,0)).const_add jet
    convert! source using 1
    · funext a
      apply Prod.ext
      · rfl
      · simp [nativeScalarValueShift]
    · simp only [one_smul]
  exact (regular.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ray (by simp [nativeScalarValueShift])

private theorem scalarSlopeShift_derivative (jet : NativeFirstJet) (coefficients : Fin 9→ℝ)
    (inside : jet∈nativeEulerSourceDomain) (mu : Fin 4) :
    HasDerivAt (fun a : ℝ=>nativeJetDensity (nativeScalarSlopeShift jet coefficients mu a))
      (fderiv ℝ nativeJetDensity jet (0,nativeScalarSlopeDirection coefficients mu)) 0 := by
  have regular : ContDiffAt ℝ 2 nativeJetDensity jet := inside
  have ray : HasDerivAt (fun a : ℝ=>nativeScalarSlopeShift jet coefficients mu a)
      (0,nativeScalarSlopeDirection coefficients mu) 0 := by
    have source:=((hasDerivAt_id (0 : ℝ)).smul_const (0,nativeScalarSlopeDirection coefficients mu)).const_add jet
    convert! source using 1
    · funext a
      apply Prod.ext
      · simp [nativeScalarSlopeShift]
      · rfl
    · simp only [one_smul]
  exact (regular.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ray (by simp [nativeScalarSlopeShift])

theorem nativeScalarValueCoefficient_atPoint (point : BasePoint) (jet : NativeFirstJet) (coefficients : Fin 9→ℝ)
    (inside : jet∈nativeEulerSourceDomain) :
    fderiv ℝ nativeJetDensity jet (nativeScalarDirection coefficients,0)=
      deriv (motherScalarAlgebraicCurve (anchoredSignal point jet) point (fieldScalar (nativeScalarDirection coefficients))) 0 := by
  have derivative:=scalarValueShift_derivative jet coefficients inside
  have law : (fun a : ℝ=>nativeJetDensity (nativeScalarValueShift jet coefficients a))=
      motherScalarAlgebraicCurve (anchoredSignal point jet) point (fieldScalar (nativeScalarDirection coefficients)) :=
    funext (nativeLocalScalarValueShift_density point jet coefficients)
  rw [law] at derivative
  exact derivative.deriv.symm

theorem nativeScalarMomentumCoefficient_atPoint (point : BasePoint) (jet : NativeFirstJet) (coefficients : Fin 9→ℝ)
    (inside : jet∈nativeEulerSourceDomain) (mu : Fin 4) :
    fderiv ℝ nativeJetDensity jet (0,nativeScalarSlopeDirection coefficients mu)=
      scalarDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration (anchoredSignal point jet))
        (fieldScalar (nativeScalarDirection coefficients)) mu point := by
  have derivative:=scalarSlopeShift_derivative jet coefficients inside mu
  have law : (fun a : ℝ=>nativeJetDensity (nativeScalarSlopeShift jet coefficients mu a))=
      motherScalarMomentumCurve (anchoredSignal point jet) point (fieldScalar (nativeScalarDirection coefficients)) mu :=
    funext (nativeLocalScalarSlopeShift_density point jet coefficients mu)
  rw [law] at derivative
  exact derivative.unique (motherScalarMomentumCurve_generated (anchoredSignal point jet) point
    (fieldScalar (nativeScalarDirection coefficients)) mu)

private theorem scalarGauge_firstGerm (signal : BasePoint→Field289) (point : BasePoint) :
    (nativeConfiguration (anchoredSignal point (signalFirstJet signal point))).gaugeConnection point=
      (nativeConfiguration signal).gaugeConnection point := by
  funext mu
  unfold nativeConfiguration
  dsimp only
  rw [anchoredSignal_value]
  rfl

private theorem scalarAlgebraic_firstGerm (signal : BasePoint→Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) (coefficients : Fin 9→ℝ) :
    motherScalarAlgebraicCurve (anchoredSignal point (signalFirstJet signal point)) point
      (fieldScalar (nativeScalarDirection coefficients))=
      motherScalarAlgebraicCurve signal point (fieldScalar (nativeScalarDirection coefficients)) := by
  have gauge : (nativeActionJet (anchoredSignal point (signalFirstJet signal point)) point).p286GaugeConnection=
      (nativeActionJet signal point).p286GaugeConnection := by
    unfold nativeActionJet generatedDiracDualFormNativePointwiseActionJet
    exact scalarGauge_firstGerm signal point
  unfold motherScalarAlgebraicCurve
  rw [gauge]
  unfold motherScalarCurve
  have fields:=nativePoint_signalFirstJet signal point differentiable
  unfold nativeLocalPoint at fields
  rw [←fields]

private theorem scalarMomentum_firstGerm (signal : BasePoint→Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) (direction : ScalarCoordinateCarrier) (mu : Fin 4) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
      (nativeConfiguration (anchoredSignal point (signalFirstJet signal point))) direction mu point=
      scalarDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal) direction mu point := by
  have fields:=nativePoint_signalFirstJet signal point differentiable
  unfold nativeLocalPoint nativePoint at fields
  unfold scalarDifferentialMomentum
  rw [←fields]

theorem nativeScalarValueCoefficient_signal (signal : BasePoint→Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) (coefficients : Fin 9→ℝ)
    (inside : signalFirstJet signal point∈nativeEulerSourceDomain) :
    fderiv ℝ nativeJetDensity (signalFirstJet signal point) (nativeScalarDirection coefficients,0)=
      deriv (motherScalarAlgebraicCurve signal point (fieldScalar (nativeScalarDirection coefficients))) 0 := by
  rw [nativeScalarValueCoefficient_atPoint point (signalFirstJet signal point) coefficients inside,
    scalarAlgebraic_firstGerm signal point differentiable coefficients]

theorem nativeScalarMomentumCoefficient_signal (signal : BasePoint→Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) (coefficients : Fin 9→ℝ)
    (inside : signalFirstJet signal point∈nativeEulerSourceDomain) (mu : Fin 4) :
    fderiv ℝ nativeJetDensity (signalFirstJet signal point) (0,nativeScalarSlopeDirection coefficients mu)=
      scalarDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal)
        (fieldScalar (nativeScalarDirection coefficients)) mu point := by
  rw [nativeScalarMomentumCoefficient_atPoint point (signalFirstJet signal point) coefficients inside mu,
    scalarMomentum_firstGerm signal point differentiable]

theorem nativeScalarDirection_single (index : Fin 9) :
    nativeScalarDirection (Pi.single index 1)=Pi.single (scalarSlot index) 1 := by
  funext field
  by_cases active : field.val<9
  · have identity : (⟨field.val,active⟩ : Fin 9)=index ↔ field=scalarSlot index := by
      constructor
      · intro same
        apply Fin.ext
        exact congrArg (fun element : Fin 9=>element.val) same
      · intro same
        apply Fin.ext
        exact congrArg (fun element : Fin 289=>element.val) same
    simp only [nativeScalarDirection,dif_pos active,Pi.single_apply,identity]
  · have distinct : field≠scalarSlot index := by
      intro same
      have values:=congrArg Fin.val same
      simp only [scalarSlot] at values
      omega
    simp [nativeScalarDirection,active,Pi.single_apply,distinct]

theorem nativeScalarSlopeDirection_single (index : Fin 9) (mu : Fin 4) :
    nativeScalarSlopeDirection (Pi.single index 1) mu=Pi.single mu (Pi.single (scalarSlot index) 1) := by
  funext nu
  simp only [nativeScalarSlopeDirection,nativeScalarDirection_single,Pi.single_apply]

private theorem scalarSignal_near (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (inside : signalFirstJet signal point∈nativeEulerSourceDomain) :
    ∀ᶠ position in 𝓝 point,DifferentiableAt ℝ signal position ∧ signalFirstJet signal position∈nativeEulerSourceDomain := by
  have signalNear:=smooth.eventually (by simp)
  have regular : ContDiffAt ℝ 2 nativeJetDensity (signalFirstJet signal point) := inside
  have domainNear : nativeEulerSourceDomain∈𝓝 (signalFirstJet signal point) := regular.eventually (by simp)
  have sourceNear:=((signalFirstJet_source_smooth signal point smooth).continuousAt).eventually_mem domainNear
  filter_upwards [signalNear,sourceNear] with position hs hi
  exact ⟨hs.differentiableAt (by norm_num),hi⟩

theorem nativeScalarEuler_identification (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (inside : signalFirstJet signal point∈nativeEulerSourceDomain)
    (index : Fin 9) :
    nativeHolonomicEuler signal point (scalarSlot index)=
      (nativeEuler signal point).scalar (fieldScalar (Pi.single (scalarSlot index) 1)) := by
  have value:=nativeScalarValueCoefficient_signal signal point (smooth.differentiableAt (by norm_num)) (Pi.single index 1) inside
  simp only [nativeScalarDirection_single] at value
  have momentum (mu : Fin 4) :
      (fun position=>fderiv ℝ nativeJetDensity (signalFirstJet signal position) (nativeJetBasis (some mu,scalarSlot index)))=ᶠ[𝓝 point]
        scalarDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal)
          (fieldScalar (Pi.single (scalarSlot index) 1)) mu := by
    filter_upwards [scalarSignal_near signal point smooth inside] with position hp
    have source:=nativeScalarMomentumCoefficient_signal signal position hp.1 (Pi.single index 1) hp.2 mu
    simpa only [nativeScalarSlopeDirection_single,nativeScalarDirection_single,nativeJetBasis] using source
  rw [motherScalarEuler_action]
  unfold nativeHolonomicEuler
  simp only [nativeLocalAction_atPoint]
  rw [show nativeJetBasis (none,scalarSlot index)=(Pi.single (scalarSlot index) 1,0) by rfl,value]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  unfold fieldDirectionalDerivative
  rw [(momentum mu).fderiv_eq]
  apply congrArg (fun f : BasePoint→ℝ=>fderiv ℝ f point (coordinateDirection mu))
  funext position
  exact (motherScalarMomentumCurve_generated signal position (fieldScalar (Pi.single (scalarSlot index) 1)) mu).deriv.symm

end LowEnergy.SourcePropagationMotherResidualDirections
