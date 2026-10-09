import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalSourceColumns

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeSourceRestriction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineDynamicBreakingVacuum
open Stage9C.Material.SpinPair PointwiseDiracSpinConnectionLift StageNineLorentzConnectionVariation
open FullQuantum.StateGreen FullQuantum.CoframeResponse SourceQuantumScalarChart SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert GaussHistoryHilbert GaussNativeMatter GaussQuantumMultiplier
open PreparationVacuumSourceFieldFamily PreparationVacuumGaugeSourceInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection PreparationVacuumLorentzFieldInjection
open PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve PreparationVacuumOriginalDensity
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumFullFieldRiesz
open PreparationVacuumActualFieldQuantization PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open GaussCoreHilbert GaussCoreDifferential
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

/-- Actual preparation fields; its scalar belongs to all70, independently of the source-point scalar9 restriction. -/
def familyPrimitiveData (z : SourceCoordinateSlice) : FieldData:=
  ((emitter z).scalar 0,(fun mu=>p286CoordinateEquiv ((emitter z).gaugeConnection 0 mu)),
    (emitter z).coframe 0,(fun mu a=>loweredLorentzConnectionCoefficient ((emitter z).gravityConnection 0) mu a))

theorem familyPrimitiveData_state (z : SourceCoordinateSlice) :
    stateDirectionMap (familyPrimitiveData z)=sourceState z :=by
  rw [←configurationState_emitter]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext mu
    change spinLinear mu (familyPrimitiveData z).2.2.2+nativePrimal ((familyPrimitiveData z).2.1 mu)=
      Quantum.operatorMatrix (FullQuantum.connection (emitter z) 0 mu)
    rw [originalConnection_source]
    apply congrArg (fun M : SourceMatrix=>M+nativePrimal (show SourceQuantumScalarChart.NativeLie from
      p286CoordinateEquiv ((emitter z).gaugeConnection 0 mu)))
    change spinCoordinates (diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm
      (fun nu a=>loweredLorentzConnectionCoefficient ((emitter z).gravityConnection 0) nu a)) mu)=
      spinCoordinates (diracSpinConnectionLift ((emitter z).gravityConnection 0) mu)
    apply congrArg spinCoordinates
    simp only [diracSpinConnectionLift,loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  · rfl

def ambientPrimitiveData (u : JointParameter) : FieldData:=familyPrimitiveData u.2+sourceData u.1

theorem ambientPrimitiveData_state (u : JointParameter) :
    stateDirectionMap (ambientPrimitiveData u)=ambientState u :=by
  rw [ambientPrimitiveData,map_add,familyPrimitiveData_state,stateDirection_source]
  rfl

def primitiveFamily (u : JointParameter) : StageNineHolonomicConfiguration:=
  configurationFromFields (emitter u.2) (fun _=>ambientPrimitiveData u)

def nativePrimitiveFamily (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (u : JointParameter) : StageNineHolonomicConfiguration:=
  Fin.addCases (fun g : Fin 3=>colorPrimitiveDirection g (fun _=>theta) (fun _=>gradient) (primitiveFamily u))
    (fun a : Fin 6=>lorentzPrimitiveDirection a (fun _=>theta) (fun _=>gradient)
      (primitiveFamily u) (fun _=>ambientPrimitiveData u)) n

theorem nativePrimitiveFamily_state (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) (u : JointParameter) :
    configurationState (nativePrimitiveFamily n theta gradient u) 0=
      stateVariation n theta gradient (ambientState u) :=by
  refine Fin.addCases (motive:=fun n : Fin 9=>configurationState (nativePrimitiveFamily n theta gradient u) 0=
    stateVariation n theta gradient (ambientState u)) (fun g : Fin 3=>?_) (fun a : Fin 6=>?_) n
  · simp only [nativePrimitiveFamily,Fin.addCases_left]
    rw [colorPrimitive_state,primitiveFamily,configurationFromFields_state,ambientPrimitiveData_state]
  · simp only [nativePrimitiveFamily,Fin.addCases_right]
    rw [lorentzPrimitive_state,configurationFromFields_state,ambientPrimitiveData_state]

/-- The two mixed symmetry legs are generated on the actual full configuration family. -/
theorem nativePrimitiveFamily_contact (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (force : Field289) (z : SourceCoordinateSlice) :
    HasDerivAt (fun r : ℝ=>configurationState (nativePrimitiveFamily n theta gradient (r • force,z)) 0)
      (stateContact n theta (fieldDirection force)) 0 :=by
  simp only [nativePrimitiveFamily_state]
  exact sourceStateContact_generated n theta gradient force z

theorem nativePrimitiveFamily_independent_pair (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (u : JointParameter) :
    (nativePrimitiveFamily n theta gradient u).conjugateMatter 0 ((primitiveFamily u).matter 0)+
      (primitiveFamily u).conjugateMatter 0 ((nativePrimitiveFamily n theta gradient u).matter 0)=0 :=by
  refine Fin.addCases (motive:=fun n : Fin 9=>
    (nativePrimitiveFamily n theta gradient u).conjugateMatter 0 ((primitiveFamily u).matter 0)+
      (primitiveFamily u).conjugateMatter 0 ((nativePrimitiveFamily n theta gradient u).matter 0)=0)
      (fun g : Fin 3=>?_) (fun a : Fin 6=>?_) n
  · simp only [nativePrimitiveFamily,Fin.addCases_left]
    exact colorPrimitive_independent_pair g (fun _=>theta) (fun _=>gradient) (primitiveFamily u) 0
  · simp only [nativePrimitiveFamily,Fin.addCases_right]
    exact lorentzPrimitive_independent_pair a (fun _=>theta) (fun _=>gradient)
      (primitiveFamily u) (fun _=>ambientPrimitiveData u) 0

def primitiveActionDerivative (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) (u : JointParameter) : FullMatrix:=
  symbolFirst p (ambientState u) (configurationState (nativePrimitiveFamily n theta gradient u) 0)

theorem primitiveActionDerivative_source (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) (u : JointParameter) :
    primitiveActionDerivative n theta gradient p u=nativeFirst n theta gradient p (ambientState u) :=by
  simp only [primitiveActionDerivative,nativePrimitiveFamily_state,nativeFirst]

def primitiveJointFiber (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) (u : JointParameter) : FockFiber→L[ℂ] FockFiber:=
  quantizer (-(4:ℂ) • (sourceActionWeight (sourceState u.2)*primitiveActionDerivative n theta gradient p u))

theorem primitiveJointFiber_source (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) (u : JointParameter) :
    primitiveJointFiber n theta gradient p u=nativeJointFiber n theta gradient p u :=by
  rw [primitiveJointFiber,primitiveActionDerivative_source]
  rfl

theorem primitiveJointFiber_contact (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (force : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>primitiveJointFiber n theta gradient p (r • force,z.val))
      (quantizer (nativeNoetherMixed n theta gradient force p (sourceState z.val) (sourceState z.val))) 0 :=by
  simp only [primitiveJointFiber_source]
  exact nativeJointFiber_generated n theta gradient force p z

def primitiveForm (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ:=
  ∫z,pairSample z (a z) (primitiveJointFiber n theta gradient p (h,z) (b z))
    ∂GaussHistoryHilbert.configurationMeasure

theorem primitiveForm_source (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) (a b : QuantumTest) (h : Field289) :
    primitiveForm n theta gradient p a b h=nativeForm n theta gradient p a b h :=by
  simp only [primitiveForm,primitiveJointFiber_source,PreparationVacuumNativeLocalWard.nativeForm,PreparationVacuumNativeLocalWard.nativeSample]

theorem primitiveForm_C2 (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) (a b : QuantumTest) :
    ContDiffAt ℝ 2 (primitiveForm n theta gradient p a b) 0 :=by
  have source : primitiveForm n theta gradient p a b=nativeForm n theta gradient p a b:=
    funext (primitiveForm_source n theta gradient p a b)
  rw [source]
  exact nativeForm_C2 n theta gradient p a b

theorem primitiveForm_contact (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (force : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (fun r : ℝ=>primitiveForm n theta gradient p a b (r • force))
      (nativeContactForm n theta gradient force p a b) 0 :=by
  simp only [primitiveForm_source]
  exact nativeForm_generated n theta gradient force p a b

theorem primitiveReader_source (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    finiteRiesz F (fun i j=>primitiveForm n theta gradient p (frameTest F i) (frameTest F j) h)=
      nativeReader n theta gradient p F h :=by
  simp only [primitiveForm_source,nativeReader]

theorem nativePreparedCurrent_primitive (q : PhysicalResponsePoint) (n : Fin 9)
    (theta : ℝ) (gradient : Fin 4→ℝ) (h : Field289) (age : ℝ) :
    nativePreparedCurrent q n theta gradient h age=
      preparedDual q h age ((finiteRiesz q.F (fun i j=>primitiveForm n theta gradient q.p
        (frameTest q.F i) (frameTest q.F j) h)) (preparedPrimal q h age)) :=by
  rw [primitiveReader_source]
  rfl

theorem primitivePreparedFive_generated (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ)
    (gradient : Fin 4→ℝ) (force : Field289) (age : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>preparedDual q (r • force) age ((finiteRiesz q.F
      (fun i j=>primitiveForm n theta gradient q.p (frameTest q.F i) (frameTest q.F j) (r • force)))
        (preparedPrimal q (r • force) age)))
      (inner ℂ (responseLeft q) (nativePreparedFive q n theta gradient force age (responseRight q))) 0 :=by
  simp only [←nativePreparedCurrent_primitive]
  exact nativePreparedCurrent_generated q n theta gradient force age hz hw

theorem primitivePrepared_initial (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ)
    (gradient : Fin 4→ℝ) (h : Field289) :
    nativePreparedCurrent q n theta gradient h 0=
      inner ℂ (responseLeft q) (jointResolvent (q.p+q.k) q.F q.z h
        ((finiteRiesz q.F (fun i j=>primitiveForm n theta gradient q.p (frameTest q.F i) (frameTest q.F j) h))
          (jointResolvent q.p q.F q.w h (responseRight q)))) :=by
  rw [primitiveReader_source]
  exact nativePreparedCurrent_initial q n theta gradient h

end LowEnergy.PreparationVacuumNativeSourceRestriction
