import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceQuantumPoleDuhamel

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleLegDynamics
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalFeedback PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumIndependentMomentumReturn PreparationVacuumCurrentSignalOperator
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCreation GaussCoreHilbert GaussFockLift GaussComposite.SourceGraph
open SourceFiniteUnitary GaussQuantumMultiplier
open CanonicalPreparationCore.Completed CanonicalScalarPreparation PreparationChartGuard PreparationScalarCoordinates
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open scoped BigOperators Topology Matrix InnerProductSpace
attribute [local irreducible] jointGenerator jointResolvent sourcePolePrepared sourcePoleDual
  sourcePolePrimalCorrection sourcePoleDualCorrection sourceMovingIndependentReader

def sourcePhysicalPoleBase (q : PhysicalResponsePoint) : Base:=sourcePoleBase q.epsilon q.precision

theorem sourcePhysicalPole_same_created (q : PhysicalResponsePoint) :
    GaussComposite.SourceGraph.prepared (sourceProfile q.epsilon q.precision)=
      sourceCreated (sourcePhysicalPoleBase q) :=by
  change GaussComposite.SourceGraph.prepared
    (zeroLocalizedProfile actualNativeLocalizer (sourceCausalState q.epsilon q.precision).point.val)=_
  exact (sourcePreparation q.epsilon q.precision).created

def sourcePhysicalPrimalError (q : PhysicalResponsePoint) (rightMomentum : PhysicalMomentum)
    (right : RestStateIndex) (t : ℝ) : H:=
  jointResolvent rightMomentum q.F q.w 0
    (sourcePolePrimalCorrection q.epsilon q.precision rightMomentum right q.F t)

def sourcePhysicalDualError (q : PhysicalResponsePoint) (leftMomentum : PhysicalMomentum)
    (left : RestStateIndex) (t : ℝ) : H→L[ℂ] ℂ:=
  (sourcePoleDualCorrection q.epsilon q.precision leftMomentum left q.F t).comp
    (jointResolvent leftMomentum q.F q.z 0)

theorem sourcePhysicalPrimal_generated (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (right : RestStateIndex) (t : ℝ) :
    sourcePolePreparedPrimal q.epsilon q.precision rightMomentum right
      (sourcePhysicalMaterialPoint q leftMomentum rightMomentum) 0 t=
      Complex.exp ((-Complex.I)*(sourceMovingPoleEnergy rightMomentum right:ℂ)*(t:ℂ)) •
        jointResolvent rightMomentum q.F q.w 0 (sourcePolePrepared q.epsilon q.precision rightMomentum right)+
        sourcePhysicalPrimalError q rightMomentum right t :=by
  simp only [sourcePolePreparedPrimal,sourcePhysicalMaterialPoint]
  change jointResolvent rightMomentum q.F q.w 0
    (time (jointGenerator rightMomentum q.F 0 0) t (sourcePolePrepared q.epsilon q.precision rightMomentum right))=_
  rw [sourcePolePrimalCorrection_generated,map_add,map_smul]
  rfl

theorem sourcePhysicalDual_generated (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left : RestStateIndex) (t : ℝ) :
    sourcePoleIndependentDual q.epsilon q.precision leftMomentum left
      (sourcePhysicalMaterialPoint q leftMomentum rightMomentum) 0 t=
      Complex.exp (Complex.I*(sourceMovingPoleEnergy leftMomentum left:ℂ)*(t:ℂ)) •
        (sourcePoleDual q.epsilon q.precision leftMomentum left).comp (jointResolvent leftMomentum q.F q.z 0)+
        sourcePhysicalDualError q leftMomentum left t :=by
  rw [sourcePoleIndependentDual,sourcePhysicalMaterialPoint_left]
  simp only [sourcePhysicalMaterialPoint,physicalTime]
  have dual : innerSL ℂ (sourcePolePrepared q.epsilon q.precision leftMomentum left)=
      sourcePoleDual q.epsilon q.precision leftMomentum left :=by rw [sourcePoleDual]
  rw [dual]
  rw [sourcePoleDualCorrection_generated,ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp]
  rfl

def sourcePhysicalDensityCorrection (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) (t : ℝ) : ℂ:=
  let J:=sourceMovingIndependentReader reader rightMomentum q.F 0
  let baseDual:=(sourcePoleDual q.epsilon q.precision leftMomentum left).comp (jointResolvent leftMomentum q.F q.z 0)
  let basePrimal:=jointResolvent rightMomentum q.F q.w 0 (sourcePolePrepared q.epsilon q.precision rightMomentum right)
  Complex.exp (Complex.I*(sourceMovingPoleEnergy leftMomentum left:ℂ)*(t:ℂ))*
    baseDual (J (sourcePhysicalPrimalError q rightMomentum right t))+
  Complex.exp ((-Complex.I)*(sourceMovingPoleEnergy rightMomentum right:ℂ)*(t:ℂ))*
    sourcePhysicalDualError q leftMomentum left t (J basePrimal)+
    sourcePhysicalDualError q leftMomentum left t (J (sourcePhysicalPrimalError q rightMomentum right t))

theorem sourcePhysicalDensity_generated (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) (t : ℝ) :
    sourcePolePreparedDensity q.epsilon q.precision leftMomentum rightMomentum left right
      (sourcePhysicalMaterialPoint q leftMomentum rightMomentum) reader 0 t=
      Complex.exp (sourcePhysicalClock leftMomentum rightMomentum left right*(t:ℂ))*
        sourcePolePreparedDensity q.epsilon q.precision leftMomentum rightMomentum left right
          (sourcePhysicalMaterialPoint q leftMomentum rightMomentum) reader 0 0+
        sourcePhysicalDensityCorrection q leftMomentum rightMomentum left right reader t :=by
  rw [sourcePolePreparedDensity,sourcePhysicalPrimal_generated,sourcePhysicalDual_generated]
  have initial : sourcePolePreparedDensity q.epsilon q.precision leftMomentum rightMomentum left right
      (sourcePhysicalMaterialPoint q leftMomentum rightMomentum) reader 0 0=
    ((sourcePoleDual q.epsilon q.precision leftMomentum left).comp (jointResolvent leftMomentum q.F q.z 0))
      (sourceMovingIndependentReader reader rightMomentum q.F 0
        (jointResolvent rightMomentum q.F q.w 0 (sourcePolePrepared q.epsilon q.precision rightMomentum right))) :=by
    rw [sourcePolePreparedDensity,sourcePoleIndependentDual,sourcePolePreparedPrimal,sourcePhysicalMaterialPoint_left]
    simp only [sourcePhysicalMaterialPoint,physicalTime,neg_zero,time_zero,ContinuousLinearMap.comp_apply,
      one_apply_eq_self]
    rw [sourcePoleDual]
  rw [initial]
  simp only [sourcePhysicalMaterialPoint,sourcePhysicalDensityCorrection,add_apply,
    smul_apply,map_add,map_smul,smul_eq_mul]
  have phase : Complex.exp (Complex.I*(sourceMovingPoleEnergy leftMomentum left:ℂ)*(t:ℂ))*
      Complex.exp ((-Complex.I)*(sourceMovingPoleEnergy rightMomentum right:ℂ)*(t:ℂ))=
    Complex.exp (sourcePhysicalClock leftMomentum rightMomentum left right*(t:ℂ)) :=by
    rw [←Complex.exp_add]
    congr 1
    unfold sourcePhysicalClock
    push_cast
    ring
  rw [←phase]
  ring

theorem sourcePhysicalPrimalError_price (q : PhysicalResponsePoint) (rightMomentum : PhysicalMomentum)
    (right : RestStateIndex) (eta t : ℝ) (positive : 0<eta) (future : 0≤t) :
    ‖sourcePhysicalPrimalError q rightMomentum right t‖≤
      ‖jointResolvent rightMomentum q.F q.w 0‖*
        ((t*PreparationVacuumPhysicalTailPrice.factorialBudget rightMomentum q.F eta*Real.exp (eta*t))*
          ‖sourcePoleColumnDefect q.epsilon q.precision rightMomentum right q.F‖) :=by
  have actual:=(jointResolvent rightMomentum q.F q.w 0).le_opNorm
    (sourcePolePrimalCorrection q.epsilon q.precision rightMomentum right q.F t)
  exact actual.trans (mul_le_mul_of_nonneg_left
    (sourcePolePrimalCorrection_price q.epsilon q.precision rightMomentum right q.F eta t positive future) (norm_nonneg _))

theorem sourcePhysicalDualError_price (q : PhysicalResponsePoint) (leftMomentum : PhysicalMomentum)
    (left : RestStateIndex) (eta t : ℝ) (positive : 0<eta) (future : 0≤t) :
    ‖sourcePhysicalDualError q leftMomentum left t‖≤
      ((t*PreparationVacuumPhysicalTailPrice.factorialBudget leftMomentum q.F eta*Real.exp (eta*t))*
        ‖sourcePoleDualDefect q.epsilon q.precision leftMomentum left q.F‖)*‖jointResolvent leftMomentum q.F q.z 0‖ :=by
  have actual:=ContinuousLinearMap.opNorm_comp_le
    (sourcePoleDualCorrection q.epsilon q.precision leftMomentum left q.F t) (jointResolvent leftMomentum q.F q.z 0)
  exact actual.trans (mul_le_mul_of_nonneg_right
    (sourcePoleDualCorrection_price q.epsilon q.precision leftMomentum left q.F eta t positive future) (norm_nonneg _))

def sourcePhysicalPrimalPrice (q : PhysicalResponsePoint) (momentum : PhysicalMomentum) (state : RestStateIndex)
    (eta t : ℝ) : ℝ:=
  ‖jointResolvent momentum q.F q.w 0‖*
    ((t*PreparationVacuumPhysicalTailPrice.factorialBudget momentum q.F eta*Real.exp (eta*t))*
      ‖sourcePoleColumnDefect q.epsilon q.precision momentum state q.F‖)

def sourcePhysicalDualPrice (q : PhysicalResponsePoint) (momentum : PhysicalMomentum) (state : RestStateIndex)
    (eta t : ℝ) : ℝ:=
  ((t*PreparationVacuumPhysicalTailPrice.factorialBudget momentum q.F eta*Real.exp (eta*t))*
    ‖sourcePoleDualDefect q.epsilon q.precision momentum state q.F‖)*‖jointResolvent momentum q.F q.z 0‖

def sourcePhysicalDensityPrice (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) (eta t : ℝ) : ℝ:=
  ‖sourceMovingIndependentReader reader rightMomentum q.F 0‖*
    (‖jointResolvent leftMomentum q.F q.z 0‖*sourcePhysicalPrimalPrice q rightMomentum right eta t+
      ‖jointResolvent rightMomentum q.F q.w 0‖*sourcePhysicalDualPrice q leftMomentum left eta t+
      sourcePhysicalDualPrice q leftMomentum left eta t*sourcePhysicalPrimalPrice q rightMomentum right eta t)

private theorem pairCorrections_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (dual dualError : E→L[ℂ] ℂ) (primal primalError : E) (middle : E→L[ℂ] E)
    (leftPhase rightPhase : ℂ) (leftBound rightBound dualBound primalBound : ℝ)
    (phaseL : ‖leftPhase‖=1) (phaseR : ‖rightPhase‖=1)
    (leftPrice : ‖dual‖≤leftBound) (rightPrice : ‖primal‖≤rightBound)
    (dualPrice : ‖dualError‖≤dualBound) (primalPrice : ‖primalError‖≤primalBound) :
    ‖leftPhase*dual (middle primalError)+rightPhase*dualError (middle primal)+dualError (middle primalError)‖≤
      ‖middle‖*(leftBound*primalBound+rightBound*dualBound+dualBound*primalBound) :=by
  have right : ‖middle primal‖≤‖middle‖*rightBound:=
    (middle.le_opNorm primal).trans (mul_le_mul_of_nonneg_left rightPrice (norm_nonneg _))
  have correction : ‖middle primalError‖≤‖middle‖*primalBound:=
    (middle.le_opNorm primalError).trans (mul_le_mul_of_nonneg_left primalPrice (norm_nonneg _))
  have first : ‖leftPhase*dual (middle primalError)‖≤leftBound*(‖middle‖*primalBound) :=by
    rw [norm_mul,phaseL,one_mul]
    exact (dual.le_opNorm _).trans (mul_le_mul leftPrice correction (norm_nonneg _) ((norm_nonneg _).trans leftPrice))
  have second : ‖rightPhase*dualError (middle primal)‖≤dualBound*(‖middle‖*rightBound) :=by
    rw [norm_mul,phaseR,one_mul]
    exact (dualError.le_opNorm _).trans (mul_le_mul dualPrice right (norm_nonneg _) ((norm_nonneg _).trans dualPrice))
  have third : ‖dualError (middle primalError)‖≤dualBound*(‖middle‖*primalBound):=
    (dualError.le_opNorm _).trans (mul_le_mul dualPrice correction (norm_nonneg _) ((norm_nonneg _).trans dualPrice))
  calc
    _≤(‖leftPhase*dual (middle primalError)‖+‖rightPhase*dualError (middle primal)‖)+‖dualError (middle primalError)‖:=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _≤(leftBound*(‖middle‖*primalBound)+dualBound*(‖middle‖*rightBound))+dualBound*(‖middle‖*primalBound):=
      add_le_add (add_le_add first second) third
    _=_ :=by ring

theorem sourcePhysicalDensityCorrection_price (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) (eta t : ℝ) (positive : 0<eta) (future : 0≤t) :
    ‖sourcePhysicalDensityCorrection q leftMomentum rightMomentum left right reader t‖≤
      sourcePhysicalDensityPrice q leftMomentum rightMomentum left right reader eta t :=by
  have dual : ‖(sourcePoleDual q.epsilon q.precision leftMomentum left).comp (jointResolvent leftMomentum q.F q.z 0)‖≤
      ‖jointResolvent leftMomentum q.F q.z 0‖ :=by
    have cost:=ContinuousLinearMap.opNorm_comp_le (sourcePoleDual q.epsilon q.precision leftMomentum left)
      (jointResolvent leftMomentum q.F q.z 0)
    simpa only [sourcePoleDual,innerSL_apply_norm,sourcePolePrepared_unit,one_mul] using cost
  have primal : ‖jointResolvent rightMomentum q.F q.w 0 (sourcePolePrepared q.epsilon q.precision rightMomentum right)‖≤
      ‖jointResolvent rightMomentum q.F q.w 0‖ :=by
    simpa only [sourcePolePrepared_unit,mul_one] using
      (jointResolvent rightMomentum q.F q.w 0).le_opNorm (sourcePolePrepared q.epsilon q.precision rightMomentum right)
  have leftPhase : ‖Complex.exp (Complex.I*(sourceMovingPoleEnergy leftMomentum left:ℂ)*(t:ℂ))‖=1 :=by
    rw [Complex.norm_exp]
    simp
  have rightPhase : ‖Complex.exp ((-Complex.I)*(sourceMovingPoleEnergy rightMomentum right:ℂ)*(t:ℂ))‖=1 :=by
    rw [Complex.norm_exp]
    simp
  exact pairCorrections_price _ _ _ _ _ _ _ _ _ _ _ leftPhase rightPhase dual primal
    (sourcePhysicalDualError_price q leftMomentum left eta t positive future)
    (sourcePhysicalPrimalError_price q rightMomentum right eta t positive future)

theorem sourcePhysicalPrimalError_initial (q : PhysicalResponsePoint) (rightMomentum : PhysicalMomentum)
    (right : RestStateIndex) : sourcePhysicalPrimalError q rightMomentum right 0=0 :=by
  rw [sourcePhysicalPrimalError,sourcePolePrimalCorrection_initial,map_zero]

theorem sourcePhysicalDualError_initial (q : PhysicalResponsePoint) (leftMomentum : PhysicalMomentum)
    (left : RestStateIndex) : sourcePhysicalDualError q leftMomentum left 0=0 :=by
  rw [sourcePhysicalDualError,sourcePoleDualCorrection_initial,ContinuousLinearMap.zero_comp]

theorem sourcePhysicalDensityCorrection_initial (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) : sourcePhysicalDensityCorrection q leftMomentum rightMomentum left right reader 0=0 :=by
  simp only [sourcePhysicalDensityCorrection,sourcePhysicalPrimalError_initial,sourcePhysicalDualError_initial,
    map_zero,zero_apply,mul_zero,add_zero]

end LowEnergy.PreparationVacuumPhysicalPoleLegDynamics
