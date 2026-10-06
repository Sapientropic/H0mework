import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalRawActionDensity

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalDensity
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumFieldPerturbation
open PreparationVacuumSourceActionJets
open PreparationVacuumGaugeSourceInjection
open CanonicalPreparationCore.Completed GaussComposite.SourceGraph
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
abbrev Operator:=H→L[ℂ] H
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent jointCurrent rawReader rawReaderContact

/-- The source dual is composed with inverse time, without an adjoint hypothesis. -/
def independentDual (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) : H→L[ℂ] ℂ:=
  (innerSL ℂ (responseLeft q)).comp (physicalTime (q.p+q.k) q.F (-age) h)

theorem independentDual_inverse (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) (v : H) :
    independentDual q h age (physicalTime (q.p+q.k) q.F age h v)=inner ℂ (responseLeft q) v :=by
  change inner ℂ (responseLeft q)
    ((physicalTime (q.p+q.k) q.F (-age) h*physicalTime (q.p+q.k) q.F age h) v)=_
  rw [(physicalTime_inverse (q.p+q.k) q.F age h).1]
  rfl

theorem independentDual_initial (q : PhysicalResponsePoint) (h : Field289) :
    independentDual q h 0=innerSL ℂ (responseLeft q) :=by
  simp only [independentDual,neg_zero,physicalTime_initial]
  rfl

theorem independentDual_time (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) :
    HasDerivAt (independentDual q h)
      ((innerSL ℂ (responseLeft q)).comp
        (physicalTime (q.p+q.k) q.F (-age) h*((Complex.I) • jointGenerator (q.p+q.k) q.F 0 h))) age :=by
  have time:=(timeJets_generated (jointGenerator (q.p+q.k) q.F 0 h) (-1) 0 age).1
  let L:=(ContinuousLinearMap.compL ℂ H H ℂ (innerSL ℂ (responseLeft q))).restrictScalars ℝ
  have generated:=L.hasFDerivAt.comp_hasDerivAt age time
  have factor (C T : Operator) : (-1:ℝ) • (T*((-Complex.I) • C))=T*((Complex.I) • C):=by
    ext v
    simp
  convert! generated using 1
  all_goals simp only [L,independentDual,ContinuousLinearMap.restrictScalars,ContinuousLinearMap.compL_apply,
    Function.comp_apply,timeJet,physicalTime,neg_one_mul,add_zero,factor]
  all_goals rfl

def preparedDual (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) : H→L[ℂ] ℂ:=
  (independentDual q h age).comp (jointResolvent (q.p+q.k) q.F q.z h)

def preparedPrimal (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) : H:=
  jointResolvent q.p q.F q.w h (physicalTime q.p q.F age h (responseRight q))

def densityRead (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  preparedDual q h age (rawReader reader q.p q.F h (preparedPrimal q h age))

theorem densityRead_actual (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) :
    densityRead q reader h age=
      rawPrepared q.epsilon q.precision reader q.p q.k q.F q.z q.w age
        q.left q.right q.lc q.ls q.rc q.rs h :=by
  simp only [densityRead,preparedDual,independentDual,preparedPrimal,rawPrepared,fiveKernel,
    responseLeft,responseRight,ContinuousLinearMap.comp_apply,mul_apply_eq_comp]
  rfl

def dualSlope (q : PhysicalResponsePoint) (force : Field289) (age : ℝ) : H→L[ℂ] ℂ:=
  (innerSL ℂ (responseLeft q)).comp
    (timeSlope force (q.p+q.k) q.F (-age)*jointResolvent (q.p+q.k) q.F q.z 0+
      physicalTime (q.p+q.k) q.F (-age) 0*
        (-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 force*
          jointResolvent (q.p+q.k) q.F q.z 0)))

def primalSlope (q : PhysicalResponsePoint) (force : Field289) (age : ℝ) : H:=
  (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0))
    (physicalTime q.p q.F age 0 (responseRight q))+
  jointResolvent q.p q.F q.w 0 (timeSlope force q.p q.F age (responseRight q))

theorem dualSlope_generated (q : PhysicalResponsePoint) (force : Field289) (age : ℝ) (hz : q.z.im≠0) :
    HasDerivAt (fun r : ℝ=>preparedDual q (r • force) age) (dualSlope q force age) 0 :=by
  have time:=physicalTime_direction force (q.p+q.k) q.F (-age)
  have inverse:=inverse_direction (q.p+q.k) q.F q.z hz force
  have product:=time.mul inverse
  let L:=(ContinuousLinearMap.compL ℂ H H ℂ (innerSL ℂ (responseLeft q))).restrictScalars ℝ
  have generated:=L.hasFDerivAt.comp_hasDerivAt 0 product
  convert! generated using 1
  all_goals simp only [preparedDual,independentDual,dualSlope,L,ContinuousLinearMap.restrictScalars,
    ContinuousLinearMap.compL_apply,Function.comp_apply,zero_smul]
  all_goals rfl

theorem primalSlope_generated (q : PhysicalResponsePoint) (force : Field289) (age : ℝ) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>preparedPrimal q (r • force) age) (primalSlope q force age) 0 :=by
  have inverse:=inverse_direction q.p q.F q.w hw force
  have time:=physicalTime_direction force q.p q.F age
  let P:=(ContinuousLinearMap.apply ℂ H (responseRight q)).restrictScalars ℝ
  have generated:=P.hasFDerivAt.comp_hasDerivAt 0 (inverse.mul time)
  convert! generated using 1
  all_goals simp only [P,preparedPrimal,primalSlope,Function.comp_apply,ContinuousLinearMap.restrictScalars,
    ContinuousLinearMap.apply_apply,add_apply,mul_apply_eq_comp,zero_smul]
  all_goals rfl

def densitySlope (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ) : ℂ:=
  dualSlope q force age (rawReader reader q.p q.F 0 (preparedPrimal q 0 age))+
    preparedDual q 0 age (rawReaderContact reader force q.p q.F (preparedPrimal q 0 age))+
    preparedDual q 0 age (rawReader reader q.p q.F 0 (primalSlope q force age))

theorem densitySlope_actual (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ) :
    densitySlope q reader force age=
      rawPreparedSlope q.epsilon q.precision reader force q.p q.k q.F q.z q.w age
        q.left q.right q.lc q.ls q.rc q.rs :=by
  simp only [densitySlope,dualSlope,preparedDual,independentDual,preparedPrimal,primalSlope,
    rawPreparedSlope,fiveDerivative,responseLeft,responseRight,ContinuousLinearMap.comp_apply,
    add_apply,mul_apply_eq_comp,map_add,inner_add_right,innerSL_apply_apply]
  abel

theorem densityRead_generated (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>densityRead q reader (r • force) age)
      (densitySlope q reader force age) 0 :=by
  have actual:=rawPrepared_generated q.epsilon q.precision reader force q.p q.k q.F q.z q.w hz hw age
    q.left q.right q.lc q.ls q.rc q.rs
  simpa only [densityRead_actual,densitySlope_actual] using actual

end LowEnergy.PreparationVacuumOriginalDensity
