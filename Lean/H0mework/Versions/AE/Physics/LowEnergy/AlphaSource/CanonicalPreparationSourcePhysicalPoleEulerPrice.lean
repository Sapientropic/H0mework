import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePhysicalPolePreparedReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleHalfResponse
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalFeedback
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumIndependentMomentumReturn
open PreparationVacuumFixedMomentumActionReturn PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalTailPrice
open PreparationVacuumPhysicalCurrentLaplaceReturn SourceFiniteUnitary GaussCoreHilbert
open Filter Set
open scoped BigOperators Topology Matrix InnerProductSpace
attribute [local irreducible] sourcePoleRead sourcePolePrepared sourcePolePreparedDensity jointGenerator jointResolvent
  sourceMovingIndependentReader sourceMatterActionOperator factorialBudget

/-- Original matter-action Euler insertion on the same generated physical material legs. -/
def sourcePoleActionInsertion (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader h : Field289) (t : ℝ) : ℂ:=
  sourcePoleIndependentDual q.epsilon q.precision pL left (sourcePhysicalMaterialPoint q pL pR) h t
    ((fderiv ℝ (sourceMatterActionOperator pR q.F) h reader)
      (sourcePolePreparedPrimal q.epsilon q.precision pR right (sourcePhysicalMaterialPoint q pL pR) h t))

theorem sourcePoleActionInsertion_near (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) (t : ℝ) :
    (fun h=>sourcePoleActionInsertion q pL pR left right reader h t)=ᶠ[𝓝 0]
      (fun h=>sourcePolePreparedDensity q.epsilon q.precision pL pR left right
        (sourcePhysicalMaterialPoint q pL pR) reader h t) :=by
  filter_upwards [sourceMatterActionOperator_gradient_near reader pR q.F,
    sourceMovingIndependentReader_near reader pR q.F] with h action moving
  simp only [sourcePoleActionInsertion,sourcePolePreparedDensity,sourcePhysicalMaterialPoint,action,moving]

def sourcePoleActionEuler (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (h : Field289) (t : ℝ) : Fin 289→ℂ:=
  fun i=> -sourcePoleActionInsertion q pL pR left right (fieldUnit i) h t

theorem sourcePoleActionEuler_source (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (i : Fin 289) :
    sourcePoleActionEuler q pL pR left right 0 t i=
      -sourcePoleRead q.epsilon q.precision pL pR left right
        (fiveKernel (fieldUnit i) pR (pL-pR) q.F q.z q.w t 0) :=by
  have same : sourcePoleActionInsertion q pL pR left right (fieldUnit i) 0 t=
      sourcePolePreparedDensity q.epsilon q.precision pL pR left right
        (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i) 0 t :=
    (sourcePoleActionInsertion_near q pL pR left right (fieldUnit i) t).self_of_nhds
  rw [sourcePoleActionEuler,same,sourcePolePreparedDensity_source]
  rfl

def sourcePoleEulerInitial (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) : Fin 289→ℂ:=sourcePoleActionEuler q pL pR left right 0 0

def sourcePoleEulerCorrection (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : Fin 289→ℂ:=
  fun i=> -sourcePhysicalDensityCorrection q pL pR left right (fieldUnit i) t

theorem sourcePoleActionEuler_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (i : Fin 289) :
    sourcePoleActionEuler q pL pR left right 0 t i=
      Complex.exp (sourcePhysicalClock pL pR left right*(t:ℂ))*sourcePoleEulerInitial q pL pR left right i+
        sourcePoleEulerCorrection q pL pR left right t i :=by
  have actual : sourcePoleActionInsertion q pL pR left right (fieldUnit i) 0 t=
      sourcePolePreparedDensity q.epsilon q.precision pL pR left right
        (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i) 0 t :=
    (sourcePoleActionInsertion_near q pL pR left right (fieldUnit i) t).self_of_nhds
  have initial : sourcePoleActionInsertion q pL pR left right (fieldUnit i) 0 0=
      sourcePolePreparedDensity q.epsilon q.precision pL pR left right
        (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i) 0 0 :=
    (sourcePoleActionInsertion_near q pL pR left right (fieldUnit i) 0).self_of_nhds
  simp only [sourcePoleActionEuler,sourcePoleEulerInitial,sourcePoleEulerCorrection,actual,initial]
  rw [sourcePhysicalDensity_generated]
  ring

attribute [local irreducible] sourcePoleActionEuler sourcePoleEulerInitial sourcePoleEulerCorrection

set_option backward.isDefEq.respectTransparency true in
theorem sourcePoleActionEuler_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (i : Fin 289) :
    Continuous (fun t=>sourcePoleActionEuler q pL pR left right 0 t i) :=by
  have kernel : Continuous (fun t=>fiveKernel (fieldUnit i) pR (pL-pR) q.F q.z q.w t 0) :=by
    have paid:=(rawKernelJets_continuous (fieldUnit i) pR (pL-pR) q.F q.z q.w 0).1
    have same : (fun t=>(rawKernelJet (fieldUnit i) pR (pL-pR) q.F q.z q.w 0 t).value)=
        (fun t=>fiveKernel (fieldUnit i) pR (pL-pR) q.F q.z q.w t 0) :=by
      funext t
      exact rawKernelJet_value (fieldUnit i) pR (pL-pR) q.F q.z q.w 0 t
    exact (congrArg (fun f : ℝ→(H→L[ℂ] H)=>Continuous f) same).mp paid
  have same : (fun t=>sourcePoleActionEuler q pL pR left right 0 t i)=
      (fun t=> -sourcePoleRead q.epsilon q.precision pL pR left right
        (fiveKernel (fieldUnit i) pR (pL-pR) q.F q.z q.w t 0)) :=by
    funext t
    exact sourcePoleActionEuler_source q pL pR left right t i
  have paid : Continuous (fun t=> -sourcePoleRead q.epsilon q.precision pL pR left right
      (fiveKernel (fieldUnit i) pR (pL-pR) q.F q.z q.w t 0)):=
    ((sourcePoleRead q.epsilon q.precision pL pR left right).continuous.comp kernel).neg
  exact (congrArg (fun f : ℝ→ℂ=>Continuous f) same).mpr paid

theorem sourcePoleEulerCorrection_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (i : Fin 289) :
    Continuous (fun t=>sourcePoleEulerCorrection q pL pR left right t i) :=by
  have phase : Continuous (fun t : ℝ=>Complex.exp (sourcePhysicalClock pL pR left right*(t:ℂ))*
      sourcePoleEulerInitial q pL pR left right i) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul continuous_const
  have same : (fun t=>sourcePoleEulerCorrection q pL pR left right t i)=
      (fun t=>sourcePoleActionEuler q pL pR left right 0 t i-
        Complex.exp (sourcePhysicalClock pL pR left right*(t:ℂ))*sourcePoleEulerInitial q pL pR left right i) :=by
    funext t
    rw [sourcePoleActionEuler_generated]
    ring
  rw [same]
  exact (sourcePoleActionEuler_continuous q pL pR left right i).sub phase

def sourcePolePrimalCoefficient (q : PhysicalResponsePoint) (pR : PhysicalMomentum)
    (right : RestStateIndex) (eta : ℝ) : ℝ:=
  ‖jointResolvent pR q.F q.w 0‖*factorialBudget pR q.F eta*
    ‖sourcePoleColumnDefect q.epsilon q.precision pR right q.F‖

def sourcePoleDualCoefficient (q : PhysicalResponsePoint) (pL : PhysicalMomentum)
    (left : RestStateIndex) (eta : ℝ) : ℝ:=
  factorialBudget pL q.F eta*‖sourcePoleDualDefect q.epsilon q.precision pL left q.F‖*
    ‖jointResolvent pL q.F q.z 0‖

def sourcePoleCorrectionCoefficient (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (eta : ℝ) (i : Fin 289) : ℝ:=
  ‖sourceMovingIndependentReader (fieldUnit i) pR q.F 0‖*
    (‖jointResolvent pL q.F q.z 0‖*sourcePolePrimalCoefficient q pR right eta/eta+
      ‖jointResolvent pR q.F q.w 0‖*sourcePoleDualCoefficient q pL left eta/eta+
      sourcePoleDualCoefficient q pL left eta*sourcePolePrimalCoefficient q pR right eta/eta^2)

theorem sourcePoleCorrectionCoefficient_nonnegative (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (eta : ℝ) (positive : 0 < eta) (i : Fin 289) :
    0 ≤ sourcePoleCorrectionCoefficient q pL pR left right eta i :=by
  have l:=factorialBudget_nonnegative pL q.F eta positive
  have r:=factorialBudget_nonnegative pR q.F eta positive
  unfold sourcePoleCorrectionCoefficient sourcePolePrimalCoefficient sourcePoleDualCoefficient
  positivity

private theorem polynomialPrice (L R D P J eta t : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hJ : 0 ≤ J) (positive : 0 < eta) (future : 0 ≤ t) :
    J*(L*(t*P*Real.exp (eta*t))+R*(t*D*Real.exp (eta*t))+
      (t*D*Real.exp (eta*t))*(t*P*Real.exp (eta*t))) ≤
      J*(L*P/eta+R*D/eta+D*P/eta^2)*Real.exp (4*eta*t) :=by
  have tprice : t ≤ Real.exp (eta*t)/eta :=by
    apply (le_div_iff₀ positive).mpr
    have original:=Real.add_one_le_exp (eta*t)
    nlinarith
  have texp : t*Real.exp (eta*t) ≤ Real.exp (2*eta*t)/eta :=by
    have paid:=mul_le_mul_of_nonneg_right tprice (Real.exp_pos (eta*t)).le
    convert! paid using 1
    rw [div_mul_eq_mul_div,←Real.exp_add]
    congr 2
    ring
  have expbound : Real.exp (2*eta*t) ≤ Real.exp (4*eta*t):=Real.exp_le_exp.mpr (by nlinarith)
  have primal : t*P*Real.exp (eta*t) ≤ P/eta*Real.exp (2*eta*t) :=by
    convert! mul_le_mul_of_nonneg_left texp hP using 1  <;>ring
  have dual : t*D*Real.exp (eta*t) ≤ D/eta*Real.exp (2*eta*t) :=by
    convert! mul_le_mul_of_nonneg_left texp hD using 1  <;>ring
  have first :=(mul_le_mul_of_nonneg_left primal hL).trans
    (by convert! mul_le_mul_of_nonneg_left expbound (show 0 ≤ L*(P/eta) by positivity) using 1;ring)
  have second :=(mul_le_mul_of_nonneg_left dual hR).trans
    (by convert! mul_le_mul_of_nonneg_left expbound (show 0 ≤ R*(D/eta) by positivity) using 1;ring)
  have third:=mul_le_mul dual primal (by positivity) (by positivity)
  have exponent : Real.exp (2*eta*t)*Real.exp (2*eta*t)=Real.exp (4*eta*t) :=by
    rw [←Real.exp_add]
    congr 1
    ring
  have product : (t*D*Real.exp (eta*t))*(t*P*Real.exp (eta*t)) ≤ D*P/eta^2*Real.exp (4*eta*t) :=by
    refine third.trans_eq ?_
    calc
      _=(D*P/eta^2)*(Real.exp (2*eta*t)*Real.exp (2*eta*t)) :=by ring
      _=_ :=by rw [exponent]
  have sum:=add_le_add (add_le_add first second) product
  convert! mul_le_mul_of_nonneg_left sum hJ using 1;ring

theorem sourcePoleEulerCorrection_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (eta t : ℝ) (positive : 0 < eta) (future : 0 ≤ t) (i : Fin 289) :
    ‖sourcePoleEulerCorrection q pL pR left right t i‖ ≤
      sourcePoleCorrectionCoefficient q pL pR left right eta i*Real.exp (4*eta*t) :=by
  have l:=factorialBudget_nonnegative pL q.F eta positive
  have r:=factorialBudget_nonnegative pR q.F eta positive
  have paid:=sourcePhysicalDensityCorrection_price q pL pR left right (fieldUnit i) eta t positive future
  rw [sourcePoleEulerCorrection,norm_neg]
  refine paid.trans ?_
  convert! polynomialPrice ‖jointResolvent pL q.F q.z 0‖ ‖jointResolvent pR q.F q.w 0‖
    (sourcePoleDualCoefficient q pL left eta) (sourcePolePrimalCoefficient q pR right eta)
    ‖sourceMovingIndependentReader (fieldUnit i) pR q.F 0‖ eta t
    (norm_nonneg _) (norm_nonneg _) (by unfold sourcePoleDualCoefficient;positivity)
    (by unfold sourcePolePrimalCoefficient;positivity) (norm_nonneg _) positive future using 1
  dsimp only [sourcePhysicalDensityPrice,sourcePhysicalPrimalPrice,sourcePhysicalDualPrice,
        sourcePoleCorrectionCoefficient,sourcePolePrimalCoefficient,sourcePoleDualCoefficient]
  ring

end LowEnergy.PreparationVacuumPhysicalPoleHalfResponse
