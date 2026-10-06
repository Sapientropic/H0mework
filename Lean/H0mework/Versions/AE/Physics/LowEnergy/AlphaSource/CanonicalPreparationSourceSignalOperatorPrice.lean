import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceOrderedSignalOperator

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentSignalOperator
open CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalTailPrice
open PreparationVacuumCurrentSignalRealization PreparationVacuumGaugeSourceInjection
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart
open PreparationVacuumPropagationPencil
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime SourcePropagationMotherEulerKernel
open SourceFiniteUnitary PreparationVacuumFieldPerturbation
open Filter Set MeasureTheory
open scoped Topology BigOperators ContDiff Interval
local instance : NormedAlgebra ℝ SourceOp:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointCurrent jointResolvent rawReader noetherReader
  physicalTime sourceRead rawInitial factorialBudget

def sourceClockGrowth (p : Fin 4→ℂ) : ℝ:=max 0 (p 0).re

theorem sourceClockGrowth_nonnegative (p : Fin 4→ℂ) : 0 ≤ sourceClockGrowth p :=le_max_left _ _

theorem sourceHistoryInput_price (p : Fin 4→ℂ) (t : ℝ) (future : 0 ≤ t) :
    ‖sourceHistoryInput p t‖ ≤ Real.exp (sourceClockGrowth p*t) :=by
  apply (sourceHistoryInput p t).opNorm_le_bound (Real.exp_pos _).le
  intro a
  rw [sourceHistoryInput_actual,sourceTimeHistory_actual]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg a))).mpr
  intro i
  refine (Complex.abs_re_le_norm _).trans ((norm_mul _ _).le.trans ?_)
  rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_le_mul (Real.exp_le_exp.mpr (by
    rw [mul_comm t]
    exact mul_le_mul_of_nonneg_right (le_max_right 0 (p 0).re) future))
    (norm_le_pi_norm a i) (norm_nonneg _) (Real.exp_pos _).le

private theorem compose_envelope {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F→L[ℝ] G) (B : E→L[ℝ] F) (a b x y t : ℝ)
    (hA : ‖A‖ ≤ a*Real.exp (x*t)) (hB : ‖B‖ ≤ b*Real.exp (y*t)) :
    ‖A.comp B‖ ≤ a*b*Real.exp ((x+y)*t) :=by
  refine (ContinuousLinearMap.opNorm_comp_le A B).trans
    ((mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA)).trans_eq ?_)
  rw [add_mul,Real.exp_add]
  ring

private theorem sandwich_envelope (A B : SourceOp) (a b x y t : ℝ)
    (hA : ‖A‖ ≤ a*Real.exp (x*t)) (hB : ‖B‖ ≤ b*Real.exp (y*t)) :
    ‖ContinuousLinearMap.mulLeftRight ℝ SourceOp A B‖ ≤ a*b*Real.exp ((x+y)*t) :=by
  refine (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ SourceOp A B).trans
    ((mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA)).trans_eq ?_)
  rw [add_mul,Real.exp_add]
  ring

private theorem actual_forward (momentum : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (eta t : ℝ) (positive : 0<eta) (future : 0 ≤ t) :
    ‖time (jointGenerator momentum F 0 0) t‖ ≤ factorialBudget momentum F eta*Real.exp (eta*t) :=by
  simpa only [physicalTime] using actualTime_future momentum F eta t positive future

private theorem actual_reverse (momentum : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (eta t : ℝ) (positive : 0<eta) (future : 0 ≤ t) :
    ‖time (jointGenerator momentum F 0 0) (-t)‖ ≤ factorialBudget momentum F eta*Real.exp (eta*t) :=by
  simpa only [physicalTime] using actualTime_past momentum F eta t positive future

private theorem imaginary_norm {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ G] (C : E→L[ℝ] G) : ‖(-Complex.I) • C‖ ≤ ‖C‖ :=by
  apply (((-Complex.I) • C)).opNorm_le_bound (norm_nonneg C)
  intro x
  rw [smul_apply,norm_smul]
  simpa only [norm_neg,Complex.norm_I,one_mul] using C.le_opNorm x

private theorem operator_neg_norm {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (C : E→L[ℝ] G) : ‖-C‖=‖C‖ :=by
  apply le_antisymm
  · apply (-C).opNorm_le_bound (norm_nonneg C)
    intro x
    simpa only [neg_apply,norm_neg] using C.le_opNorm x
  · apply C.opNorm_le_bound (norm_nonneg (-C))
    intro x
    simpa only [neg_apply,norm_neg] using (-C).le_opNorm x

def sourcePrimalCoefficient (q : PhysicalResponsePoint) (eta : ℝ) : ℝ:=
  factorialBudget q.p q.F eta^3*‖jointCurrent q.p q.F 0 0‖

def sourceDualCoefficient (q : PhysicalResponsePoint) (eta : ℝ) : ℝ:=
  factorialBudget (q.p+q.k) q.F eta^3*‖jointCurrent (q.p+q.k) q.F 0 0‖

private theorem source_drive_price (momentum : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (p : Fin 4→ℂ) (eta t : ℝ) (positive : 0<eta) (future : 0 ≤ t) :
    ‖(ContinuousLinearMap.mulLeftRight ℝ SourceOp
      (time (jointGenerator momentum F 0 0) (-t)) (time (jointGenerator momentum F 0 0) t)).comp
        (((-Complex.I) • jointCurrent momentum F 0 0).comp (sourceHistoryInput p t))‖ ≤
      factorialBudget momentum F eta^2*‖jointCurrent momentum F 0 0‖*
        Real.exp ((2*eta+sourceClockGrowth p)*t) :=by
  have current : ‖(-Complex.I) • jointCurrent momentum F 0 0‖ ≤
    ‖jointCurrent momentum F 0 0‖*Real.exp (0*t) :=by
    simpa only [zero_mul,Real.exp_zero,mul_one] using imaginary_norm (jointCurrent momentum F 0 0)
  have input := sourceHistoryInput_price p t future
  have transport:=sandwich_envelope _ _ _ _ _ _ t
    (actual_reverse momentum F eta t positive future) (actual_forward momentum F eta t positive future)
  have field : ‖sourceHistoryInput p t‖ ≤ 1*Real.exp (sourceClockGrowth p*t):=by simpa only [one_mul] using input
  have generated:=compose_envelope _ _ _ _ _ _ t transport
    (compose_envelope _ _ _ _ _ _ t current field)
  convert! generated using 1
  simp only [zero_add,mul_one]
  congr 2 <;> ring

theorem sourceRightDrive_price (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (eta t : ℝ)
    (positive : 0<eta) (future : 0 ≤ t) :
    ‖sourceRightDrive q p t‖ ≤ factorialBudget q.p q.F eta^2*‖jointCurrent q.p q.F 0 0‖*
      Real.exp ((2*eta+sourceClockGrowth p)*t) :=
  source_drive_price q.p q.F p eta t positive future

theorem sourceLeftDrive_price (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (eta t : ℝ)
    (positive : 0<eta) (future : 0 ≤ t) :
    ‖sourceLeftDrive q p t‖ ≤ factorialBudget (q.p+q.k) q.F eta^2*‖jointCurrent (q.p+q.k) q.F 0 0‖*
      Real.exp ((2*eta+sourceClockGrowth p)*t) :=by
  have same : sourceLeftDrive q p t=-(sourceRightDrive {q with p:=q.p+q.k} p t) :=by
    simp only [sourceLeftDrive,sourceRightDrive,ContinuousLinearMap.comp_neg,ContinuousLinearMap.neg_comp]
  calc
    ‖sourceLeftDrive q p t‖=‖-(sourceRightDrive {q with p:=q.p+q.k} p t)‖:=congrArg norm same
    _=‖sourceRightDrive {q with p:=q.p+q.k} p t‖:=operator_neg_norm _
    _ ≤ _:=source_drive_price (q.p+q.k) q.F p eta t positive future

private theorem integral_envelope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ→E) (C x t : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x) (ht : 0 ≤ t)
    (paid : ∀s,0 ≤ s→‖f s‖ ≤ C*Real.exp (x*s)) :
    ‖∫s in (0 : ℝ)..t,f s‖ ≤ (C*t)*Real.exp (x*t) :=by
  have bound : ∀s∈uIoc (0 : ℝ) t,‖f s‖ ≤ C*Real.exp (x*t) :=by
    rw [uIoc_of_le ht]
    intro s hs
    exact (paid s hs.1.le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hx)) hC)
  have source:=intervalIntegral.norm_integral_le_of_norm_le_const bound
  simpa only [sub_zero,abs_of_nonneg ht,mul_assoc,mul_comm (Real.exp (x*t)) t] using source

private theorem primal_normalization (B J eta g t : ℝ) :
    (B*1)*(B^2*J*t)*Real.exp ((eta+0+(2*eta+g))*t)=
      (B^3*J)*t*Real.exp ((3*eta+g)*t) :=by
  have exponent : eta+0+(2*eta+g)=3*eta+g:=by ring
  rw [exponent]
  ring

private theorem dual_normalization (B J eta g t : ℝ) :
    (1*B)*(B^2*J*t)*Real.exp ((0+eta+(2*eta+g))*t)=
      (B^3*J)*t*Real.exp ((3*eta+g)*t) :=by
  have exponent : 0+eta+(2*eta+g)=3*eta+g:=by ring
  rw [exponent]
  ring

private theorem exponent_normalization (C left right t : ℝ) (same : left=right) :
    C*Real.exp (left*t)=C*Real.exp (right*t) :=by
  rw [same]

theorem sourcePrimalOperator_price (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (eta t : ℝ)
    (positive : 0<eta) (future : 0 ≤ t) :
    ‖sourcePrimalOperator q p t‖ ≤ sourcePrimalCoefficient q eta*t*
      Real.exp ((3*eta+sourceClockGrowth p)*t) :=by
  have budget:=factorialBudget_nonnegative q.p q.F eta positive
  have primitive:=integral_envelope (sourceRightDrive q p) _ _ t (by positivity)
    (by have h:=sourceClockGrowth_nonnegative p;positivity) future
    (fun s hs=>sourceRightDrive_price q p eta s positive hs)
  have one : ‖(1 : SourceOp)‖ ≤ 1 :=by
    change ‖(ContinuousLinearMap.id ℂ _ : SourceOp)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have oneBound : ‖(1 : SourceOp)‖ ≤ 1*Real.exp (0*t):=by
    simpa only [zero_mul,Real.exp_zero,mul_one] using one
  have transport:=sandwich_envelope _ _ _ _ _ _ t
    (actual_forward q.p q.F eta t positive future) oneBound
  have actual:=compose_envelope (E:=SignalAmplitude) (F:=SourceOp) (G:=SourceOp)
    (ContinuousLinearMap.mulLeftRight ℝ SourceOp (time (jointGenerator q.p q.F 0 0) t) 1)
    (∫s in (0 : ℝ)..t,sourceRightDrive q p s)
    (factorialBudget q.p q.F eta*1)
    (factorialBudget q.p q.F eta^2*‖jointCurrent q.p q.F 0 0‖*t)
    (eta+0) (2*eta+sourceClockGrowth p) t transport primitive
  exact actual.trans_eq (primal_normalization _ _ eta (sourceClockGrowth p) t)

theorem sourceIndependentDualOperator_price (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (eta t : ℝ)
    (positive : 0<eta) (future : 0 ≤ t) :
    ‖sourceIndependentDualOperator q p t‖ ≤ sourceDualCoefficient q eta*t*
      Real.exp ((3*eta+sourceClockGrowth p)*t) :=by
  have budget:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
  have primitive:=integral_envelope (sourceLeftDrive q p) _ _ t (by positivity)
    (by have h:=sourceClockGrowth_nonnegative p;positivity) future
    (fun s hs=>sourceLeftDrive_price q p eta s positive hs)
  have one : ‖(1 : SourceOp)‖ ≤ 1 :=by
    change ‖(ContinuousLinearMap.id ℂ _ : SourceOp)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have oneBound : ‖(1 : SourceOp)‖ ≤ 1*Real.exp (0*t):=by
    simpa only [zero_mul,Real.exp_zero,mul_one] using one
  have transport:=sandwich_envelope _ _ _ _ _ _ t
    oneBound (actual_reverse (q.p+q.k) q.F eta t positive future)
  have actual:=compose_envelope (E:=SignalAmplitude) (F:=SourceOp) (G:=SourceOp)
    (ContinuousLinearMap.mulLeftRight ℝ SourceOp 1 (time (jointGenerator (q.p+q.k) q.F 0 0) (-t)))
    (∫s in (0 : ℝ)..t,sourceLeftDrive q p s)
    (1*factorialBudget (q.p+q.k) q.F eta)
    (factorialBudget (q.p+q.k) q.F eta^2*‖jointCurrent (q.p+q.k) q.F 0 0‖*t)
    (0+eta) (2*eta+sourceClockGrowth p) t transport primitive
  exact actual.trans_eq (dual_normalization _ _ eta (sourceClockGrowth p) t)

def sourceMaterialMap (q : PhysicalResponsePoint) (reader : Field289) : Field289→L[ℝ] SourceOp:=
  let L:=jointResolvent (q.p+q.k) q.F q.z 0
  let R:=jointResolvent q.p q.F q.w 0
  let J:=rawReader reader q.p q.F 0
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp (-L) (L*J*R)).comp (jointCurrent (q.p+q.k) q.F q.z 0)+
    (ContinuousLinearMap.mulLeftRight ℝ SourceOp (L*J*R) (-R)).comp (jointCurrent q.p q.F q.w 0)

def sourceContactMap (q : PhysicalResponsePoint) (reader : Field289) : Field289→L[ℝ] SourceOp:=
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp (jointResolvent (q.p+q.k) q.F q.z 0)
    (jointResolvent q.p q.F q.w 0)).comp (fderiv ℝ (noetherReader reader q.p q.F) 0)

theorem sourceMiddleOperator_source_maps (q : PhysicalResponsePoint) (reader : Field289)
    (p : Fin 4→ℂ) (t : ℝ) :
    sourceMiddleOperator q reader p t=(sourceMaterialMap q reader).comp (sourceHistoryInput p 0)+
      (sourceContactMap q reader).comp (sourceHistoryInput p t) :=by
  simp only [sourceMiddleOperator,sourceMaterialMap,sourceContactMap,ContinuousLinearMap.add_comp]
  abel

def sourceMiddleCoefficient (q : PhysicalResponsePoint) (reader : Field289) : ℝ:=
  ‖sourceMaterialMap q reader‖+‖sourceContactMap q reader‖

theorem sourceMiddleOperator_price (q : PhysicalResponsePoint) (reader : Field289)
    (p : Fin 4→ℂ) (t : ℝ) (future : 0 ≤ t) :
    ‖sourceMiddleOperator q reader p t‖ ≤ sourceMiddleCoefficient q reader*Real.exp (sourceClockGrowth p*t) :=by
  have initial : ‖sourceHistoryInput p 0‖ ≤ 1:=by
    simpa only [mul_zero,Real.exp_zero] using sourceHistoryInput_price p 0 le_rfl
  have material : ‖(sourceMaterialMap q reader).comp (sourceHistoryInput p 0)‖ ≤
      ‖sourceMaterialMap q reader‖:=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left initial (norm_nonneg _)).trans_eq (mul_one _))
  have materialGrowth : ‖(sourceMaterialMap q reader).comp (sourceHistoryInput p 0)‖ ≤
      ‖sourceMaterialMap q reader‖*Real.exp (sourceClockGrowth p*t):=
    material.trans (le_mul_of_one_le_right (sourceMaterialMap q reader).opNorm_nonneg
      (Real.one_le_exp (mul_nonneg (sourceClockGrowth_nonnegative p) future)))
  have contact : ‖(sourceContactMap q reader).comp (sourceHistoryInput p t)‖ ≤
      ‖sourceContactMap q reader‖*Real.exp (sourceClockGrowth p*t):=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (sourceHistoryInput_price p t future) (norm_nonneg _))
  rw [sourceMiddleOperator_source_maps]
  refine (ContinuousLinearMap.opNorm_add_le _ _).trans ((add_le_add materialGrowth contact).trans_eq ?_)
  change ‖sourceMaterialMap q reader‖*Real.exp (sourceClockGrowth p*t)+
    ‖sourceContactMap q reader‖*Real.exp (sourceClockGrowth p*t)=
      (‖sourceMaterialMap q reader‖+‖sourceContactMap q reader‖)*Real.exp (sourceClockGrowth p*t)
  exact (add_mul _ _ _).symm

def sourceHistoryLinearCoefficient (q : PhysicalResponsePoint) (reader : Field289) (eta : ℝ) : ℝ:=
  ‖rawInitial q reader‖*(factorialBudget q.p q.F eta*sourceDualCoefficient q eta+
    factorialBudget (q.p+q.k) q.F eta*sourcePrimalCoefficient q eta)

def sourceHistoryConstantCoefficient (q : PhysicalResponsePoint) (reader : Field289) (eta : ℝ) : ℝ:=
  factorialBudget (q.p+q.k) q.F eta*factorialBudget q.p q.F eta*sourceMiddleCoefficient q reader

private theorem norm_one_source : ‖(1 : SourceOp)‖ ≤ 1 :=by
  change ‖(ContinuousLinearMap.id ℂ _ : SourceOp)‖ ≤ 1
  exact ContinuousLinearMap.norm_id_le

theorem sourceHistoryOperator_price (q : PhysicalResponsePoint) (reader : Field289)
    (p : Fin 4→ℂ) (eta t : ℝ) (positive : 0<eta) (future : 0 ≤ t) :
    ‖sourceHistoryOperator q reader p t‖ ≤
      (sourceHistoryLinearCoefficient q reader eta*t+sourceHistoryConstantCoefficient q reader eta)*
        Real.exp ((4*eta+sourceClockGrowth p)*t) :=by
  have left:=actualTime_past (q.p+q.k) q.F eta t positive future
  have right:=actualTime_future q.p q.F eta t positive future
  have oneBound : ‖(1 : SourceOp)‖ ≤ 1*Real.exp (0*t):=by
    simpa only [zero_mul,Real.exp_zero,mul_one] using norm_one_source
  have leftProduct : ‖physicalTime (q.p+q.k) q.F (-t) 0*rawInitial q reader‖ ≤
      factorialBudget (q.p+q.k) q.F eta*‖rawInitial q reader‖*Real.exp (eta*t) :=by
    have source:=(norm_mul_le (physicalTime (q.p+q.k) q.F (-t) 0) (rawInitial q reader)).trans
      (mul_le_mul_of_nonneg_right left (norm_nonneg (rawInitial q reader)))
    simpa only [mul_assoc,mul_comm (Real.exp (eta*t)) ‖rawInitial q reader‖] using source
  have primal := compose_envelope _ _ _ _ _ _ t
    (sandwich_envelope _ _ _ _ _ _ t leftProduct oneBound)
    (sourcePrimalOperator_price q p eta t positive future)
  have rightInitial : ‖rawInitial q reader*physicalTime q.p q.F t 0‖ ≤
      ‖rawInitial q reader‖*factorialBudget q.p q.F eta*Real.exp (eta*t) :=by
    have source:=(norm_mul_le (rawInitial q reader) (physicalTime q.p q.F t 0)).trans
      (mul_le_mul_of_nonneg_left right (norm_nonneg (rawInitial q reader)))
    simpa only [←mul_assoc] using source
  have dual := compose_envelope _ _ _ _ _ _ t
    (sandwich_envelope _ _ _ _ _ _ t oneBound rightInitial)
    (sourceIndependentDualOperator_price q p eta t positive future)
  have middle := compose_envelope _ _ _ _ _ _ t
    (sandwich_envelope _ _ _ _ _ _ t left right)
    (show ‖sourceMiddleOperator q reader p t‖ ≤ sourceMiddleCoefficient q reader*Real.exp (sourceClockGrowth p*t)
      from sourceMiddleOperator_price q reader p t future)
  have e31 : eta+0+(3*eta+sourceClockGrowth p)=4*eta+sourceClockGrowth p:=by ring
  have e32 : 0+eta+(3*eta+sourceClockGrowth p)=4*eta+sourceClockGrowth p:=by ring
  have primalNormalized:=primal.trans_eq (exponent_normalization _ _ _ t e31)
  have dualNormalized:=dual.trans_eq (exponent_normalization _ _ _ t e32)
  have grow : Real.exp ((eta+eta+sourceClockGrowth p)*t) ≤ Real.exp ((4*eta+sourceClockGrowth p)*t):=
    Real.exp_le_exp.mpr (by nlinarith)
  have budgets : 0 ≤ factorialBudget (q.p+q.k) q.F eta*factorialBudget q.p q.F eta*sourceMiddleCoefficient q reader :=by
    have hL:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
    have hR:=factorialBudget_nonnegative q.p q.F eta positive
    unfold sourceMiddleCoefficient
    positivity
  have middleGrowth := middle.trans (mul_le_mul_of_nonneg_left grow budgets)
  unfold sourceHistoryOperator
  refine (ContinuousLinearMap.opNorm_add_le _ _).trans
    (add_le_add ((ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add dualNormalized middleGrowth)) primalNormalized) |>.trans_eq ?_
  simp only [sourceHistoryLinearCoefficient,sourceHistoryConstantCoefficient,mul_one,one_mul]
  ring

def sourceCurrentLinearCoefficient (q : PhysicalResponsePoint) (eta : ℝ) : ℝ:=
  ‖sourceRead q‖*(∑i : Fin 289,sourceHistoryLinearCoefficient q (fieldUnit i) eta)

def sourceCurrentConstantCoefficient (q : PhysicalResponsePoint) (eta : ℝ) : ℝ:=
  ‖sourceRead q‖*(∑i : Fin 289,sourceHistoryConstantCoefficient q (fieldUnit i) eta)

theorem sourceCurrentCoefficient_nonnegative (q : PhysicalResponsePoint) (eta : ℝ) (positive : 0<eta) :
    0 ≤ sourceCurrentLinearCoefficient q eta ∧ 0 ≤ sourceCurrentConstantCoefficient q eta :=by
  have left:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
  have right:=factorialBudget_nonnegative q.p q.F eta positive
  constructor
  · unfold sourceCurrentLinearCoefficient
    apply mul_nonneg (sourceRead q).opNorm_nonneg
    apply Finset.sum_nonneg
    intro i _
    unfold sourceHistoryLinearCoefficient sourceDualCoefficient sourcePrimalCoefficient
    positivity
  · unfold sourceCurrentConstantCoefficient
    apply mul_nonneg (sourceRead q).opNorm_nonneg
    apply Finset.sum_nonneg
    intro i _
    unfold sourceHistoryConstantCoefficient sourceMiddleCoefficient
    positivity

theorem sourceCurrentOperator_price (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (eta t : ℝ)
    (positive : 0<eta) (future : 0 ≤ t) :
    ‖sourceCurrentOperator q p t‖ ≤
      (sourceCurrentLinearCoefficient q eta*t+sourceCurrentConstantCoefficient q eta)*
        Real.exp ((4*eta+sourceClockGrowth p)*t) :=by
  have left:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
  have right:=factorialBudget_nonnegative q.p q.F eta positive
  have eachNonnegative (i : Fin 289) : 0 ≤ sourceHistoryLinearCoefficient q (fieldUnit i) eta*t+
      sourceHistoryConstantCoefficient q (fieldUnit i) eta :=by
    unfold sourceHistoryLinearCoefficient sourceHistoryConstantCoefficient sourcePrimalCoefficient
      sourceDualCoefficient sourceMiddleCoefficient
    positivity
  unfold sourceCurrentOperator
  apply ContinuousLinearMap.norm_pi_le_of_le
  · intro i
    have individual:=(ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (sourceHistoryOperator_price q (fieldUnit i) p eta t positive future)
        (norm_nonneg (-((sourceRead q).restrictScalars ℝ))))
    have reader : ‖-((sourceRead q).restrictScalars ℝ)‖=‖sourceRead q‖ :=by
      rw [operator_neg_norm,ContinuousLinearMap.norm_restrictScalars]
    rw [reader] at individual
    have single : sourceHistoryLinearCoefficient q (fieldUnit i) eta*t+sourceHistoryConstantCoefficient q (fieldUnit i) eta ≤
        ∑j : Fin 289,(sourceHistoryLinearCoefficient q (fieldUnit j) eta*t+sourceHistoryConstantCoefficient q (fieldUnit j) eta) :=
      Finset.single_le_sum (fun j _=>eachNonnegative j) (Finset.mem_univ i)
    refine individual.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right single (Real.exp_pos _).le) (sourceRead q).opNorm_nonneg).trans_eq ?_)
    simp only [Finset.sum_add_distrib,←Finset.sum_mul,sourceCurrentLinearCoefficient,sourceCurrentConstantCoefficient]
    ring
  · have coefficients:=sourceCurrentCoefficient_nonnegative q eta positive
    exact mul_nonneg (add_nonneg (mul_nonneg coefficients.1 future) coefficients.2) (Real.exp_pos _).le

private theorem amplitude_reconstruction (a : SignalAmplitude) :
    a=(∑i : Fin 289,(a i).re • Pi.single i (1 : ℂ))+
      ∑i : Fin 289,(a i).im • (Complex.I • Pi.single i (1 : ℂ)) :=by
  funext j
  simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,
    smul_eq_mul,Complex.real_smul]
  simp only [mul_ite,mul_zero,mul_one,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact (Complex.re_add_im (a j)).symm

private theorem current_basis (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) :
    sourceCurrentOperator q p t=
      (∑i : Fin 289,(Complex.reCLM.comp (ContinuousLinearMap.proj i : SignalAmplitude→L[ℝ] ℂ)).smulRight
        (sourceCurrentOperator q p t (Pi.single i 1)))+
      ∑i : Fin 289,(Complex.imCLM.comp (ContinuousLinearMap.proj i : SignalAmplitude→L[ℝ] ℂ)).smulRight
        (sourceCurrentOperator q p t (Complex.I • Pi.single i 1)) :=by
  ext a j
  have generated:=congrArg (sourceCurrentOperator q p t) (amplitude_reconstruction a)
  simpa only [map_add,map_sum,map_smul,add_apply,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    Pi.add_apply,Pi.smul_apply,Finset.sum_apply] using congrFun generated j

theorem sourceCurrentOperator_continuous (q : PhysicalResponsePoint) (p : Fin 4→ℂ) :
    Continuous (sourceCurrentOperator q p) :=by
  have each (a : SignalAmplitude) : Continuous (fun t=>sourceCurrentOperator q p t a) :=by
    apply continuous_pi
    intro j
    have actual : (fun t=>sourceCurrentOperator q p t a j)=
        fun t=>(noetherHistorySourceJet q (nativeTimeSignal (sourceRealSignal p a)) t j).value :=by
      funext t
      exact congrFun (sourceCurrentOperator_actual q p t a) j
    rw [actual]
    exact (noetherHistorySourceJet_continuous q _ (sourceTimeSignal_continuous p a) j).1
  have first : Continuous (fun t=>∑i : Fin 289,
      (Complex.reCLM.comp (ContinuousLinearMap.proj i : SignalAmplitude→L[ℝ] ℂ)).smulRight
        (sourceCurrentOperator q p t (Pi.single i 1))) :=by
    apply continuous_finsetSum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ SignalAmplitude (Fin 289→ℂ)
      (Complex.reCLM.comp (ContinuousLinearMap.proj i))).continuous.comp (each _)
  have second : Continuous (fun t=>∑i : Fin 289,
      (Complex.imCLM.comp (ContinuousLinearMap.proj i : SignalAmplitude→L[ℝ] ℂ)).smulRight
        (sourceCurrentOperator q p t (Complex.I • Pi.single i 1))) :=by
    apply continuous_finsetSum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ SignalAmplitude (Fin 289→ℂ)
      (Complex.imCLM.comp (ContinuousLinearMap.proj i))).continuous.comp (each _)
  exact (first.add second).congr (fun t=>(current_basis q p t).symm)

end LowEnergy.PreparationVacuumCurrentSignalOperator
