import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalMaterialMomentum
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMovingPoleJointObservation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleLegDynamics
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalFeedback PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumJointFieldResponse PreparationVacuumCurrentSignalOperator
open PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalTailPrice PreparationVacuumNoetherResponsePrice
open PreparationVacuumFieldPerturbation SourceFiniteUnitary GaussCoreHilbert
open Filter MeasureTheory Set
open scoped BigOperators Topology Matrix InnerProductSpace Interval
abbrev PoleOp:=H→L[ℂ] H
local instance : NormedAlgebra ℝ PoleOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ PoleOp:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointGenerator sourcePolePrepared actualMovingPolePreparation factorialBudget

private theorem timeContinuous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E→L[ℂ] E) : Continuous (time C):=
  continuous_iff_continuousAt.mpr (fun t=>
    (hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

private theorem scalarTime {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (energy t : ℝ) : time ((energy:ℂ) • (1 : E→L[ℂ] E)) t=
      Complex.exp ((-Complex.I)*(energy:ℂ)*(t:ℂ)) • (1 : E→L[ℂ] E) :=by
  have normalized : t • ((-Complex.I) • ((energy:ℂ) • (1:E→L[ℂ] E)))=
      algebraMap ℂ (E→L[ℂ] E) ((-Complex.I)*(energy:ℂ)*(t:ℂ)) :=by
    rw [←smul_assoc,smul_smul,Algebra.algebraMap_eq_smul_one]
    congr 1
    change (t:ℂ)*(-Complex.I)*(energy:ℂ)=(-Complex.I)*(energy:ℂ)*(t:ℂ)
    ring
  rw [time,normalized,←NormedSpace.algebraMap_exp_comm,←Complex.exp_eq_exp_ℂ,Algebra.algebraMap_eq_smul_one]

private theorem scalarPhase_unit (energy t : ℝ) : ‖Complex.exp ((-Complex.I)*(energy:ℂ)*(t:ℂ))‖=1 :=by
  rw [Complex.norm_exp]
  simp

private theorem columnDuhamel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E→L[ℂ] E) (energy : ℝ) (v : E) (t : ℝ) :
    time C t v-Complex.exp ((-Complex.I)*(energy:ℂ)*(t:ℂ)) • v=
      ∫s in (0:ℝ)..t,Complex.exp ((-Complex.I)*(energy:ℂ)*((t-s):ℂ)) •
        (time C s ((-Complex.I) • (C v-(energy:ℂ) • v))) :=by
  let scalar : E→L[ℂ] E:=(energy:ℂ) • 1
  have integral : IntervalIntegrable (fun s : ℝ=>time C s*((-Complex.I) • (C-scalar))*time scalar (t-s)) volume 0 t:=
    (((timeContinuous C).mul continuous_const).mul
      ((timeContinuous scalar).comp (continuous_const.sub continuous_id))).intervalIntegrable 0 t
  have difference:=congrArg (fun A : E→L[ℂ] E=>A v) (CanonicalGradedVariation.time_difference scalar C t)
  rw [CanonicalGradedVariation.differenceIntegral,ContinuousLinearMap.intervalIntegral_apply integral,sub_apply] at difference
  simp only [scalar,scalarTime,smul_apply,one_apply_eq_self] at difference
  rw [difference]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [mul_apply_eq_comp,smul_apply,sub_apply,one_apply_eq_self,
    map_smul,smul_smul,Complex.ofReal_sub]

def sourcePoleColumnDefect (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) : H:=
  jointGenerator momentum F 0 0 (sourcePolePrepared epsilon precision momentum state)-
    (sourceMovingPoleEnergy momentum state:ℂ) • sourcePolePrepared epsilon precision momentum state

def sourcePolePrimalCorrection (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (t : ℝ) : H:=
  ∫s in (0:ℝ)..t,Complex.exp ((-Complex.I)*(sourceMovingPoleEnergy momentum state:ℂ)*((t-s):ℂ)) •
    (time (jointGenerator momentum F 0 0) s ((-Complex.I) • sourcePoleColumnDefect epsilon precision momentum state F))

theorem sourcePolePrimalCorrection_generated (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    time (jointGenerator momentum F 0 0) t (sourcePolePrepared epsilon precision momentum state)=
      Complex.exp ((-Complex.I)*(sourceMovingPoleEnergy momentum state:ℂ)*(t:ℂ)) •
        sourcePolePrepared epsilon precision momentum state+sourcePolePrimalCorrection epsilon precision momentum state F t :=by
  have source:=columnDuhamel (jointGenerator momentum F 0 0) (sourceMovingPoleEnergy momentum state)
    (sourcePolePrepared epsilon precision momentum state) t
  have generated:=sub_eq_iff_eq_add.mp source
  simpa only [sourcePolePrimalCorrection,sourcePoleColumnDefect,add_comm] using generated

def sourcePoleDual (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) : H→L[ℂ] ℂ:=innerSL ℂ (sourcePolePrepared epsilon precision momentum state)

def sourcePoleDualDefect (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) : H→L[ℂ] ℂ:=
  (sourcePoleDual epsilon precision momentum state).comp (jointGenerator momentum F 0 0)-
    (sourceMovingPoleEnergy momentum state:ℂ) • sourcePoleDual epsilon precision momentum state

def sourcePoleDualCorrection (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (t : ℝ) : H→L[ℂ] ℂ:=
  ∫s in (0:ℝ)..(-t),Complex.exp ((-Complex.I)*(sourceMovingPoleEnergy momentum state:ℂ)*((-t-s):ℂ)) •
    (((-Complex.I) • sourcePoleDualDefect epsilon precision momentum state F).comp
      (time (jointGenerator momentum F 0 0) s))

private theorem dualDuhamel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E→L[ℂ] E) (energy : ℝ) (dual : E→L[ℂ] ℂ) (t : ℝ) :
    dual.comp (time C (-t))=
      Complex.exp (Complex.I*(energy:ℂ)*(t:ℂ)) • dual+
        ∫s in (0:ℝ)..(-t),Complex.exp ((-Complex.I)*(energy:ℂ)*((-t-s):ℂ)) •
          (((-Complex.I) • (dual.comp C-(energy:ℂ) • dual)).comp (time C s)) :=by
  let scalar : E→L[ℂ] E:=(energy:ℂ) • 1
  let compose : (E→L[ℂ] E)→L[ℂ] (E→L[ℂ] ℂ):=(ContinuousLinearMap.compL ℂ E E ℂ) dual
  have integral : IntervalIntegrable (fun s : ℝ=>time C s*((-Complex.I) • (C-scalar))*time scalar (-t-s)) volume 0 (-t):=
    (((timeContinuous C).mul continuous_const).mul
      ((timeContinuous scalar).comp (continuous_const.sub continuous_id))).intervalIntegrable 0 (-t)
  have source:=congrArg compose (CanonicalGradedVariation.time_difference scalar C (-t))
  rw [map_sub,CanonicalGradedVariation.differenceIntegral,←compose.intervalIntegral_comp_comm integral] at source
  have commutation (s : ℝ) : Commute (C-scalar) (time C s):=
    time_commutes C (C-scalar) ((Commute.refl C).sub_left ((Commute.one_left C).smul_left (energy:ℂ))) s
  have integrand (s : ℝ) : compose (time C s*((-Complex.I) • (C-scalar))*time scalar (-t-s))=
      Complex.exp ((-Complex.I)*(energy:ℂ)*((-t-s):ℂ)) •
        (((-Complex.I) • (dual.comp C-(energy:ℂ) • dual)).comp (time C s)) :=by
    simp only [scalar,scalarTime]
    ext v
    simp only [compose,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
      mul_apply_eq_comp,smul_apply,one_apply_eq_self,map_smul,sub_apply]
    have swap:=congrArg (fun A : E→L[ℂ] E=>A v) (commutation s).eq
    simp only [mul_apply_eq_comp,sub_apply,scalar,smul_apply,one_apply_eq_self] at swap
    change _=_
    rw [←swap]
    simp only [map_sub,map_smul,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_neg]
  rw [intervalIntegral.integral_congr (fun s _=>integrand s)] at source
  have identity : dual.comp (1:E→L[ℂ] E)=dual:=by ext v;rfl
  have aligned : compose (time scalar (-t))=Complex.exp (Complex.I*(energy:ℂ)*(t:ℂ)) • dual :=by
    simp only [scalar,scalarTime,compose,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_smul,identity]
    congr 1
    congr 1
    push_cast
    ring
  rw [aligned] at source
  simpa only [compose,ContinuousLinearMap.compL_apply,add_comm] using (sub_eq_iff_eq_add.mp source)

theorem sourcePoleDualCorrection_generated (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    (sourcePoleDual epsilon precision momentum state).comp (time (jointGenerator momentum F 0 0) (-t))=
      Complex.exp (Complex.I*(sourceMovingPoleEnergy momentum state:ℂ)*(t:ℂ)) •
        sourcePoleDual epsilon precision momentum state+sourcePoleDualCorrection epsilon precision momentum state F t :=by
  exact dualDuhamel _ _ _ _

private theorem actualTime_absolute (momentum : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (eta t : ℝ) (positive : 0<eta) :
    ‖time (jointGenerator momentum F 0 0) t‖≤factorialBudget momentum F eta*Real.exp (eta*|t|) :=by
  by_cases future : 0≤t
  · simpa only [physicalTime,abs_of_nonneg future] using actualTime_future momentum F eta t positive future
  · have past : 0≤-t:=by linarith
    simpa only [physicalTime,neg_neg,abs_of_neg (lt_of_not_ge future)] using actualTime_past momentum F eta (-t) positive past

theorem sourcePolePrimalCorrection_price (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (eta t : ℝ) (positive : 0<eta) (future : 0≤t) :
    ‖sourcePolePrimalCorrection epsilon precision momentum state F t‖≤
      (t*factorialBudget momentum F eta*Real.exp (eta*t))*‖sourcePoleColumnDefect epsilon precision momentum state F‖ :=by
  have bound (s : ℝ) (inside : s∈Ι (0:ℝ) t) :
      ‖Complex.exp ((-Complex.I)*(sourceMovingPoleEnergy momentum state:ℂ)*((t-s):ℂ)) •
        (time (jointGenerator momentum F 0 0) s ((-Complex.I) • sourcePoleColumnDefect epsilon precision momentum state F))‖≤
      factorialBudget momentum F eta*Real.exp (eta*t)*‖sourcePoleColumnDefect epsilon precision momentum state F‖ :=by
    have within : |s|≤t:=by
      simpa only [abs_of_nonneg future] using (PreparationVacuumFieldPerturbation.interval_times inside).1
    have phase:=scalarPhase_unit (sourceMovingPoleEnergy momentum state) (t-s)
    simp only [Complex.ofReal_sub] at phase
    rw [norm_smul,phase,one_mul]
    have timeprice:=actualTime_absolute momentum F eta s positive
    have larger : factorialBudget momentum F eta*Real.exp (eta*|s|)≤factorialBudget momentum F eta*Real.exp (eta*t):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left within positive.le))
        (factorialBudget_nonnegative momentum F eta positive)
    have applied:=(time (jointGenerator momentum F 0 0) s).le_opNorm ((-Complex.I) • sourcePoleColumnDefect epsilon precision momentum state F)
    rw [norm_smul,norm_neg,Complex.norm_I,one_mul] at applied
    exact applied.trans (mul_le_mul_of_nonneg_right (timeprice.trans larger) (norm_nonneg _))
  have integral:=intervalIntegral.norm_integral_le_of_norm_le_const bound
  change ‖sourcePolePrimalCorrection epsilon precision momentum state F t‖≤_ at integral
  exact integral.trans_eq (by rw [sub_zero,abs_of_nonneg future];ring)

theorem sourcePoleDualCorrection_price (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (eta t : ℝ) (positive : 0<eta) (future : 0≤t) :
    ‖sourcePoleDualCorrection epsilon precision momentum state F t‖≤
      (t*factorialBudget momentum F eta*Real.exp (eta*t))*‖sourcePoleDualDefect epsilon precision momentum state F‖ :=by
  have bound (s : ℝ) (inside : s∈Ι (0:ℝ) (-t)) :
      ‖Complex.exp ((-Complex.I)*(sourceMovingPoleEnergy momentum state:ℂ)*((-t-s):ℂ)) •
        (((-Complex.I) • sourcePoleDualDefect epsilon precision momentum state F).comp
          (time (jointGenerator momentum F 0 0) s))‖≤
      ‖sourcePoleDualDefect epsilon precision momentum state F‖*
        (factorialBudget momentum F eta*Real.exp (eta*t)) :=by
    have phase:=scalarPhase_unit (sourceMovingPoleEnergy momentum state) (-t-s)
    simp only [Complex.ofReal_sub,Complex.ofReal_neg] at phase
    rw [norm_smul,phase,one_mul]
    have timeprice:=actualTime_absolute momentum F eta s positive
    have within : |s|≤t:=by
      simpa only [abs_neg,abs_of_nonneg future] using (PreparationVacuumFieldPerturbation.interval_times inside).1
    have larger : factorialBudget momentum F eta*Real.exp (eta*|s|)≤factorialBudget momentum F eta*Real.exp (eta*t):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left within positive.le))
        (factorialBudget_nonnegative momentum F eta positive)
    have applied:=ContinuousLinearMap.opNorm_comp_le
      ((-Complex.I) • sourcePoleDualDefect epsilon precision momentum state F)
      (time (jointGenerator momentum F 0 0) s)
    rw [norm_smul,norm_neg,Complex.norm_I,one_mul] at applied
    exact applied.trans (mul_le_mul_of_nonneg_left (timeprice.trans larger) (norm_nonneg _))
  have integral:=intervalIntegral.norm_integral_le_of_norm_le_const bound
  change ‖sourcePoleDualCorrection epsilon precision momentum state F t‖≤_ at integral
  exact integral.trans_eq (by rw [sub_zero,abs_neg,abs_of_nonneg future];ring)

theorem sourcePolePrimalCorrection_initial (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) : sourcePolePrimalCorrection epsilon precision momentum state F 0=0 :=by
  simp only [sourcePolePrimalCorrection,intervalIntegral.integral_same]

theorem sourcePoleDualCorrection_initial (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) : sourcePoleDualCorrection epsilon precision momentum state F 0=0 :=by
  simp only [sourcePoleDualCorrection,neg_zero,intervalIntegral.integral_same]

end LowEnergy.PreparationVacuumPhysicalPoleLegDynamics
