import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationPropagationPencilDynamics
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPropagationPencil
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalTailPrice PreparationVacuumGaugeSourceInjection
open Filter Set MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix Interval
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointGenerator jointCurrent jointResolvent rawReader rawReaderContact
  physicalTime timeSlope factorialBudget variationBudget leftGenerator rightGenerator leftCurrent rightCurrent

section Weighted
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem weighted_integrable_op (f : ℝ→E) (hc : Continuous f) (hf : SourceSubexp f)
    (lambda : ℂ) (positive : 0<lambda.re) :
    IntegrableOn (fun r=>laplaceWeight lambda r • f r) (Ioi (0:ℝ)) :=by
  have half : 0<lambda.re/2:=by positivity
  have small : ∀ᶠr : ℝ in atTop,Real.exp (-(lambda.re/2)*r)*‖f r‖<1:=
    (hf (lambda.re/2) half).eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))
  obtain ⟨A,hA⟩:=eventually_atTop.mp small
  let B:=max A 0
  have bound (r : ℝ) (hr : B<r) : ‖laplaceWeight lambda r • f r‖≤Real.exp (-(lambda.re/2)*r):=by
    have s:=(hA r ((le_max_left A 0).trans hr.le)).le
    have w : Real.exp (-lambda.re*r)=Real.exp (-(lambda.re/2)*r)*Real.exp (-(lambda.re/2)*r):=by
      rw [←Real.exp_add];congr 1;ring
    calc
      _=Real.exp (-lambda.re*r)*‖f r‖:=by rw [norm_smul,laplace_norm]
      _=Real.exp (-(lambda.re/2)*r)*(Real.exp (-(lambda.re/2)*r)*‖f r‖):=by rw [w];ring
      _≤Real.exp (-(lambda.re/2)*r)*1:=mul_le_mul_of_nonneg_left s (Real.exp_pos _).le
      _=_:=mul_one _
  have majorant : IntegrableOn (fun r : ℝ=>Real.exp (-(lambda.re/2)*r)) (Ioi B):=
    integrableOn_exp_mul_Ioi (by linarith) B
  have wcont : Continuous (fun r=>laplaceWeight lambda r • f r):=by
    apply Continuous.smul
    · unfold laplaceWeight;fun_prop
    · exact hc
  have tail : IntegrableOn (fun r=>laplaceWeight lambda r • f r) (Ioi B):=by
    apply majorant.mono' wcont.aestronglyMeasurable.restrict
    apply (ae_restrict_mem measurableSet_Ioi).mono
    exact bound
  have finite : IntegrableOn (fun r=>laplaceWeight lambda r • f r) (Ioc 0 B):=
    (wcont.intervalIntegrable (0:ℝ) B).1
  rw [←Ioc_union_Ioi_eq_Ioi (show (0:ℝ)≤B from le_max_right A 0)]
  exact finite.union tail

private theorem weighted_zero (f : ℝ→E) (hf : SourceSubexp f) (lambda : ℂ) (positive : 0<lambda.re) :
    Tendsto (fun r=>laplaceWeight lambda r • f r) atTop (𝓝 0) :=by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_smul,laplace_norm] using hf lambda.re positive

private theorem weight_jet (lambda : ℂ) (t : ℝ) :
    HasDerivAt (laplaceWeight lambda) (-lambda*laplaceWeight lambda t) t :=by
  unfold laplaceWeight
  convert! (((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.const_mul (-lambda)).cexp) using 1
  simp [Complex.ofRealCLM]
  ring

variable [CompleteSpace E]

private theorem actual_laplace_ode (L : E→L[ℂ] E) (f d : ℝ→E)
    (hc : Continuous f) (hd : Continuous d) (hf : SourceSubexp f) (hds : SourceSubexp d)
    (ode : ∀r,HasDerivAt f (L (f r)+d r) r) (lambda : ℂ) (positive : 0<lambda.re) :
    lambda • (∫r in Ioi (0:ℝ),laplaceWeight lambda r • f r)-
      L (∫r in Ioi (0:ℝ),laplaceWeight lambda r • f r)=
      f 0+∫r in Ioi (0:ℝ),laplaceWeight lambda r • d r :=by
  have fi:=weighted_integrable_op f hc hf lambda positive
  have di:=weighted_integrable_op d hd hds lambda positive
  let B : E→L[ℂ] E:=L-lambda • ContinuousLinearMap.id ℂ E
  have derivative (r : ℝ) :
      HasDerivAt (fun s=>laplaceWeight lambda s • f s)
        (B (laplaceWeight lambda r • f r)+laplaceWeight lambda r • d r) r :=by
    have h:=(weight_jet lambda r).smul (ode r)
    convert! h using 1
    dsimp only [B]
    rw [sub_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_smul]
    rw [neg_mul,neg_smul]
    rw [smul_add]
    abel
  have bi : IntegrableOn (fun r=>B (laplaceWeight lambda r • f r)) (Ioi (0:ℝ)):=
    B.integrable_comp fi
  have total:=integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _=>derivative r) (bi.add di)
    (weighted_zero f hf lambda positive)
  rw [integral_add bi di,B.integral_comp_comm fi] at total
  have atzero : laplaceWeight lambda 0=1:=by simp [laplaceWeight]
  simp only [B,sub_apply,smul_apply,ContinuousLinearMap.id_apply,atzero,one_smul,zero_sub] at total
  calc
    _=-(L (∫r in Ioi (0:ℝ),laplaceWeight lambda r • f r)-
      lambda • (∫r in Ioi (0:ℝ),laplaceWeight lambda r • f r)+
      ∫r in Ioi (0:ℝ),laplaceWeight lambda r • d r)+
      ∫r in Ioi (0:ℝ),laplaceWeight lambda r • d r:=by abel
    _=_:=by rw [total,neg_neg]

end Weighted

def rawFlow (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) : Op:=
  fiveKernel reader q.p q.k q.F q.z q.w t 0

def slopeFlow (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) : Op:=
  fiveDerivative reader force q.p q.k q.F q.z q.w t

def evolutionGenerator (q : PhysicalResponsePoint) : Op→L[ℂ] Op:=
  ContinuousLinearMap.mul ℂ Op (-leftGenerator q)+
    (ContinuousLinearMap.mul ℂ Op).flip (rightGenerator q)

def driveOperator (q : PhysicalResponsePoint) (force : Field289) : Op→L[ℂ] Op:=
  -ContinuousLinearMap.mul ℂ Op (leftCurrent q force)+
    (ContinuousLinearMap.mul ℂ Op).flip (rightCurrent q force)

def slopeDrive (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) : Op:=
  driveOperator q force (rawFlow q reader t)

theorem driveOperator_apply (q : PhysicalResponsePoint) (force : Field289) (A : Op) :
    driveOperator q force A=-(leftCurrent q force*A)+A*rightCurrent q force :=rfl

def rawHalf (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ) : Op:=
  ∫r in Ioi (0:ℝ),laplaceWeight lambda r • rawFlow q reader r

def slopeHalf (q : PhysicalResponsePoint) (reader force : Field289) (lambda : ℂ) : Op:=
  ∫r in Ioi (0:ℝ),laplaceWeight lambda r • slopeFlow q reader force r

def propagationPencil (q : PhysicalResponsePoint) (lambda : ℂ) : Op→L[ℂ] Op:=
  lambda • ContinuousLinearMap.id ℂ Op-evolutionGenerator q

private theorem sylvester_algebra {R : Type*} [Ring R] (x l r a : R) :
    x-((-l)*a+a*r)=x+l*a-a*r :=by
  rw [neg_mul,sub_eq_add_neg,neg_add_rev,neg_neg]
  abel

theorem propagationPencil_actual (q : PhysicalResponsePoint) (lambda : ℂ) (A : Op) :
    propagationPencil q lambda A=lambda • A+leftGenerator q*A-A*rightGenerator q :=by
  simp only [propagationPencil,evolutionGenerator,sub_apply,
    add_apply,smul_apply,ContinuousLinearMap.id_apply,
    neg_apply,ContinuousLinearMap.mul_apply',ContinuousLinearMap.flip_apply]
  convert! sylvester_algebra (lambda • A) (leftGenerator q) (rightGenerator q) A using 1

theorem evolutionGenerator_apply (q : PhysicalResponsePoint) (A : Op) :
    evolutionGenerator q A=-leftGenerator q*A+A*rightGenerator q :=by
  rfl

theorem rawFlow_subexp (q : PhysicalResponsePoint) (reader : Field289) : SourceSubexp (rawFlow q reader) :=by
  have h:=(rawKernelJets_subexp reader q.p q.k q.F q.z q.w).1
  convert! h using 1; first | rfl | (funext r; simp only [rawFlow,rawKernelJet_value])

theorem slopeFlow_subexp (q : PhysicalResponsePoint) (reader force : Field289) : SourceSubexp (slopeFlow q reader force) :=by
  have h:=(slopeKernelJets_subexp reader force q.p q.k q.F q.z q.w).1
  convert! h using 1; first | rfl | (funext r; simp only [slopeFlow,slopeKernelJet_value])

theorem rawFlow_integrable (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    IntegrableOn (fun r=>laplaceWeight lambda r • rawFlow q reader r) (Ioi (0:ℝ)) :=
  weighted_integrable_op _ (continuous_iff_continuousAt.mpr (fun r=>(rawKernel_ode q reader r).continuousAt))
    (rawFlow_subexp q reader) lambda positive

theorem slopeFlow_integrable (q : PhysicalResponsePoint) (reader force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    IntegrableOn (fun r=>laplaceWeight lambda r • slopeFlow q reader force r) (Ioi (0:ℝ)) :=
  weighted_integrable_op _ (continuous_iff_continuousAt.mpr (fun r=>(slopeKernel_ode q reader force r).continuousAt))
    (slopeFlow_subexp q reader force) lambda positive

theorem rawHalf_pencil (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    propagationPencil q lambda (rawHalf q reader lambda)=rawInitial q reader :=by
  have hc : Continuous (rawFlow q reader):=continuous_iff_continuousAt.mpr (fun r=>(rawKernel_ode q reader r).continuousAt)
  have ode (r : ℝ) : HasDerivAt (rawFlow q reader) (evolutionGenerator q (rawFlow q reader r)+(0:Op)) r:=by
    convert! rawKernel_ode q reader r using 1; first | rfl | simp only [rawFlow,evolutionGenerator_apply,add_zero]
  have h:=actual_laplace_ode (evolutionGenerator q) (rawFlow q reader) (fun _=>0) hc continuous_const
    (rawFlow_subexp q reader) (subexp_const 0) ode lambda positive
  simpa only [propagationPencil,rawHalf,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,smul_zero,integral_zero,add_zero,rawFlow,rawKernel_initial] using h

theorem slopeHalf_pencil (q : PhysicalResponsePoint) (reader force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    propagationPencil q lambda (slopeHalf q reader force lambda)=
      slopeInitial q reader force-leftCurrent q force*rawHalf q reader lambda+
        rawHalf q reader lambda*rightCurrent q force :=by
  have hc : Continuous (slopeFlow q reader force):=continuous_iff_continuousAt.mpr (fun r=>(slopeKernel_ode q reader force r).continuousAt)
  have rawc : Continuous (rawFlow q reader):=continuous_iff_continuousAt.mpr (fun r=>(rawKernel_ode q reader r).continuousAt)
  have drivec : Continuous (slopeDrive q reader force):=by
    exact (driveOperator q force).continuous.comp rawc
  have drives : SourceSubexp (slopeDrive q reader force):=by
    exact subexp_map (driveOperator q force) (rawFlow_subexp q reader)
  have ode (r : ℝ) : HasDerivAt (slopeFlow q reader force)
      (evolutionGenerator q (slopeFlow q reader force r)+slopeDrive q reader force r) r:=by
    have h:=slopeKernel_ode q reader force r
    convert! h using 1; first | rfl | (simp only [slopeFlow,rawFlow,slopeDrive,driveOperator_apply,evolutionGenerator_apply,sub_eq_add_neg]; abel)
  have h:=actual_laplace_ode (evolutionGenerator q) (slopeFlow q reader force) (slopeDrive q reader force)
    hc drivec (slopeFlow_subexp q reader force) drives ode lambda positive
  have ri:=rawFlow_integrable q reader lambda positive
  have integralDrive : (∫r in Ioi (0:ℝ),laplaceWeight lambda r • slopeDrive q reader force r)=
      -(leftCurrent q force*rawHalf q reader lambda)+rawHalf q reader lambda*rightCurrent q force :=by
    rw [←driveOperator_apply q force (rawHalf q reader lambda)]
    unfold slopeDrive rawHalf
    rw [←(driveOperator q force).integral_comp_comm ri]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun r=>(map_smul (driveOperator q force) (laplaceWeight lambda r) (rawFlow q reader r)).symm)
  simpa only [propagationPencil,slopeHalf,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,slopeFlow,slopeKernel_initial,integralDrive,sub_eq_add_neg,add_assoc,neg_mul] using h

end LowEnergy.PreparationVacuumPropagationPencil
