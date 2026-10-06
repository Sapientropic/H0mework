import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationTwoTimeGroup
import Mathlib.Analysis.Normed.Algebra.Spectrum

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationResolvent
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalTailPrice PreparationVacuumPropagationPencil PreparationVacuumGaugeSourceInjection
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace Interval
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ TransferOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ TransferOp:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedSpace ℝ TransferOp:=ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ TransferOp:=by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=TransferOp)) using 1
local instance : ContinuousSMul ℝ TransferOp:=by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=TransferOp)) using 1
local instance : ContinuousENorm TransferOp:=by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=TransferOp)) using 1
local instance : IsScalarTower ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  rfl⟩
local instance : SMulCommClass ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  exact (map_smul A c (B X)).symm⟩
attribute [local irreducible] evolutionGenerator propagationPencil twoTimeMap rawHalf slopeHalf

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
/-- The whole source inverse is generated by actual physical time, with no inverse certificate. -/
def sourceInverse (q : PhysicalResponsePoint) (lambda : ℂ) : TransferOp:=
  ∫r in Ioi (0:ℝ),laplaceWeight lambda r • twoTimeMap q r

attribute [local irreducible] sourceInverse

theorem sourceInverse_integrable (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    IntegrableOn (fun r=>laplaceWeight lambda r • twoTimeMap q r) (Ioi (0:ℝ)) :=
  by
    have h:=weighted_integrable_op (E:=TransferOp) (twoTimeMap q) (twoTimeMap_continuous q) (twoTimeMap_subexp q) lambda positive
    convert! h using 1

private theorem pencil_left_algebra {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R]
    (lambda : ℂ) (L A : R) : (lambda • 1-L)*A=lambda • A-L*A :=by
  rw [sub_mul,smul_mul_assoc,one_mul]

private theorem pencil_right_algebra {R : Type*} [Ring R] [Module ℂ R] [SMulCommClass ℂ R R]
    (lambda : ℂ) (L A : R) : A*(lambda • 1-L)=lambda • A-A*L :=by
  rw [mul_sub,mul_smul_comm,mul_one]

theorem sourceInverse_left (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    propagationPencil q lambda*sourceInverse q lambda=1 :=by
  have ode (r : ℝ) : HasDerivAt (twoTimeMap q)
      (ContinuousLinearMap.mul ℂ TransferOp (evolutionGenerator q) (twoTimeMap q r)+(0:TransferOp)) r:=by
    have h:=twoTimeMap_derivative q r
    have normal : @HasDerivAt ℝ _ TransferOp (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup
        (NormedSpace.restrictScalars ℝ ℂ TransferOp).toModule
        (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
        (NormedSpace.restrictScalars ℝ ℂ TransferOp).toIsBoundedSMul.continuousSMul
        (twoTimeMap q) (evolutionGenerator q*twoTimeMap q r) r:=by
      convert! h using 1
    convert! normal using 1
    convert! add_zero (evolutionGenerator q*twoTimeMap q r) using 1
  have hc : Continuous (twoTimeMap q):=by convert! twoTimeMap_continuous q using 1
  have hf : SourceSubexp (twoTimeMap q):=by convert! twoTimeMap_subexp q using 1
  have h : lambda • (∫r in Ioi (0:ℝ),laplaceWeight lambda r • twoTimeMap q r)-
      (ContinuousLinearMap.mul ℂ TransferOp (evolutionGenerator q))
        (∫r in Ioi (0:ℝ),laplaceWeight lambda r • twoTimeMap q r)=
      twoTimeMap q 0+∫r in Ioi (0:ℝ),laplaceWeight lambda r • (0:TransferOp) :=by
    apply actual_laplace_ode (E:=TransferOp) _ _ (fun _=>0)
    · convert! hc using 1
    · exact continuous_const
    · convert! hf using 1
    · exact subexp_const 0
    · intro r
      convert! ode r using 1
    · exact positive
  simp only [ContinuousLinearMap.mul_apply',smul_zero,integral_zero,add_zero,twoTimeMap_initial] at h
  have value : (∫r in Ioi (0:ℝ),laplaceWeight lambda r • twoTimeMap q r)=sourceInverse q lambda:=by unfold sourceInverse;rfl
  unfold propagationPencil
  change (lambda • (1:TransferOp)-evolutionGenerator q)*sourceInverse q lambda=1
  have paid : lambda • sourceInverse q lambda-evolutionGenerator q*sourceInverse q lambda=(1:TransferOp):=by
    convert! h using 1
    · exact congrArg (fun A : TransferOp=>lambda • A-evolutionGenerator q*A) value.symm
    · have zeroFunction : (fun r : ℝ=>laplaceWeight lambda r • (0:TransferOp))=(fun _ : ℝ=>(0:TransferOp)):=by
        funext r
        apply ContinuousLinearMap.ext
        intro A
        apply ContinuousLinearMap.ext
        intro x
        simp only [smul_apply,zero_apply,smul_zero]
      have zeroValue : (∫r in Ioi (0:ℝ),laplaceWeight lambda r • (0:TransferOp))=0:=by
        calc
          _=∫r in Ioi (0:ℝ),(0:TransferOp):=congrArg (fun f : ℝ→TransferOp=>∫r in Ioi (0:ℝ),f r) zeroFunction
          _=0:=by convert! (integral_zero (G:=TransferOp) (μ:=volume.restrict (Ioi (0:ℝ)))) using 1
      exact (add_zero (1:TransferOp)).symm.trans (congrArg (fun A : TransferOp=>(1:TransferOp)+A) zeroValue.symm)
  have algebra : (lambda • (1:TransferOp)-evolutionGenerator q)*sourceInverse q lambda=
      lambda • sourceInverse q lambda-evolutionGenerator q*sourceInverse q lambda :=by
    convert! pencil_left_algebra (R:=TransferOp) lambda (evolutionGenerator q) (sourceInverse q lambda) using 1
  exact algebra.trans paid

theorem sourceInverse_right (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    sourceInverse q lambda*propagationPencil q lambda=1 :=by
  have ode (r : ℝ) : HasDerivAt (twoTimeMap q)
      ((ContinuousLinearMap.mul ℂ TransferOp).flip (evolutionGenerator q) (twoTimeMap q r)+(0:TransferOp)) r:=by
    have h:=twoTimeMap_right_derivative q r
    have normal : @HasDerivAt ℝ _ TransferOp (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup
        (NormedSpace.restrictScalars ℝ ℂ TransferOp).toModule
        (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
        (NormedSpace.restrictScalars ℝ ℂ TransferOp).toIsBoundedSMul.continuousSMul
        (twoTimeMap q) (twoTimeMap q r*evolutionGenerator q) r:=by
      convert! h using 1
    convert! normal using 1
    convert! add_zero (twoTimeMap q r*evolutionGenerator q) using 1
  have hc : Continuous (twoTimeMap q):=by convert! twoTimeMap_continuous q using 1
  have hf : SourceSubexp (twoTimeMap q):=by convert! twoTimeMap_subexp q using 1
  have h : lambda • (∫r in Ioi (0:ℝ),laplaceWeight lambda r • twoTimeMap q r)-
      ((ContinuousLinearMap.mul ℂ TransferOp).flip (evolutionGenerator q))
        (∫r in Ioi (0:ℝ),laplaceWeight lambda r • twoTimeMap q r)=
      twoTimeMap q 0+∫r in Ioi (0:ℝ),laplaceWeight lambda r • (0:TransferOp) :=by
    apply actual_laplace_ode (E:=TransferOp) _ _ (fun _=>0)
    · convert! hc using 1
    · exact continuous_const
    · convert! hf using 1
    · exact subexp_const 0
    · intro r
      convert! ode r using 1
    · exact positive
  simp only [ContinuousLinearMap.mul_apply',ContinuousLinearMap.flip_apply,smul_zero,integral_zero,add_zero,twoTimeMap_initial] at h
  have value : (∫r in Ioi (0:ℝ),laplaceWeight lambda r • twoTimeMap q r)=sourceInverse q lambda:=by unfold sourceInverse;rfl
  unfold propagationPencil
  change sourceInverse q lambda*(lambda • (1:TransferOp)-evolutionGenerator q)=1
  have paid : lambda • sourceInverse q lambda-sourceInverse q lambda*evolutionGenerator q=(1:TransferOp):=by
    convert! h using 1
    · exact congrArg (fun A : TransferOp=>lambda • A-A*evolutionGenerator q) value.symm
    · have zeroFunction : (fun r : ℝ=>laplaceWeight lambda r • (0:TransferOp))=(fun _ : ℝ=>(0:TransferOp)):=by
        funext r
        apply ContinuousLinearMap.ext
        intro A
        apply ContinuousLinearMap.ext
        intro x
        simp only [smul_apply,zero_apply,smul_zero]
      have zeroValue : (∫r in Ioi (0:ℝ),laplaceWeight lambda r • (0:TransferOp))=0:=by
        calc
          _=∫r in Ioi (0:ℝ),(0:TransferOp):=congrArg (fun f : ℝ→TransferOp=>∫r in Ioi (0:ℝ),f r) zeroFunction
          _=0:=by convert! (integral_zero (G:=TransferOp) (μ:=volume.restrict (Ioi (0:ℝ)))) using 1
      exact (add_zero (1:TransferOp)).symm.trans (congrArg (fun A : TransferOp=>(1:TransferOp)+A) zeroValue.symm)
  have algebra : sourceInverse q lambda*(lambda • (1:TransferOp)-evolutionGenerator q)=
      lambda • sourceInverse q lambda-sourceInverse q lambda*evolutionGenerator q :=by
    convert! pencil_right_algebra (R:=TransferOp) lambda (evolutionGenerator q) (sourceInverse q lambda) using 1
  exact algebra.trans paid

theorem sourcePencil_isUnit (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    IsUnit (propagationPencil q lambda) :=
  ⟨⟨propagationPencil q lambda,sourceInverse q lambda,sourceInverse_left q lambda positive,
      sourceInverse_right q lambda positive⟩,rfl⟩

theorem rawHalf_true_inverse (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    rawHalf q reader lambda=sourceInverse q lambda (rawInitial q reader) :=by
  have h:=congrArg (fun A : Op=>sourceInverse q lambda A) (rawHalf_pencil q reader lambda positive)
  have cancel:=congrArg (fun L : TransferOp=>L (rawHalf q reader lambda)) (sourceInverse_right q lambda positive)
  simpa only [mul_apply_eq_comp,one_apply_eq_self] using cancel.symm.trans h

theorem slopeHalf_true_inverse (q : PhysicalResponsePoint) (reader force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    slopeHalf q reader force lambda=sourceInverse q lambda
      (slopeInitial q reader force-leftCurrent q force*sourceInverse q lambda (rawInitial q reader)+
        sourceInverse q lambda (rawInitial q reader)*rightCurrent q force) :=by
  have h:=congrArg (fun A : Op=>sourceInverse q lambda A) (slopeHalf_pencil q reader force lambda positive)
  have cancel:=congrArg (fun L : TransferOp=>L (slopeHalf q reader force lambda)) (sourceInverse_right q lambda positive)
  rw [rawHalf_true_inverse q reader lambda positive] at h
  simpa only [mul_apply_eq_comp,one_apply_eq_self] using cancel.symm.trans h

end LowEnergy.SourcePropagationResolvent
