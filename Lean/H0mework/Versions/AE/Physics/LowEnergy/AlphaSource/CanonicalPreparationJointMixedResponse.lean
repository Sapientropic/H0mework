import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationJointSource
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumJointFieldResponse
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse PreparationVacuumSourceActionJets
open PreparationVacuumGradedTransport PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open PreparationVacuumSourcePreparedResponse PreparationVacuumSpatialDensityTransport
open CanonicalPreparationCore.Completed GaussComposite GaussComposite.SourceGraph
open Filter Set
open scoped Topology ContDiff BigOperators InnerProductSpace
abbrev Operator:=H→L[ℂ] H
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator

def jointCurrent (p : PhysicalMomentum) (F : Index) (z : ℂ) (h : Field289) : Field289→L[ℝ] Operator:=
  fderiv ℝ (jointGenerator p F z) h

def jointHessian (p : PhysicalMomentum) (F : Index) (z : ℂ) : Field289→L[ℝ] Field289→L[ℝ] Operator:=
  fderiv ℝ (jointCurrent p F z) 0

theorem jointHessian_symmetric (p : PhysicalMomentum) (F : Index) (z : ℂ) (f g : Field289) :
    jointHessian p F z f g=jointHessian p F z g f :=
  (jointGenerator_C2 p F z).isSymmSndFDerivAt (by simp) f g

theorem fieldRay_derivative (f : Field289) (r : ℝ) : HasDerivAt (fun t : ℝ=>t • f) f r :=by
  simpa only [id_eq,one_smul] using (hasDerivAt_id r).smul_const f

theorem jointCurrent_source (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) :
    jointCurrent p F z 0 f=PreparationVacuumUncutYukawa.sourceCurrent f p F none 0 :=by
  have h:=(jointGenerator_C2 p F z).differentiableAt (by norm_num) |>.hasFDerivAt
  have generated:=h.comp_hasDerivAt_of_eq 0 (fieldRay_derivative f 0) (by simp)
  have original:=(sourceGenerator_derivative f p F none z).self_of_nhds
  have same:=original.congr_of_eventuallyEq (jointGenerator_ray f p F z)
  exact generated.unique same

theorem jointGenerator_ray_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) :
    ∀ᶠr : ℝ in 𝓝 0,HasDerivAt (fun t : ℝ=>jointGenerator p F z (t • f)) (jointCurrent p F z (r • f) f) r :=by
  have path : Tendsto (fun r : ℝ=>r • f) (𝓝 0) (𝓝 (0:Field289)):=by
    have continuous : Continuous (fun r : ℝ=>r • f):=continuous_id.smul continuous_const
    simpa only [zero_smul] using continuous.tendsto (0:ℝ)
  have nearby:=(jointGenerator_C2 p F z).eventually (by norm_num)
  filter_upwards [path.eventually nearby] with r hr
  exact hr.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt r (fieldRay_derivative f r)

theorem current_direction (p : PhysicalMomentum) (F : Index) (z : ℂ) (f g : Field289) :
    HasDerivAt (fun r : ℝ=>jointCurrent p F z (r • f) g) (jointHessian p F z f g) 0 :=by
  have hc:=(jointGenerator_C2 p F z).fderiv_right (m:=1) (by norm_num)
  have diff:=hc.differentiableAt (by norm_num) |>.hasFDerivAt
  let E : (Field289→L[ℝ] Operator)→L[ℝ] Operator:=ContinuousLinearMap.apply ℝ Operator g
  have read:=E.hasFDerivAt.comp 0 diff
  have generated:=read.comp_hasDerivAt_of_eq 0 (fieldRay_derivative f 0) (by simp)
  exact generated

theorem jointHessian_source_diagonal (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) :
    jointHessian p F z f f=PreparationVacuumUncutYukawa.sourceContact f p F none :=by
  have first : (fun r : ℝ=>jointCurrent p F z (r • f) f)=ᶠ[𝓝 0] PreparationVacuumUncutYukawa.sourceCurrent f p F none :=by
    filter_upwards [jointGenerator_ray_derivative f p F z,sourceGenerator_derivative f p F none z,
      (jointGenerator_ray f p F z).eventually_nhds] with r hr hs he
    exact hr.unique (hs.congr_of_eventuallyEq he)
  exact (current_direction p F z f f).unique ((sourceCurrent_derivative f p F none).congr_of_eventuallyEq first)

theorem jointGenerator_unit (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) :
    IsUnit (jointGenerator p F z 0) :=by
  have base:=(jointGenerator_ray (0:Field289) p F z).self_of_nhds
  simp only [zero_smul] at base
  rw [base]
  exact (sourceUnit 0 p F none z 0 (movingDiagonal_units 0 p F z hz).self_of_nhds).isUnit

def jointResolvent (p : PhysicalMomentum) (F : Index) (z : ℂ) (h : Field289) : Operator:=
  Ring.inverse (jointGenerator p F z h)

theorem jointResolvent_C2 (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) :
    ContDiffAt ℝ 2 (jointResolvent p F z) 0 :=by
  obtain ⟨u,hu⟩:=jointGenerator_unit p F z hz
  have outer : ContDiffAt ℝ 2 (Ring.inverse : Operator→Operator) (jointGenerator p F z 0):=by
    rw [←hu];exact contDiffAt_ringInverse ℝ u
  exact outer.comp 0 (jointGenerator_C2 p F z)

theorem jointResolvent_ray (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) :
    (fun r : ℝ=>jointResolvent p F z (r • f))=ᶠ[𝓝 0] sourceResolvent f p F none z :=
  (jointGenerator_ray f p F z).mono (fun _ h=>congrArg Ring.inverse h)

theorem inverse_direction (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) (f : Field289) :
    HasDerivAt (fun r : ℝ=>jointResolvent p F z (r • f))
      (-(jointResolvent p F z 0*jointCurrent p F z 0 f*jointResolvent p F z 0)) 0 :=by
  have line:=(jointGenerator_ray_derivative f p F z).self_of_nhds
  simp only [zero_smul] at line
  have unit:=jointGenerator_unit p F z hz
  have result:=inverse_curve_derivative (fun r : ℝ=>jointGenerator p F z (r • f)) 0
    (jointCurrent p F z 0 f) line (by simpa only [zero_smul] using unit)
  simpa only [zero_smul,jointResolvent] using result

attribute [local irreducible] jointResolvent jointCurrent jointHessian
  PreparationVacuumUncutYukawa.sourceResolvent PreparationVacuumUncutYukawa.sourceCurrent
  PreparationVacuumUncutYukawa.sourceContact

def jointVertex (g : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (h : Field289) : Operator:=
  -(jointResolvent (p+k) F z h*jointCurrent p F w h g*jointResolvent p F w h)

def mixedVertex (f g : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) : Operator:=
  jointResolvent (p+k) F z 0*jointCurrent (p+k) F z 0 f*jointResolvent (p+k) F z 0*
    jointCurrent p F w 0 g*jointResolvent p F w 0+
  jointResolvent (p+k) F z 0*jointCurrent p F w 0 g*jointResolvent p F w 0*
    jointCurrent p F w 0 f*jointResolvent p F w 0-
  jointResolvent (p+k) F z 0*jointHessian p F w f g*jointResolvent p F w 0

private theorem mixed_inverse_algebra {A : Type*} [Ring A] (L R J K Q S : A) :
    -((-(L*J*L)*K+L*S)*R+(L*K)*(-(R*Q*R)))=
      L*J*L*K*R+L*K*R*Q*R-L*S*R :=by
  simp only [mul_add,add_mul,neg_mul,mul_neg,neg_neg,neg_add,mul_assoc,sub_eq_add_neg]
  abel

theorem mixedVertex_generated (f g : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    HasDerivAt (fun r : ℝ=>jointVertex g p k F z w (r • f)) (mixedVertex f g p k F z w) 0 :=by
  have left:=inverse_direction (p+k) F z hz f
  have middle:=current_direction p F w f g
  have right:=inverse_direction p F w hw f
  have generated:=((left.mul middle).mul right).neg
  simp only [Pi.mul_apply,Pi.neg_apply,zero_smul] at generated
  have algebra:=mixed_inverse_algebra (jointResolvent (p+k) F z 0) (jointResolvent p F w 0)
    (jointCurrent (p+k) F z 0 f) (jointCurrent p F w 0 g) (jointCurrent p F w 0 f) (jointHessian p F w f g)
  exact generated.congr_deriv algebra

theorem jointResolvent_zero (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) :
    jointResolvent p F z 0=sourceResolvent f p F none z 0 :=by
  simpa only [zero_smul] using (jointResolvent_ray f p F z).self_of_nhds

theorem jointVertex_original_base (g : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) :
    jointVertex g p k F z w 0=
      -(sourceResolvent 0 (p+k) F none z 0*PreparationVacuumUncutYukawa.sourceCurrent g p F none 0*sourceResolvent 0 p F none w 0) :=by
  simp only [jointVertex,jointResolvent_zero 0,jointCurrent_source]

theorem mixedVertex_original_diagonal (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) :
    mixedVertex f f p 0 F z z=sourceInverseContact f p F none z :=by
  simp only [mixedVertex,add_zero,jointResolvent_zero f,jointCurrent_source,jointHessian_source_diagonal,sourceInverseContact]
  simp only [neg_mul,mul_neg,neg_neg,neg_add,add_mul,mul_add,sub_eq_add_neg,mul_assoc]
  abel

theorem mixedVertex_add_left (f f' g : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) :
    mixedVertex (f+f') g p k F z w=mixedVertex f g p k F z w+mixedVertex f' g p k F z w :=by
  simp only [mixedVertex,map_add,add_apply,mul_add,add_mul]
  simp only [neg_mul,mul_neg,neg_neg,neg_add,add_mul,mul_add,sub_eq_add_neg,mul_assoc]
  abel

theorem mixedVertex_add_right (f g g' : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) :
    mixedVertex f (g+g') p k F z w=mixedVertex f g p k F z w+mixedVertex f g' p k F z w :=by
  simp only [mixedVertex,map_add,add_apply,mul_add,add_mul]
  simp only [neg_mul,mul_neg,neg_neg,neg_add,add_mul,mul_add,sub_eq_add_neg,mul_assoc]
  abel

theorem mixedVertex_smul_left (c : ℝ) (f g : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) :
    mixedVertex (c • f) g p k F z w=c • mixedVertex f g p k F z w :=by
  have left (A B : Operator) : (c • A)*B=c • (A*B):=Algebra.smul_mul_assoc c A B
  have right (A B : Operator) : A*(c • B)=c • (A*B):=Algebra.mul_smul_comm c A B
  simp only [mixedVertex,map_smul,smul_apply,left,right,smul_add,smul_sub]

theorem mixedVertex_smul_right (c : ℝ) (f g : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) :
    mixedVertex f (c • g) p k F z w=c • mixedVertex f g p k F z w :=by
  have left (A B : Operator) : (c • A)*B=c • (A*B):=Algebra.smul_mul_assoc c A B
  have right (A B : Operator) : A*(c • B)=c • (A*B):=Algebra.mul_smul_comm c A B
  simp only [mixedVertex,map_smul,smul_apply,left,right,smul_add,smul_sub]

attribute [local irreducible] jointVertex mixedVertex sourceProfile

def preparedVertex (epsilon : ℝ) (precision : 0<epsilon) (g : Field289) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) (h : Field289) : ℂ:=
  inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (jointVertex g p k F z w h (completedLeg right b t (sourceProfile epsilon precision)))

def preparedMixed (epsilon : ℝ) (precision : 0<epsilon) (f g : Field289) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : ℂ:=
  inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (mixedVertex f g p k F z w (completedLeg right b t (sourceProfile epsilon precision)))

theorem preparedMixed_generated (epsilon : ℝ) (precision : 0<epsilon) (f g : Field289) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (fun r : ℝ=>preparedVertex epsilon precision g p k F z w left right a s b t (r • f))
      (preparedMixed epsilon precision f g p k F z w left right a s b t) 0 :=
  PreparationVacuumFullFieldRiesz.paired_derivative (mixedVertex_generated f g p k F z w hz hw) _ _

def sourceMixedBilinear (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : Field289→ₗ[ℝ] Field289→ₗ[ℝ] ℂ where
  toFun f:= {
    toFun g:=preparedMixed epsilon precision f g p k F z w left right a s b t
    map_add' g g':=by simp only [preparedMixed,mixedVertex_add_right,add_apply,inner_add_right]
    map_smul' c g:=by simp only [preparedMixed,mixedVertex_smul_right,smul_apply,inner_smul_right_eq_smul,RingHom.id_apply]
  }
  map_add' f f':=by
    apply LinearMap.ext;intro g
    change preparedMixed epsilon precision (f+f') g p k F z w left right a s b t=
      preparedMixed epsilon precision f g p k F z w left right a s b t+
      preparedMixed epsilon precision f' g p k F z w left right a s b t
    simp only [preparedMixed,mixedVertex_add_left,add_apply,inner_add_right]
  map_smul' c f:=by
    apply LinearMap.ext;intro g
    change preparedMixed epsilon precision (c • f) g p k F z w left right a s b t=
      c • preparedMixed epsilon precision f g p k F z w left right a s b t
    simp only [preparedMixed,mixedVertex_smul_left,smul_apply,inner_smul_right_eq_smul]

def mixedCurvatureMatrix (epsilon : ℝ) (precision : 0<epsilon) (qLeft qRight : Fin 4→ℂ)
    (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : Matrix (Fin 36) (Fin 36) ℂ:=
  fun i j=>preparedMixed epsilon precision (readerReal qLeft i) (readerReal qRight j) p k F z w left right a s b t+
    Complex.I*preparedMixed epsilon precision (readerImag qLeft i) (readerReal qRight j) p k F z w left right a s b t+
    Complex.I*preparedMixed epsilon precision (readerReal qLeft i) (readerImag qRight j) p k F z w left right a s b t-
    preparedMixed epsilon precision (readerImag qLeft i) (readerImag qRight j) p k F z w left right a s b t

def curvatureVertexCurve (epsilon : ℝ) (precision : 0<epsilon) (qLeft qRight : Fin 4→ℂ)
    (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) (i j : Fin 36) (r : ℝ) : ℂ:=
  preparedVertex epsilon precision (readerReal qRight j) p k F z w left right a s b t (r • readerReal qLeft i)+
    Complex.I*preparedVertex epsilon precision (readerReal qRight j) p k F z w left right a s b t (r • readerImag qLeft i)+
    Complex.I*preparedVertex epsilon precision (readerImag qRight j) p k F z w left right a s b t (r • readerReal qLeft i)-
    preparedVertex epsilon precision (readerImag qRight j) p k F z w left right a s b t (r • readerImag qLeft i)

theorem mixedCurvatureMatrix_generated (epsilon : ℝ) (precision : 0<epsilon) (qLeft qRight : Fin 4→ℂ)
    (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (a s b t : Fin 2) (i j : Fin 36) :
    HasDerivAt (curvatureVertexCurve epsilon precision qLeft qRight p k F z w left right a s b t i j)
      (mixedCurvatureMatrix epsilon precision qLeft qRight p k F z w left right a s b t i j) 0 :=by
  have rr:=preparedMixed_generated epsilon precision (readerReal qLeft i) (readerReal qRight j) p k F z w hz hw left right a s b t
  have ir:=preparedMixed_generated epsilon precision (readerImag qLeft i) (readerReal qRight j) p k F z w hz hw left right a s b t
  have ri:=preparedMixed_generated epsilon precision (readerReal qLeft i) (readerImag qRight j) p k F z w hz hw left right a s b t
  have ii:=preparedMixed_generated epsilon precision (readerImag qLeft i) (readerImag qRight j) p k F z w hz hw left right a s b t
  exact ((rr.add (ir.const_mul Complex.I)).add (ri.const_mul Complex.I)).sub ii

end LowEnergy.PreparationVacuumJointFieldResponse
