import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationActualMomentumPencil
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationCommonMomentum
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil SourcePropagationResolvent SourcePropagationSpectralAxis
open SourcePropagationFieldFeedback SourcePropagationNearFieldTime
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionFieldLift
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
abbrev Op:=SourcePropagationResolvent.Op
abbrev TransferOp:=SourcePropagationResolvent.TransferOp
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ TransferOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ Op:=ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℝ TransferOp:=ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ TransferOp:=by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=TransferOp)) using 1
local instance : ContinuousSMul ℝ TransferOp:=by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=TransferOp)) using 1
local instance : AddCommGroup TransferOp:=ContinuousLinearMap.addCommGroup
local instance : IsTopologicalAddGroup TransferOp:=by
  have normal : @IsTopologicalAddGroup TransferOp
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup.toAddGroup:=inferInstance
  convert! normal using 1
local instance : NormSMulClass ℂ Op:=by
  convert! (NormedSpace.toNormSMulClass (𝕜:=ℂ) (E:=Op)) using 1
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
attribute [local irreducible] jointGenerator jointCurrent jointResolvent
  sourceRead rawInitial actualResolvent evolutionGenerator propagationPencil sourceGreen
  originalJacobi originalChange originalReadback originalRowLift activeKernel contactInverse extendedKernel
  momentumCompressionMap momentumCompression responseLeft responseRight
  PreparationVacuumSourcePreparedResponse.sourceProfile

def transferPoint (q : PhysicalResponsePoint) (k : PhysicalMomentum) : PhysicalResponsePoint:={q with k:=k}

theorem transfer_read (q : PhysicalResponsePoint) (k : PhysicalMomentum) :
    sourceRead (transferPoint q k)=sourceRead q:=by
  unfold sourceRead responseLeft responseRight transferPoint
  rfl

theorem transfer_evolution_continuous (q : PhysicalResponsePoint) :
    Continuous (fun k : PhysicalMomentum=>evolutionGenerator (transferPoint q k)):=by
  have left : Continuous (fun k : PhysicalMomentum=>(-Complex.I) • jointGenerator (q.p+k) q.F 0 0):=
    ((jointGenerator_base_continuous q.F 0).comp
      ((continuous_const : Continuous (fun _ : PhysicalMomentum=>q.p)).add continuous_id)).const_smul (-Complex.I)
  have right : Continuous (fun _ : PhysicalMomentum=>(-Complex.I) • jointGenerator q.p q.F 0 0):=continuous_const
  have actual:=(ContinuousLinearMap.continuous (R₁:=ℂ) (R₂:=ℂ) (M₁:=Op×Op) (M₂:=TransferOp) evolutionMap).comp (left.prodMk right)
  convert! actual using 1
  funext k
  apply ContinuousLinearMap.ext
  intro A
  simp only [evolutionMap,evolutionGenerator_apply,leftGenerator,rightGenerator,transferPoint,
    add_apply,neg_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd',ContinuousLinearMap.mul_apply',ContinuousLinearMap.flip_apply,Function.comp_apply,neg_mul]
  convert! congrArg (fun B : Op=>B+A*((-Complex.I) • jointGenerator q.p q.F 0 0))
    (neg_mul (((-Complex.I) • jointGenerator (q.p+k) q.F 0 0):Op) A) using 1

theorem transfer_pencil_continuous (q : PhysicalResponsePoint) (lambda : ℂ) :
    Continuous (fun k : PhysicalMomentum=>propagationPencil (transferPoint q k) lambda):=by
  unfold propagationPencil
  exact continuous_const.sub (transfer_evolution_continuous q)

private theorem inverse_two_sides {R : Type*} [Ring R] (P A : R)
    (left : P*A=1) (right : A*P=1) : A=Ring.inverse P:=by
  have unit : IsUnit P:=⟨⟨P,A,left,right⟩,rfl⟩
  exact (left_inv_eq_right_inv (Ring.inverse_mul_cancel P unit) left).symm

theorem transfer_resolvent_inverse (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0)
    (k : PhysicalMomentum) :
    actualResolvent (transferPoint q k) lambda=Ring.inverse (propagationPencil (transferPoint q k) lambda):=by
  convert! inverse_two_sides (R:=TransferOp) _ _
    (actualResolvent_left (transferPoint q k) lambda off)
    (actualResolvent_right (transferPoint q k) lambda off) using 1

theorem transfer_resolvent_continuous (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    Continuous (fun k : PhysicalMomentum=>actualResolvent (transferPoint q k) lambda):=by
  apply continuous_iff_continuousAt.mpr
  intro k
  let u:=normBasePencilUnit (transferPoint q k) lambda off
  have atInverse : ContinuousAt (Ring.inverse : TransferOp→TransferOp)
      (propagationPencil (transferPoint q k) lambda):=by
    have actual:=(contDiffAt_ringInverse (𝕜:=ℝ) (R:=TransferOp) (n:=1) u).continuousAt
    convert! actual using 1
  have inner : ContinuousAt (fun t : PhysicalMomentum=>propagationPencil (transferPoint q t) lambda) k:=
    (transfer_pencil_continuous q lambda).continuousAt
  exact (atInverse.comp (f:=fun t : PhysicalMomentum=>propagationPencil (transferPoint q t) lambda)
    (x:=k) inner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t=>transfer_resolvent_inverse q lambda off t))

theorem transfer_material_continuous (q : PhysicalResponsePoint) (hz : q.z.im≠0) :
    Continuous (fun k : PhysicalMomentum=>jointResolvent (q.p+k) q.F q.z 0):=by
  apply continuous_iff_continuousAt.mpr
  intro k
  obtain ⟨u,hu⟩:=jointGenerator_unit (q.p+k) q.F q.z hz
  have atInverse : ContinuousAt (Ring.inverse : Op→Op) (jointGenerator (q.p+k) q.F q.z 0):=by
    rw [←hu]
    exact (contDiffAt_ringInverse ℝ (n:=1) u).continuousAt
  have inner : ContinuousAt (fun t : PhysicalMomentum=>jointGenerator (q.p+t) q.F q.z 0) k:=
    ((jointGenerator_base_continuous q.F q.z).comp
      ((continuous_const : Continuous (fun _ : PhysicalMomentum=>q.p)).add continuous_id)).continuousAt
  have actual:=atInverse.comp (f:=fun t : PhysicalMomentum=>jointGenerator (q.p+t) q.F q.z 0) (x:=k) inner
  convert! actual using 1
  funext t
  unfold jointResolvent
  rfl

theorem transfer_rawInitial_continuous (q : PhysicalResponsePoint) (hz : q.z.im≠0) (reader : Field289) :
    Continuous (fun k : PhysicalMomentum=>rawInitial (transferPoint q k) reader):=by
  have actual:=(transfer_material_continuous q hz).mul_const (rawReader reader q.p q.F 0)
    |>.mul_const (jointResolvent q.p q.F q.w 0)
  convert! actual using 1
  funext k
  unfold rawInitial transferPoint
  rfl

/-- Both source inverse and material preparation retain their true carriers. -/
def momentumPreparedOperator (q : PhysicalResponsePoint) (lambda : ℂ) (reader : Field289)
    (k : PhysicalMomentum) : Op:=
  actualResolvent (transferPoint q k) lambda (rawInitial (transferPoint q k) reader)

theorem momentumPreparedOperator_continuous (q : PhysicalResponsePoint) (lambda : ℂ)
    (off : lambda.re≠0) (hz : q.z.im≠0) (reader : Field289) :
    Continuous (momentumPreparedOperator q lambda reader):=
  (transfer_resolvent_continuous q lambda off).clm_apply (transfer_rawInitial_continuous q hz reader)

def momentumSource (q : PhysicalResponsePoint) (lambda : ℂ) (k : PhysicalMomentum) : Fin 289→ℂ:=
  fun i=>-sourceRead q (momentumPreparedOperator q lambda (fieldUnit i) k)

theorem momentumSource_continuous (q : PhysicalResponsePoint) (lambda : ℂ)
    (off : lambda.re≠0) (hz : q.z.im≠0) : Continuous (momentumSource q lambda):=by
  apply continuous_pi
  intro i
  exact ((sourceRead q).continuous.comp (momentumPreparedOperator_continuous q lambda off hz (fieldUnit i))).neg

theorem momentumSource_actual (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (k : PhysicalMomentum) :
    momentumSource q lambda k=halfForcing (transferPoint q k) 0 false lambda:=by
  rw [←axisSource_future (transferPoint q k) 0 false lambda positive]
  ext i
  simp only [momentumSource,momentumPreparedOperator,axisSource,axisPreparedOperator,Bool.false_eq_true,
    ↓reduceIte,transfer_read]

private theorem complex_drive {V : Type*} [AddCommGroup V] [Module ℂ V] (A B : V) :
    -((-Complex.I) • A)+(-Complex.I) • B=Complex.I • (A-B):=by
  simp [smul_sub,sub_eq_add_neg]

theorem transfer_identity_drive (q : PhysicalResponsePoint) (k : PhysicalMomentum) :
    evolutionGenerator (transferPoint q k) (1:Op)=Complex.I • momentumCompressionMap q.F k:=by
  rw [evolutionGenerator_apply]
  simp only [leftGenerator,rightGenerator,transferPoint,one_mul,mul_one]
  have algebra:=complex_drive (V:=Op) (jointGenerator (q.p+k) q.F 0 0) (jointGenerator q.p q.F 0 0)
  rw [algebra,jointGenerator_momentum_difference]

private theorem kernel_resolvent_algebra {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R L : E→L[ℂ] E) (lambda : ℂ) (nonzero : lambda≠0)
    (right : R*(lambda • ContinuousLinearMap.id ℂ E-L)=1) (x : E) :
    R x-lambda⁻¹ • x=lambda⁻¹ • R (L x):=by
  have applied:=congrArg (fun T : E→L[ℂ] E=>T x) right
  have equation : lambda • R x-R (L x)=x:=by
    simpa only [mul_apply_eq_comp,sub_apply,smul_apply,ContinuousLinearMap.id_apply,map_sub,map_smul,one_apply_eq_self] using applied
  have solved:=congrArg (fun y : E=>lambda⁻¹ • y) equation
  simp only [smul_sub,smul_smul,inv_mul_cancel₀ nonzero,one_smul] at solved
  exact sub_eq_iff_eq_add.mpr (sub_eq_iff_eq_add.mp solved |>.trans (add_comm _ _))

/-- The small-transfer drive of the actual zero mode is produced by the source momentum action. -/
theorem transfer_identity_response (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0)
    (k : PhysicalMomentum) :
    actualResolvent (transferPoint q k) lambda (1:Op)-lambda⁻¹ • (1:Op)=
      lambda⁻¹ • actualResolvent (transferPoint q k) lambda (Complex.I • momentumCompressionMap q.F k):=by
  have nonzero : lambda≠0:=fun h=>off (by rw [h];rfl)
  have right : actualResolvent (transferPoint q k) lambda*
      (lambda • ContinuousLinearMap.id ℂ Op-evolutionGenerator (transferPoint q k))=1:=by
    simpa only [propagationPencil] using actualResolvent_right (transferPoint q k) lambda off
  have actual:=kernel_resolvent_algebra
    (actualResolvent (transferPoint q k) lambda) (evolutionGenerator (transferPoint q k)) lambda nonzero
    right (1:Op)
  rw [transfer_identity_drive] at actual
  exact actual

private theorem kernel_price {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    (R : E→L[ℂ] E) (M : D→L[ℝ] E) (k : D) (lambda : ℂ) :
    ‖lambda⁻¹ • R (Complex.I • M k)‖≤‖lambda⁻¹‖*‖R‖*‖M‖*‖k‖:=by
  have scaled : ‖Complex.I • M k‖≤‖M k‖:=by
    simpa only [Complex.norm_I,one_mul] using norm_smul_le Complex.I (M k)
  have argument:=scaled.trans (M.le_opNorm k)
  have applied:=(R.le_opNorm _).trans (mul_le_mul_of_nonneg_left argument (norm_nonneg R))
  exact (norm_smul_le _ _).trans
    ((mul_le_mul_of_nonneg_left applied (norm_nonneg _)).trans_eq (by ring))

theorem transfer_identity_error (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0)
    (k : PhysicalMomentum) :
    ‖actualResolvent (transferPoint q k) lambda (1:Op)-lambda⁻¹ • (1:Op)‖≤
      ‖lambda⁻¹‖*‖actualResolvent (transferPoint q k) lambda‖*‖momentumCompressionMap q.F‖*‖k‖:=by
  rw [transfer_identity_response q lambda off k]
  convert! kernel_price (E:=Op) (D:=PhysicalMomentum) (actualResolvent (transferPoint q k) lambda)
    (momentumCompressionMap q.F) k lambda using 1

private theorem pair_read_identity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x y : E) :
    ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ E y)) (1:E→L[ℂ] E)=inner ℂ x y:=rfl

private theorem actual_read_identity (q : PhysicalResponsePoint) :
    sourceRead q (1:Op)=inner ℂ (responseLeft q) (responseRight q):=by
  unfold sourceRead
  exact pair_read_identity (E:=H) (responseLeft q) (responseRight q)

private theorem read_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (read : E→L[ℂ] ℂ) (A B C : E) (lambda : ℂ)
    (actual : A-lambda⁻¹ • B=lambda⁻¹ • C) :
    read A-lambda⁻¹*read B=lambda⁻¹*read C:=by
  simpa only [map_sub,map_smul,smul_eq_mul] using congrArg read actual

private theorem read_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (read : E→L[ℂ] ℂ) (A B : E) (lambda : ℂ) :
    ‖read A-lambda⁻¹*read B‖≤‖read‖*‖A-lambda⁻¹ • B‖:=by
  have actual:=read.le_opNorm (A-lambda⁻¹ • B)
  simpa only [map_sub,map_smul,smul_eq_mul] using actual

theorem transfer_identity_visible_read (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0)
    (k : PhysicalMomentum) :
    sourceRead q (actualResolvent (transferPoint q k) lambda (1:Op))-
      lambda⁻¹*inner ℂ (responseLeft q) (responseRight q)=
      lambda⁻¹*sourceRead q (actualResolvent (transferPoint q k) lambda (Complex.I • momentumCompressionMap q.F k)):=by
  have identity:=actual_read_identity q
  rw [←identity]
  exact read_difference (E:=Op) (sourceRead q) (actualResolvent (transferPoint q k) lambda (1:Op))
    (1:Op) (actualResolvent (transferPoint q k) lambda (Complex.I • momentumCompressionMap q.F k)) lambda
    (transfer_identity_response q lambda off k)

theorem transfer_identity_visible_error (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0)
    (k : PhysicalMomentum) :
    ‖sourceRead q (actualResolvent (transferPoint q k) lambda (1:Op))-
      lambda⁻¹*inner ℂ (responseLeft q) (responseRight q)‖≤
      ‖sourceRead q‖*‖lambda⁻¹‖*‖actualResolvent (transferPoint q k) lambda‖*
        ‖momentumCompressionMap q.F‖*‖k‖:=by
  have identity:=actual_read_identity q
  rw [←identity]
  exact (read_price (E:=Op) (sourceRead q) (actualResolvent (transferPoint q k) lambda (1:Op)) (1:Op) lambda).trans
    ((mul_le_mul_of_nonneg_left (transfer_identity_error q lambda off k) (norm_nonneg _)).trans_eq (by ring))

private theorem sourceMatrix_continuous (ts : List SourceTerm) : Continuous (sourceMatrix ts):=by
  induction ts with
  | nil=>change Continuous (fun _ : Fin 4→ℂ=>(0:Matrix (Fin 289) (Fin 289) ℂ));exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix:=by
      apply continuous_matrix
      intro i j
      unfold SourceTerm.matrix Matrix.single Powers.value
      simp only [Matrix.of_apply]
      split_ifs <;> fun_prop
    have same : sourceMatrix (a::rest)=fun p=>a.matrix p+sourceMatrix rest p:=funext (sourceMatrix_cons a rest)
    rw [same]
    exact term.add ih

private theorem originalChange_continuous : Continuous originalChange:=by
  unfold originalChange
  exact sourceMatrix_continuous _

private theorem originalReadback_continuous : Continuous originalReadback:=by
  have actual:=(sourceMatrix_continuous originalChangeTerms).comp continuous_neg
  unfold originalReadback originalChange
  exact actual.matrix_transpose

private theorem extendedKernel_continuous : Continuous extendedKernel:=by
  unfold extendedKernel activeKernel
  exact (sourceMatrix_continuous activeTerms).add continuous_const

private def completeGreen (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  originalChange p*(contactInverse p+activeProjection*(extendedKernel p)⁻¹)*originalReadback p

private theorem completeGreen_continuousAt (p : regularSource) : ContinuousAt completeGreen p.val:=by
  obtain ⟨u,hu⟩:=p.property
  have determinant : ContinuousAt (Ring.inverse : ℂ→ℂ) (extendedKernel p.val).det:=by
    rw [←hu]
    exact (contDiffAt_ringInverse ℝ (n:=1) u).continuousAt
  have inverse:=(continuousAt_matrix_inv (extendedKernel p.val) determinant).comp
    (f:=extendedKernel) (x:=p.val) extendedKernel_continuous.continuousAt
  have contact : Continuous contactInverse:=by
    unfold contactInverse
    exact sourceMatrix_continuous _
  exact (originalChange_continuous.continuousAt.mul
    (contact.continuousAt.add (continuousAt_const.mul inverse))).mul originalReadback_continuous.continuousAt

def momentumDomain (lambda : ℂ) : Set PhysicalMomentum:=
  {k | fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda∈regularSource}

private theorem originalMomentum_continuous (lambda : ℂ) :
    Continuous (fun k : PhysicalMomentum=>fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda):=by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_const
  · change Continuous (fun k : PhysicalMomentum=>Complex.I*(k j:ℂ))
    fun_prop

theorem momentumDomain_source_near (lambda : physicalSpectralDomain 0) :
    ∀ᶠk in 𝓝 (0:PhysicalMomentum),k∈momentumDomain lambda.val:=by
  have continuous:=((extendedKernel_continuous.comp (originalMomentum_continuous lambda.val)).matrix_det).continuousAt (x:=0)
  have nonzero : (extendedKernel (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial 0) lambda.val)).det≠0:=
    isUnit_iff_ne_zero.mp lambda.property
  have near:=continuous.eventually_ne nonzero
  exact near.mono (fun k hk=>isUnit_iff_ne_zero.mpr hk)

def momentumBase (lambda : physicalSpectralDomain 0) : momentumDomain lambda.val:=⟨0,lambda.property⟩

/-- This is the original field Green on its genuine generated momentum domain. -/
def actualMomentumField (q : PhysicalResponsePoint) (lambda : ℂ) (k : momentumDomain lambda) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k.val) lambda,k.property⟩
    (momentumSource q lambda k.val)

theorem actualMomentumField_actual (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (k : momentumDomain lambda) :
    actualMomentumField q lambda k=halfField (transferPoint q k.val) 0 false k.val ⟨lambda,k.property⟩:=by
  unfold actualMomentumField halfField
  rw [momentumSource_actual q lambda positive k.val]

theorem actualMomentumField_equation (q : PhysicalResponsePoint) (lambda : ℂ) (k : momentumDomain lambda) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k.val) lambda)*ᵥactualMomentumField q lambda k=
      momentumSource q lambda k.val-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k.val) lambda)*ᵥsourceCompatibility
          (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k.val) lambda) (momentumSource q lambda k.val):=by
  exact original_forced_field
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k.val) lambda,k.property⟩
    (momentumSource q lambda k.val)

theorem actualMomentumField_small_transfer (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain 0)
    (off : lambda.val.re≠0) (hz : q.z.im≠0) :
    Tendsto (actualMomentumField q lambda.val) (𝓝 (momentumBase lambda))
      (𝓝 (actualMomentumField q lambda.val (momentumBase lambda))):=by
  have projection : Continuous (fun k : momentumDomain lambda.val=>k.val):=continuous_subtype_val
  have scalar:=((momentumSource_continuous q lambda.val off hz).comp projection).continuousAt (x:=momentumBase lambda)
  have matrix:=((completeGreen_continuousAt
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial 0) lambda.val,lambda.property⟩).comp
      (f:=fun k : momentumDomain lambda.val=>fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k.val) lambda.val)
      (x:=momentumBase lambda) ((originalMomentum_continuous lambda.val).comp projection).continuousAt)
  have actual : Tendsto (fun k : momentumDomain lambda.val=>
      completeGreen (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k.val) lambda.val)*ᵥ
        momentumSource q lambda.val k.val) (𝓝 (momentumBase lambda))
      (𝓝 (completeGreen (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (momentumBase lambda).val) lambda.val)*ᵥ
        momentumSource q lambda.val (momentumBase lambda).val)):=by
    apply tendsto_pi_nhds.mpr
    intro row
    unfold Matrix.mulVec dotProduct
    apply tendsto_finsetSum
    intro i _
    exact ((matrix.tendsto.apply_nhds row).apply_nhds i).mul (scalar.tendsto.apply_nhds i)
  convert! actual using 1
  all_goals first
    | (funext k;unfold actualMomentumField PreparationVacuumOriginalGreenFeedback.sourceField sourceGreen completeGreen;rfl)
    | (unfold actualMomentumField PreparationVacuumOriginalGreenFeedback.sourceField sourceGreen completeGreen;rfl)

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row0_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 0 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row1_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 1 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row2_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 2 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row3_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 3 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row4_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 4 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row5_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 5 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row6_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 6 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row7_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 7 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row8_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 8 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row9_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 9 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row10_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 10 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row11_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 11 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row12_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 12 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row13_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 13 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row14_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 14 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row15_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 15 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row16_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 16 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row17_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 17 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row18_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 18 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row19_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 19 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row20_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 20 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row21_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 21 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row22_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 22 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row23_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 23 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row24_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 24 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row25_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 25 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row26_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 26 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row27_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 27 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row28_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 28 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row29_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 29 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row30_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 30 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row31_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 31 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row32_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 32 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row33_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 33 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row34_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 34 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

set_option backward.isDefEq.respectTransparency true in
private theorem originalReader36_row35_continuous (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p 35 column):=by
  fin_cases column <;> dsimp only [originalReader36] <;> fun_prop

private theorem originalReader36_continuous (row : Fin 36) (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p row column):=by
  fin_cases row

  · exact originalReader36_row0_continuous column

  · exact originalReader36_row1_continuous column

  · exact originalReader36_row2_continuous column

  · exact originalReader36_row3_continuous column

  · exact originalReader36_row4_continuous column

  · exact originalReader36_row5_continuous column

  · exact originalReader36_row6_continuous column

  · exact originalReader36_row7_continuous column

  · exact originalReader36_row8_continuous column

  · exact originalReader36_row9_continuous column

  · exact originalReader36_row10_continuous column

  · exact originalReader36_row11_continuous column

  · exact originalReader36_row12_continuous column

  · exact originalReader36_row13_continuous column

  · exact originalReader36_row14_continuous column

  · exact originalReader36_row15_continuous column

  · exact originalReader36_row16_continuous column

  · exact originalReader36_row17_continuous column

  · exact originalReader36_row18_continuous column

  · exact originalReader36_row19_continuous column

  · exact originalReader36_row20_continuous column

  · exact originalReader36_row21_continuous column

  · exact originalReader36_row22_continuous column

  · exact originalReader36_row23_continuous column

  · exact originalReader36_row24_continuous column

  · exact originalReader36_row25_continuous column

  · exact originalReader36_row26_continuous column

  · exact originalReader36_row27_continuous column

  · exact originalReader36_row28_continuous column

  · exact originalReader36_row29_continuous column

  · exact originalReader36_row30_continuous column

  · exact originalReader36_row31_continuous column

  · exact originalReader36_row32_continuous column

  · exact originalReader36_row33_continuous column

  · exact originalReader36_row34_continuous column

  · exact originalReader36_row35_continuous column

def actualMomentumCurvature (q : PhysicalResponsePoint) (lambda : ℂ) (k : momentumDomain lambda) : Fin 36→ℂ:=
  fun row=>∑i : Fin 289,originalReader36
    (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k.val) lambda) row i*actualMomentumField q lambda k i

theorem actualMomentumCurvature_small_transfer (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain 0)
    (off : lambda.val.re≠0) (hz : q.z.im≠0) :
    Tendsto (actualMomentumCurvature q lambda.val) (𝓝 (momentumBase lambda))
      (𝓝 (actualMomentumCurvature q lambda.val (momentumBase lambda))):=by
  apply tendsto_pi_nhds.mpr
  intro row
  unfold actualMomentumCurvature
  apply tendsto_finsetSum
  intro i _
  have projection : Continuous (fun k : momentumDomain lambda.val=>k.val):=continuous_subtype_val
  have reader:=(((originalReader36_continuous row i).comp (originalMomentum_continuous lambda.val)).comp
    projection).continuousAt (x:=momentumBase lambda) |>.tendsto
  exact reader.mul ((actualMomentumField_small_transfer q lambda off hz).apply_nhds i)

theorem actualMomentumCurvature_actual (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (k : momentumDomain lambda) :
    actualMomentumCurvature q lambda k=curvatureReturn (transferPoint q k.val) 0 false ⟨lambda,k.property⟩:=by
  have source:=axisField_curvature_future (transferPoint q k.val) 0 false ⟨lambda,k.property⟩ positive
  rw [axisField_future (transferPoint q k.val) 0 false ⟨lambda,k.property⟩ positive] at source
  unfold actualMomentumCurvature
  rw [actualMomentumField_actual q lambda positive k]
  convert! source using 1


end LowEnergy.SourcePropagationCommonMomentum
