import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCausalCurrentHalf

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumCausalPoleResponse
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalZeroRead
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumGaugeSourceInjection
open PreparationVacuumFullOriginResponse
open PreparationVacuumFullPoleContinuation PreparationVacuumSharedPoleCarrier PreparationVacuumSoftPoleSelection
open SourcePropagationNativeActionHessian Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourcePoleCurrentHalf sourcePoleCurrentWindow sourceGreen sourceField actualCurrent

def returnedHalfCurrent (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (l r : RestStateIndex)
    (lambda : ℂ) : Fin 289→ℂ:=fun i=>
  (movingOverlap pL*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>sourcePoleCurrentHalf q pL pR a b lambda i)*
    (movingOverlap pR).conjTranspose) l r

set_option backward.isDefEq.respectTransparency false in
theorem returnedCurrent_halfAxis (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (l r : RestStateIndex)
    (lambda : ℂ) (positive : 0<lambda.re) :
    Tendsto (fun T=>returnedCurrentWindow q pL pR l r lambda T) atTop (𝓝 (returnedHalfCurrent q pL pR l r lambda)):=by
  apply tendsto_pi_nhds.mpr
  intro i
  have current : Tendsto (fun T=>(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>actualCurrent q pL pR a b lambda T i)) atTop
      (𝓝 (show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>sourcePoleCurrentHalf q pL pR a b lambda i)):=
    tendsto_pi_nhds.mpr (fun a=>tendsto_pi_nhds.mpr (fun b=>by simpa only [actualCurrent] using sourcePoleCurrentWindow_halfAxis q pL pR a b lambda positive i))
  have read : Continuous (fun M : Matrix RestStateIndex RestStateIndex ℂ=>(movingOverlap pL*M*(movingOverlap pR).conjTranspose) l r):=by fun_prop
  have result:=read.tendsto _ |>.comp current
  simpa only [Function.comp_def,returnedCurrentWindow_tensor,returnedHalfCurrent] using result

def returnedCausalHalfField (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) : Fin 289→ℂ:=
  sourceField (causalPoint k frequency) (returnedHalfCurrent q (p-k) p l r frequency.val)

def returnedCausalWindowField (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) (T : ℝ) : Fin 289→ℂ:=
  sourceField (causalPoint k frequency) (returnedCurrentWindow q (p-k) p l r frequency.val T)

def returnedHalfCosource (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) : Fin 289→ℂ:=
  originalReadback (fixedMomentum k frequency.val)*ᵥreturnedHalfCurrent q (p-k) p l r frequency.val

theorem returnedCausalField_halfAxis (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) :
    Tendsto (returnedCausalWindowField q p k l r frequency) atTop (𝓝 (returnedCausalHalfField q p k l r frequency)):=by
  have read : Continuous (sourceField (causalPoint k frequency)):=by
    unfold sourceField
    exact continuous_const.matrix_mulVec continuous_id
  exact read.tendsto _ |>.comp (returnedCurrent_halfAxis q (p-k) p l r frequency.val frequency.property.1)

theorem returnedCausalHalfField_whole (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) :
    nativeFourierHessian nativeHessian (fixedMomentum k frequency.val)*ᵥreturnedCausalHalfField q p k l r frequency=
      returnedHalfCurrent q (p-k) p l r frequency.val-originalRowLift (fixedMomentum k frequency.val)*ᵥ
        (nullProjection*ᵥreturnedHalfCosource q p k l r frequency):=by
  rw [returnedCausalHalfField,nativeActionFourierHessian_original]
  exact original_forced_field (causalPoint k frequency) _

set_option backward.isDefEq.respectTransparency false in
private theorem read_transfer (M : Matrix (Fin 289) (Fin 289) ℂ)
    (U V : Matrix RestStateIndex RestStateIndex ℂ) (F : RestStateIndex→RestStateIndex→Fin 289→ℂ)
    (l r : RestStateIndex) :
    M*ᵥ(fun i=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>F a b i)*V) l r)=fun i=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>(M*ᵥF a b) i)*V) l r:=by
  funext i
  simp only [Matrix.mulVec,Matrix.mul_apply,dotProduct,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

def returnedCausalCosource (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) (T : ℝ) : Fin 289→ℂ:=fun i=>
  (movingOverlap (p-k)*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>
    sourceActualCurrentCosource q (p-k) p a b (physicalSpatial k) frequency.val T i)*(movingOverlap p).conjTranspose) l r

theorem returnedCausalCurrent_ward (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) (T : ℝ) :
    originalReadback (fixedMomentum k frequency.val)*ᵥreturnedCurrentWindow q (p-k) p l r frequency.val T=
      returnedCausalCosource q p k l r frequency T:=by
  have current : returnedCurrentWindow q (p-k) p l r frequency.val T=fun i=>
      (movingOverlap (p-k)*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>
        sourcePoleCurrentWindow q (p-k) p a b frequency.val T i)*(movingOverlap p).conjTranspose) l r:=by
    funext i
    simpa only [actualCurrent] using returnedCurrentWindow_tensor q (p-k) p l r frequency.val T i
  rw [current,read_transfer]
  simp only [fixedMomentum,sourceActualCurrentWindow_ward]
  rfl

theorem returnedCausalCosource_halfAxis (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) :
    Tendsto (returnedCausalCosource q p k l r frequency) atTop (𝓝 (returnedHalfCosource q p k l r frequency)):=by
  have read : Continuous (fun f : Fin 289→ℂ=>originalReadback (fixedMomentum k frequency.val)*ᵥf):=
    continuous_const.matrix_mulVec continuous_id
  have result:=read.tendsto _ |>.comp (returnedCurrent_halfAxis q (p-k) p l r frequency.val frequency.property.1)
  simp only [Function.comp_def,returnedCausalCurrent_ward] at result
  exact result

/-- This total expression is used only for continuity; legal source points return the original Green exactly. -/
def originalGreenExpression (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  originalChange p*(contactInverse p+activeProjection*(extendedKernel p)⁻¹)*originalReadback p

theorem originalGreenExpression_actual (p : regularSource) : originalGreenExpression p.val=sourceGreen p:=by unfold sourceGreen; rfl

private theorem sourceMatrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms):=by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix:=by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value;fun_prop
      · exact continuous_const
    exact term.add ih

private theorem extendedKernel_continuous : Continuous extendedKernel:=
  (sourceMatrix_continuous activeTerms).add continuous_const

private theorem originalGreenExpression_continuous_at (p : Fin 4→ℂ) (regular : p∈regularSource) :
    ContinuousAt originalGreenExpression p:=by
  have inverse : ContinuousAt (fun v=>(extendedKernel v)⁻¹) p:=
    (continuousAt_matrix_inv _ (by simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ (isUnit_iff_ne_zero.mp regular)))).tendsto.comp extendedKernel_continuous.continuousAt.tendsto
  have change : Continuous originalChange:=sourceMatrix_continuous originalChangeTerms
  have contact : Continuous contactInverse:=sourceMatrix_continuous contactInverseTerms
  have read : Continuous originalReadback:= (change.comp continuous_neg).matrix_transpose
  exact (change.continuousAt.mul (contact.continuousAt.add (continuousAt_const.mul inverse))).mul read.continuousAt

private theorem causalMomentum_continuous (omega : ℝ) (k : PhysicalMomentum) :
    Continuous (fun eta : ℝ=>causalMomentum eta omega k):=by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change Continuous (fun eta : ℝ=>(eta:ℂ)-Complex.I*(omega:ℂ))
    fun_prop
  · exact continuous_const

def returnedDampedField (q : PhysicalResponsePoint) (epsilon s : ℝ) (n : PhysicalMomentum)
    (l r : RestStateIndex) (T eta : ℝ) : Fin 289→ℂ:=
  originalGreenExpression (causalMomentum eta (sourceFrequency epsilon s) (epsilon^2 • n))*ᵥ
    returnedCurrentWindow q (sheetLeft epsilon n 0) 0 l r (causalLambda eta (sourceFrequency epsilon s)) T

private theorem returnedDampedField_continuous_at (q : PhysicalResponsePoint) (epsilon s : ℝ) (n : PhysicalMomentum)
    (l r : RestStateIndex) (T : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0)
    (regular : frequencyRay epsilon s n∈regularSource) :
    ContinuousAt (returnedDampedField q epsilon s n l r T) 0:=by
  have center : causalMomentum 0 (sourceFrequency epsilon s) (epsilon^2 • n)∈regularSource:=by
    rw [causalMomentum_zero]
    exact regular
  have green : ContinuousAt (fun eta : ℝ=>originalGreenExpression (causalMomentum eta (sourceFrequency epsilon s) (epsilon^2 • n))) 0:=
    (originalGreenExpression_continuous_at _ center).tendsto.comp
      ((causalMomentum_continuous (sourceFrequency epsilon s) (epsilon^2 • n)).tendsto 0)
  have frequency : Continuous (fun eta : ℝ=>causalLambda eta (sourceFrequency epsilon s)):=by unfold causalLambda;fun_prop
  have path : Continuous (fun eta : ℝ=>(sheetLeft epsilon n 0,(0:PhysicalMomentum),causalLambda eta (sourceFrequency epsilon s))):=
    continuous_const.prodMk (continuous_const.prodMk frequency)
  have current := (returnedCurrentWindow_joint_continuous q l r T nonrealL nonrealR).comp path
  exact (continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (green.tendsto.prodMk_nhds current.continuousAt.tendsto)

/-- Removing damping at finite time returns the already generated physical response; no interchange with the half-axis limit occurs. -/
theorem returnedDampedField_boundary (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ∀ᶠ (e : scaleDomain) in scaleApproach,∀ᶠ (s : ℝ) in 𝓝[≠] (sourceSheet branch n unit e.val),
      Tendsto (returnedDampedField q e.val s n l r T) (𝓝[>] (0:ℝ)) (𝓝 (returnedSheetField q e.val s n l r T)):=by
  filter_upwards [returnedSheetField_original q branch n unit l r T] with e near
  filter_upwards [near] with s source
  obtain ⟨point,coordinate,field⟩:=source
  have regular : frequencyRay e.val s n∈regularSource:=coordinate ▸ point.property
  have result := (returnedDampedField_continuous_at q e.val s n l r T nonrealL nonrealR regular).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have same : returnedDampedField q e.val s n l r T 0=returnedSheetField q e.val s n l r T:=by
    rw [field]
    unfold returnedDampedField
    rw [causalMomentum_zero,←coordinate,originalGreenExpression_actual]
    unfold sourceField returnedSheetCurrent causalLambda sheetLambda
    simp only [Complex.ofReal_zero,zero_sub,neg_mul]
  rw [same] at result
  exact result

private theorem causal_domain_near (epsilon s : ℝ) (n : PhysicalMomentum)
    (regular : frequencyRay epsilon s n∈regularSource) :
    ∀ᶠ eta in 𝓝 (0:ℝ),causalMomentum eta (sourceFrequency epsilon s) (epsilon^2 • n)∈regularSource:=by
  have nonzero : (extendedKernel (causalMomentum 0 (sourceFrequency epsilon s) (epsilon^2 • n))).det≠0:=by
    rw [causalMomentum_zero]
    exact isUnit_iff_ne_zero.mp regular
  have continuous : Continuous (fun eta : ℝ=>(extendedKernel (causalMomentum eta (sourceFrequency epsilon s) (epsilon^2 • n))).det):=
    (extendedKernel_continuous.comp (causalMomentum_continuous _ _)).matrix_det
  filter_upwards [continuous.continuousAt.eventually_ne nonzero] with eta nonzero
  exact isUnit_iff_ne_zero.mpr nonzero

set_option backward.isDefEq.respectTransparency false in
private theorem returnedDampedField_generated (q : PhysicalResponsePoint) (epsilon s : ℝ) (n : PhysicalMomentum)
    (l r : RestStateIndex) (eta : ℝ) (positive : 0<eta)
    (regular : causalMomentum eta (sourceFrequency epsilon s) (epsilon^2 • n)∈regularSource) :
    ∃frequency : CausalFrequency (epsilon^2 • n),frequency.val=causalLambda eta (sourceFrequency epsilon s) ∧
      ∀T,returnedDampedField q epsilon s n l r T eta=returnedCausalWindowField q (0:PhysicalMomentum) (epsilon^2 • n) l r frequency T:=by
  let frequency : CausalFrequency (epsilon^2 • n):=⟨causalLambda eta (sourceFrequency epsilon s),
    by rw [causalLambda_re];exact positive,regular⟩
  refine ⟨frequency,rfl,?_⟩
  intro T
  unfold returnedDampedField returnedCausalWindowField sourceField
  rw [←originalGreenExpression_actual]
  rfl

attribute [local irreducible] returnedDampedField returnedCausalWindowField returnedCausalHalfField originalGreenExpression

set_option backward.isDefEq.respectTransparency false in
/-- Both routes use the same damped source field: the finite-window boundary and the half-axis response. -/
theorem returnedDampedField_boundary_domain (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) :
    ∀ᶠ (e : scaleDomain) in scaleApproach,∀ᶠ (s : ℝ) in 𝓝[≠] (sourceSheet branch n unit e.val),∀ᶠ (eta : ℝ) in 𝓝[>] (0:ℝ),
      ∃frequency : CausalFrequency (e.val^2 • n),frequency.val=causalLambda eta (sourceFrequency e.val s) ∧
        ∀T,returnedDampedField q e.val s n l r T eta=returnedCausalWindowField q (0:PhysicalMomentum) (e.val^2 • n) l r frequency T:=by
  filter_upwards [sourceSheet_regular_near branch n unit] with e near
  filter_upwards [near] with s source
  obtain ⟨_,_,regular⟩:=source
  filter_upwards [(causal_domain_near e.val s n regular).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0),self_mem_nhdsWithin] with eta regular positive
  exact returnedDampedField_generated q e.val s n l r eta positive regular

set_option backward.isDefEq.respectTransparency false in
theorem returnedSheet_causal_half_response (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) :
    ∀ᶠ (e : scaleDomain) in scaleApproach,∀ᶠ (eta : ℝ) in 𝓝[>] (0:ℝ),
      ∃frequency : CausalFrequency (e.val^2 • n),frequency.val=causalLambda eta (sourceFrequency e.val (sourceSheet branch n unit e.val)) ∧
        Tendsto (fun T=>returnedDampedField q e.val (sourceSheet branch n unit e.val) n l r T eta) atTop
          (𝓝 (returnedCausalHalfField q (0:PhysicalMomentum) (e.val^2 • n) l r frequency)):=by
  filter_upwards [sourceSheet_causal_regular branch n unit] with e legal
  filter_upwards [legal,self_mem_nhdsWithin] with eta regular positive
  obtain ⟨frequency,coordinate,field⟩:=returnedDampedField_generated q e.val (sourceSheet branch n unit e.val) n l r eta positive regular
  refine ⟨frequency,coordinate,?_⟩
  have same : (fun T=>returnedDampedField q e.val (sourceSheet branch n unit e.val) n l r T eta)=
      returnedCausalWindowField q (0:PhysicalMomentum) (e.val^2 • n) l r frequency:=funext field
  rw [same]
  exact returnedCausalField_halfAxis q 0 (e.val^2 • n) l r frequency

end LowEnergy.PreparationVacuumCausalPoleResponse
