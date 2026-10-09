import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationFullFiveLeading
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationConstrainedPoleReturn
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPropagationPencil
open SourcePropagationAlgebraicResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFieldConstraintResponse PreparationVacuumActionFieldLift
open Filter
open scoped Topology BigOperators Matrix
abbrev FieldMatrix:=Matrix (Fin 289) (Fin 289) ℂ
attribute [local irreducible] originalJacobi originalChange contactInverse activeKernel
  originalReadback originalRowLift PreparationVacuumOriginalGreenFeedback.sourceField sourceGreen sourceCompatibility
  sourcePoleOrder rationalSource normalizedPreparedSource preparedLeadingSource

def originalFieldDenominator (p : Fin 4→ℂ) : ℂ:=(extendedKernel p).det

def originalClearedGreen (p : Fin 4→ℂ) : FieldMatrix:=
  originalChange p*(originalFieldDenominator p • contactInverse p+
    activeProjection*(extendedKernel p).adjugate)*originalReadback p

private theorem clear_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (S C P K N : Matrix n n ℂ) (regular : K.det≠0) :
    K.det • (S*(C+P*K⁻¹)*N)=S*(K.det • C+P*K.adjugate)*N:=by
  calc
    _=S*(K.det • (C+P*K⁻¹))*N:=by rw [←smul_mul_assoc,←mul_smul_comm]
    _=S*(K.det • C+P*(K.det • K⁻¹))*N:=by rw [smul_add,mul_smul_comm]
    _=S*(K.det • C+P*K.adjugate)*N:=by
      rw [Matrix.inv_def,Ring.inverse_eq_inv,smul_smul,mul_inv_cancel₀ regular,one_smul]

theorem originalGreen_denominator (p : regularSource) :
    originalFieldDenominator p.val • sourceGreen p=originalClearedGreen p.val:=by
  unfold originalClearedGreen originalFieldDenominator sourceGreen
  exact clear_inverse (originalChange p.val) (contactInverse p.val) activeProjection
    (extendedKernel p.val) (originalReadback p.val) (isUnit_iff_ne_zero.mp p.property)

private theorem cleared_green_algebra {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (H S C P K N L J A Z B : R) (d : ℂ)
    (contact : H*S*C=L*J) (active : H*S*P=L*A)
    (extension : P*K=A) (adjugate : K*B=d • (1:R))
    (partition : J+P=1-Z) (row : L*N=1) :
    H*(S*(d • C+P*B)*N)=d • (1-L*Z*N):=by
  calc
    _=(d • (H*S*C)+(H*S*P)*B)*N:=by
      simp only [mul_add,mul_smul_comm,smul_mul_assoc]
      noncomm_ring
    _=(d • (L*J)+(L*A)*B)*N:=by rw [contact,active]
    _=(d • (L*J)+d • (L*P))*N:=by
      rw [←extension,mul_assoc,mul_assoc,adjugate,mul_smul_comm,mul_one,mul_smul_comm]
    _=d • (L*(J+P)*N):=by
      rw [←smul_add,←mul_add,smul_mul_assoc]
    _=d • (1-L*Z*N):=by rw [partition,mul_sub,mul_one,sub_mul,row]

theorem originalClearedGreen_equation (p : Fin 4→ℂ) :
    originalJacobi p*originalClearedGreen p=
      originalFieldDenominator p • (1-originalRowLift p*nullProjection*originalReadback p):=by
  have partition : contactProjection+activeProjection=1-nullProjection:=by
    rw [eq_sub_iff_add_eq]
    exact projection_partition
  unfold originalClearedGreen originalFieldDenominator
  exact cleared_green_algebra (R:=FieldMatrix) (originalJacobi p) (originalChange p)
    (contactInverse p) activeProjection (extendedKernel p) (originalReadback p)
    (originalRowLift p) contactProjection (activeKernel p) nullProjection
    (extendedKernel p).adjugate (extendedKernel p).det
    (original_contact_intertwiner p) (original_active_intertwiner p)
    (original_active_extended p) (Matrix.mul_adjugate _) partition (original_row_readback p)

private theorem term_continuous (term : SourceTerm) : Continuous term.matrix:=by
  apply continuous_matrix
  intro i j
  simp only [SourceTerm.matrix,Matrix.single_apply]
  split_ifs
  · unfold Powers.value
    fun_prop
  · exact continuous_const

private theorem matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms):=by
  induction terms with
  | nil=>
    convert! (continuous_const : Continuous (fun _ : Fin 4→ℂ=>(0:FieldMatrix))) using 1

  | cons term terms ih=>
    convert! (term_continuous term).add ih using 1


private theorem originalChange_continuous : Continuous originalChange:=by
  unfold originalChange
  exact matrix_continuous originalChangeTerms
private theorem contactInverse_continuous : Continuous contactInverse:=by
  unfold contactInverse
  exact matrix_continuous contactInverseTerms
private theorem extendedKernel_continuous : Continuous extendedKernel:=by
  unfold extendedKernel activeKernel
  exact (matrix_continuous activeTerms).add continuous_const

private theorem originalReadback_continuous : Continuous originalReadback:=by
  unfold originalReadback
  exact (originalChange_continuous.comp continuous_neg).matrix_transpose

theorem originalFieldDenominator_continuous : Continuous originalFieldDenominator:=
  extendedKernel_continuous.matrix_det

theorem originalClearedGreen_continuous : Continuous originalClearedGreen:=by
  unfold originalClearedGreen
  exact (originalChange_continuous.matrix_mul
    ((originalFieldDenominator_continuous.smul contactInverse_continuous).add
      (continuous_const.matrix_mul extendedKernel_continuous.matrix_adjugate))).matrix_mul
        originalReadback_continuous

def poleMomentum (q : PhysicalResponsePoint) (lambda : ℂ) : Fin 4→ℂ:=
  fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda

private theorem poleMomentum_continuous (q : PhysicalResponsePoint) : Continuous (poleMomentum q):=by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_id
  · exact continuous_const

def clearedPreparedField (q : PhysicalResponsePoint) (a lambda : ℂ) (force : Field289)
    (response : Bool) : Fin 289→ℂ:=
  originalClearedGreen (poleMomentum q lambda)*ᵥnormalizedPreparedSource q a lambda force response

def preparedFieldLeading (q : PhysicalResponsePoint) (a : ℂ) (force : Field289)
    (response : Bool) : Fin 289→ℂ:=
  originalClearedGreen (poleMomentum q a)*ᵥpreparedLeadingSource q a force response

theorem clearedPreparedField_continuousAt (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) :
    ContinuousAt (fun lambda=>clearedPreparedField q a lambda force response) a:=by
  unfold clearedPreparedField Matrix.mulVec dotProduct
  apply tendsto_pi_nhds.mpr
  intro row
  apply tendsto_finsetSum
  intro i _
  exact ((((originalClearedGreen_continuous.comp (poleMomentum_continuous q)).continuousAt.tendsto).apply_nhds row).apply_nhds i).mul
    ((normalizedPreparedSource_continuousAt q a force response).tendsto.apply_nhds i)

theorem preparedFieldLeading_equation (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) :
    originalJacobi (poleMomentum q a)*ᵥpreparedFieldLeading q a force response=
      originalFieldDenominator (poleMomentum q a) •
        (preparedLeadingSource q a force response-originalRowLift (poleMomentum q a)*ᵥ
          sourceCompatibility (poleMomentum q a) (preparedLeadingSource q a force response)):=by
  unfold preparedFieldLeading
  rw [Matrix.mulVec_mulVec,originalClearedGreen_equation,Matrix.smul_mulVec,
    Matrix.sub_mulVec,Matrix.one_mulVec]
  simp only [sourceCompatibility,Matrix.mulVec_mulVec,mul_assoc]

theorem clearedPreparedField_actual (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) (lambda : physicalSpectralDomain q.k)
    (punctured : lambda.val≠a) :
    ((lambda.val-a)^responsePoleOrder q a response*originalFieldDenominator (poleMomentum q lambda.val)) •
      rationalField q force response lambda=clearedPreparedField q a lambda.val force response:=by
  have green:=originalGreen_denominator
    (⟨poleMomentum q lambda.val,lambda.property⟩ : regularSource)
  have source:=preparedSource_scaled q a lambda.val force response punctured
  unfold rationalField clearedPreparedField PreparationVacuumOriginalGreenFeedback.sourceField
  rw [←source,←green]
  rw [Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul]
  congr 1
  exact mul_comm _ _

theorem clearedPreparedField_leading_limit (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) (root : (propagationPolynomial q).eval a=0) :
    Tendsto (fun lambda : ℂ=>clearedPreparedField q a lambda force response)
      (𝓝 a) (𝓝 (preparedFieldLeading q a force response)):=by
  have actual:=(clearedPreparedField_continuousAt q a force response).tendsto
  change Tendsto (fun lambda=>clearedPreparedField q a lambda force response) (𝓝 a)
    (𝓝 (originalClearedGreen (poleMomentum q a)*ᵥnormalizedPreparedSource q a a force response)) at actual
  rw [normalizedPreparedSource_at_pole q a force response root] at actual
  exact actual

private theorem originalReader_continuous (row : Fin 36) (column : Fin 289) :
    Continuous (fun p : Fin 4→ℂ=>originalReader36 p row column):=by
  run_tac
    let name:=(Lean.Name.num `_private.H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationPreparedMomentumReturn 0) ++
      `LowEnergy.SourcePropagationCommonMomentum.originalReader36_continuous
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) $(Lean.mkIdent `row) $(Lean.mkIdent `column)))

def clearedPreparedCurvature (q : PhysicalResponsePoint) (a lambda : ℂ)
    (force : Field289) (response : Bool) : Fin 36→ℂ:=
  originalReader36 (poleMomentum q lambda)*ᵥclearedPreparedField q a lambda force response

def preparedCurvatureLeading (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) : Fin 36→ℂ:=
  originalReader36 (poleMomentum q a)*ᵥpreparedFieldLeading q a force response

theorem clearedPreparedCurvature_leading_limit (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) (root : (propagationPolynomial q).eval a=0) :
    Tendsto (fun lambda : ℂ=>clearedPreparedCurvature q a lambda force response)
      (𝓝 a) (𝓝 (preparedCurvatureLeading q a force response)):=by
  apply tendsto_pi_nhds.mpr
  intro row
  unfold clearedPreparedCurvature preparedCurvatureLeading Matrix.mulVec dotProduct
  apply tendsto_finsetSum
  intro i _
  exact ((originalReader_continuous row i).comp (poleMomentum_continuous q)).continuousAt.tendsto.mul
    ((clearedPreparedField_leading_limit q a force response root).apply_nhds i)

theorem clearedPreparedCurvature_actual (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) (lambda : physicalSpectralDomain q.k)
    (positive : 0<lambda.val.re) (punctured : lambda.val≠a) :
    ((lambda.val-a)^responsePoleOrder q a response*originalFieldDenominator (poleMomentum q lambda.val)) •
      curvatureReturn q force response lambda=clearedPreparedCurvature q a lambda.val force response:=by
  rw [←rationalField_curvature q force response lambda positive]
  unfold clearedPreparedCurvature
  rw [←clearedPreparedField_actual q a force response lambda punctured,Matrix.mulVec_smul]
  rfl

end LowEnergy.SourcePropagationConstrainedPoleReturn
