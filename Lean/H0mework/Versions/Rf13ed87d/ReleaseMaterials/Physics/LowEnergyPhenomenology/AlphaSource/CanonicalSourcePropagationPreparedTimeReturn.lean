import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNearFieldHalfAxis
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNearFieldTime
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil SourcePropagationResolvent
open PreparationVacuumPhysicalTailPrice PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
open SourcePropagationSpectralAxis SourcePropagationFieldFeedback
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
local instance : AddCommGroup TransferOp:=ContinuousLinearMap.addCommGroup
local instance : IsTopologicalAddGroup TransferOp:=by
  have normal : @IsTopologicalAddGroup TransferOp
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup.toAddGroup:=inferInstance
  convert! normal using 1
local instance : IsTopologicalRing TransferOp:=by
  convert! (NonUnitalSeminormedRing.toIsTopologicalRing (α:=TransferOp)) using 1
local instance : NormSMulClass ℂ TransferOp:=by
  convert! (NormedSpace.toNormSMulClass (𝕜:=ℂ) (E:=TransferOp)) using 1
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

open PreparationVacuumOriginalGreenFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumRealReaction
open MeasureTheory Set Filter
open scoped Topology Interval
attribute [local irreducible] sourceRead sourceGreen fieldInverse backgroundInitial backgroundOperator physicalBackgroundMap

/-- The read is taken on the whole original two-time propagation carrier. -/
def preparedTimeRead (q : PhysicalResponsePoint) (reader : Field289) (h : Field289) :
    @ContinuousLinearMap ℂ ℂ inferInstance inferInstance (RingHom.id ℂ) TransferOp
      (inferInstance : NormedAddCommGroup TransferOp).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup.toAddCommMonoid
      ℂ (inferInstance : NormedAddCommGroup ℂ).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup ℂ).toAddCommGroup.toAddCommMonoid
      (inferInstance : NormedSpace ℂ TransferOp).toModule (inferInstance : NormedSpace ℂ ℂ).toModule:=by
  convert! (sourceRead q).comp (ContinuousLinearMap.apply ℂ Op (backgroundInitial q reader h)) using 1

theorem preparedTimeRead_apply (q : PhysicalResponsePoint) (reader : Field289) (h : Field289) (T : TransferOp) :
    preparedTimeRead q reader h T=sourceRead q (T (backgroundInitial q reader h)):=rfl

theorem physicalBackgroundMap_kernel (q : PhysicalResponsePoint) (reader : Field289) (h : Field289) (t : ℝ) :
    physicalBackgroundMap q h t (backgroundInitial q reader h)=fiveKernel reader q.p q.k q.F q.z q.w t h :=by
  simp only [physicalBackgroundMap_apply,backgroundInitial,fiveKernel,neg_zero,physicalTime_initial,one_mul,mul_one,mul_assoc]

def timeSource (q : PhysicalResponsePoint) (h : Field289) (t : ℝ) (i : Fin 289) : ℂ:=
  -preparedTimeRead q (fieldUnit i) h (physicalBackgroundMap q h t)

theorem timeSource_actual (q : PhysicalResponsePoint) (h : Field289) (t : ℝ) :
    timeSource q h t=actualSource q t h :=by
  ext i
  rw [timeSource,preparedTimeRead_apply,physicalBackgroundMap_kernel]
  unfold actualSource eulerCovector rawPrepared sourceRead
  rfl

def preparedTimeHalf (q : PhysicalResponsePoint) (lambda : ℂ) (h : Field289) : Fin 289→ℂ:=
  fun i=>∫t in Ioi (0:ℝ),laplaceWeight lambda t*timeSource q h t i

def preparedTimeWindow (q : PhysicalResponsePoint) (lambda : ℂ) (h : Field289) (T : ℝ) : Fin 289→ℂ:=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*timeSource q h t i

theorem preparedTime_integrable (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (h : Field289) (inside : h∈timeDomain q lambda) (i : Fin 289) :
    IntegrableOn (fun t=>laplaceWeight lambda t*timeSource q h t i) (Ioi (0:ℝ)) :=by
  have actual:=physicalBackgroundMap_integrable q lambda positive h inside
  have normal : @Integrable TransferOp
      (inferInstance : NormedAddCommGroup TransferOp).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (SeminormedAddGroup.toContinuousENorm (E:=TransferOp))
      ℝ inferInstance (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t)
      (volume.restrict (Ioi (0:ℝ))):=by
    unfold IntegrableOn at actual
    convert! actual using 1
  have generated:=(ContinuousLinearMap.integrable_comp (𝕜:=ℂ) (E:=ℂ) (H:=TransferOp)
    (preparedTimeRead q (fieldUnit i) h) normal).neg
  unfold IntegrableOn
  convert! generated using 1
  funext t
  simp only [timeSource,preparedTimeRead_apply,map_smul,smul_eq_mul,mul_neg]
  rfl

theorem preparedTimeHalf_read (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (h : Field289) (inside : h∈timeDomain q lambda) (i : Fin 289) :
    preparedTimeHalf q lambda h i=-sourceRead q (nearTimeHalf q lambda h (backgroundInitial q (fieldUnit i) h)) :=by
  have actual:=physicalBackgroundMap_integrable q lambda positive h inside
  have normal : @Integrable TransferOp
      (inferInstance : NormedAddCommGroup TransferOp).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (SeminormedAddGroup.toContinuousENorm (E:=TransferOp))
      ℝ inferInstance (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t)
      (volume.restrict (Ioi (0:ℝ))):=by
    unfold IntegrableOn at actual
    convert! actual using 1
  have commutes:=ContinuousLinearMap.integral_comp_comm (𝕜:=ℂ) (E:=TransferOp) (Fₗ:=ℂ)
    (preparedTimeRead q (fieldUnit i) h) normal
  have read : preparedTimeRead q (fieldUnit i) h (nearTimeHalf q lambda h)=
      sourceRead q (nearTimeHalf q lambda h (backgroundInitial q (fieldUnit i) h)):=
    preparedTimeRead_apply q (fieldUnit i) h (nearTimeHalf q lambda h)
  rw [←read]
  unfold preparedTimeHalf nearTimeHalf
  calc
    _=∫t in Ioi (0:ℝ),-(preparedTimeRead q (fieldUnit i) h
        (laplaceWeight lambda t • physicalBackgroundMap q h t)):=by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t=>by
        simp only [timeSource,map_smul,smul_eq_mul,mul_neg])
    _=-(∫t in Ioi (0:ℝ),preparedTimeRead q (fieldUnit i) h
        (laplaceWeight lambda t • physicalBackgroundMap q h t)):=integral_neg _
    _=_:=congrArg Neg.neg commutes

theorem preparedTimeHalf_background_generated (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    ∀ᶠh : Field289 in 𝓝 0,preparedTimeHalf q lambda h=backgroundSource q lambda h :=by
  filter_upwards [timeDomain_source_near q lambda positive,nearTimeHalf_inverse_generated q lambda positive] with h inside inverse
  ext i
  rw [preparedTimeHalf_read q lambda positive h inside i,inverse]
  unfold backgroundSource backgroundOperator
  rfl

def preparedCoefficient (q : PhysicalResponsePoint) (lambda : ℂ) (h : Field289) (i : Fin 289) : ℝ:=
  ‖preparedTimeRead q (fieldUnit i) h‖*physicalBudget q (lambda.re/4)

theorem preparedTime_envelope (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (h : Field289) (inside : h∈timeDomain q lambda) (t : ℝ) (future : 0≤t) (i : Fin 289) :
    ‖laplaceWeight lambda t*timeSource q h t i‖≤preparedCoefficient q lambda h i*Real.exp (-(lambda.re/2)*t) :=by
  have identity : laplaceWeight lambda t*timeSource q h t i=
      -preparedTimeRead q (fieldUnit i) h (laplaceWeight lambda t • physicalBackgroundMap q h t):=by
    simp only [timeSource,map_smul,smul_eq_mul,mul_neg]
  rw [identity,norm_neg]
  exact ((preparedTimeRead q (fieldUnit i) h).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (physicalBackgroundMap_damped_bound q lambda positive h inside t future) (norm_nonneg _)).trans_eq (by unfold preparedCoefficient;ring))

def preparedTailPrice (q : PhysicalResponsePoint) (lambda : ℂ) (h : Field289) (T : ℝ) (i : Fin 289) : ℝ:=
  (2/lambda.re)*preparedCoefficient q lambda h i*Real.exp (-(lambda.re/2)*T)

theorem preparedTimeHalf_error (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (h : Field289) (inside : h∈timeDomain q lambda) (T : ℝ) (future : 0≤T) (i : Fin 289) :
    ‖preparedTimeHalf q lambda h i-preparedTimeWindow q lambda h T i‖≤preparedTailPrice q lambda h T i :=by
  have actual:=preparedTime_integrable q lambda positive h inside i
  have tail:=actual.mono_set (Ioi_subset_Ioi future)
  have equation:=intervalIntegral.integral_interval_add_Ioi actual tail
  have difference : preparedTimeHalf q lambda h i-preparedTimeWindow q lambda h T i=
      ∫t in Ioi T,laplaceWeight lambda t*timeSource q h t i:=by
    apply sub_eq_iff_eq_add.mpr
    simpa only [preparedTimeHalf,preparedTimeWindow,add_comm] using equation.symm
  rw [difference]
  have majorant : IntegrableOn (fun t : ℝ=>preparedCoefficient q lambda h i*Real.exp (-(lambda.re/2)*t)) (Ioi T):=
    (integrableOn_exp_mul_Ioi (a:=-(lambda.re/2)) (by linarith) T).const_mul _
  have bound : ∀ᵐt ∂volume.restrict (Ioi T),‖laplaceWeight lambda t*timeSource q h t i‖≤
      preparedCoefficient q lambda h i*Real.exp (-(lambda.re/2)*t):=
    (ae_restrict_mem measurableSet_Ioi).mono (fun t ht=>preparedTime_envelope q lambda positive h inside t (future.trans ht.le) i)
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae tail.norm majorant bound).trans_eq ?_)
  rw [integral_const_mul,integral_exp_mul_Ioi (show -(lambda.re/2)<0 by linarith) T]
  unfold preparedTailPrice
  field_simp

def preparedTimeField (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (h : Field289) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
      (preparedTimeHalf q lambda.val h)

def preparedWindowField (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (h : Field289) (T : ℝ) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
      (preparedTimeWindow q lambda.val h T)

def preparedFieldPrice (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (h : Field289) (T : ℝ) (row : Fin 289) : ℝ:=
  ∑i : Fin 289,‖sourceGreen ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩ row i‖*
    preparedTailPrice q lambda.val h T i

theorem preparedTimeField_error (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re)
    (h : Field289) (inside : h∈timeDomain q lambda.val) (T : ℝ) (future : 0≤T) (row : Fin 289) :
    ‖preparedTimeField q lambda h row-preparedWindowField q lambda h T row‖≤preparedFieldPrice q lambda h T row :=by
  unfold preparedTimeField preparedWindowField PreparationVacuumOriginalGreenFeedback.sourceField preparedFieldPrice
  simp only [Matrix.mulVec,dotProduct,←Finset.sum_sub_distrib,←mul_sub]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (preparedTimeHalf_error q lambda.val positive h inside T future i) (norm_nonneg _)

theorem preparedTimeField_background_generated (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    ∀ᶠh : Field289 in 𝓝 0,preparedTimeField q lambda h=backgroundField q lambda h :=by
  filter_upwards [preparedTimeHalf_background_generated q lambda.val positive] with h same
  unfold preparedTimeField backgroundField
  rw [same]

theorem preparedTimeField_equation (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (h : Field289) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥpreparedTimeField q lambda h=
      preparedTimeHalf q lambda.val h-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)
            (preparedTimeHalf q lambda.val h) :=by
  unfold preparedTimeField
  exact original_forced_field
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
    (preparedTimeHalf q lambda.val h)

theorem preparedTimeCurvature_background_generated (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    ∀ᶠh : Field289 in 𝓝 0,originalReader36
      (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥpreparedTimeField q lambda h=
      backgroundCurvature q lambda h :=by
  filter_upwards [preparedTimeField_background_generated q lambda positive] with h same
  rw [same]
  rfl

end LowEnergy.SourcePropagationNearFieldTime
