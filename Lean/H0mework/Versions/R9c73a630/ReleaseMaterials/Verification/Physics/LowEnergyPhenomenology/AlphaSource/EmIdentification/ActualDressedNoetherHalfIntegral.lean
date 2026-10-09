import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherBackground

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNonlinearHalf
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil
open SourcePropagationResolvent SourcePropagationFieldFeedback SourcePropagationNearFieldTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
local instance : NormedAlgebra ℝ ResponseOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ SourcePropagationResolvent.TransferOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ SourcePropagationResolvent.TransferOp := ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ SourcePropagationResolvent.TransferOp := by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=SourcePropagationResolvent.TransferOp)) using 1
local instance : ContinuousSMul ℝ SourcePropagationResolvent.TransferOp := by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=SourcePropagationResolvent.TransferOp)) using 1
local instance : ContinuousENorm SourcePropagationResolvent.TransferOp := by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=SourcePropagationResolvent.TransferOp)) using 1
attribute [local irreducible] noetherBackgroundInitial noetherBackgroundOperator physicalBackgroundMap
  nearTimeHalf fieldInverse noetherStaticHalf dressedKinematicPoint dressedNoetherKernel

def noetherNonlinearHalf (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ)
    (h : Field289) : ResponseOp :=
  ∫t in Ioi (0:ℝ),laplaceWeight lambda t •
    physicalBackgroundMap q h t (noetherBackgroundInitial q reader h)

def noetherNonlinearWindow (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ)
    (h : Field289) (T : ℝ) : ResponseOp :=
  ∫t in (0:ℝ)..T,laplaceWeight lambda t •
    physicalBackgroundMap q h t (noetherBackgroundInitial q reader h)

attribute [local irreducible] noetherNonlinearHalf noetherNonlinearWindow

/-- The original two-time propagation reads exactly the actual nonlinear Noether insertion. -/
theorem noether_nonlinear_kernel_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader h : Field289) (t : ℝ) :
    physicalBackgroundMap (dressedKinematicPoint event transfer) h t
        (noetherBackgroundInitial (dressedKinematicPoint event transfer) reader h)=
      dressedNoetherKernel event transfer reader t h := by
  simp only [physicalBackgroundMap_apply,noetherBackgroundInitial,dressedNoetherKernel,
    dressedKinematicPoint,mul_assoc,sub_eq_add_neg]

theorem noether_nonlinear_half_integrable (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) (h : Field289) (inside : h∈timeDomain q lambda) :
    IntegrableOn (fun t=>laplaceWeight lambda t •
      physicalBackgroundMap q h t (noetherBackgroundInitial q reader h)) (Ioi (0:ℝ)) := by
  have paid:=physicalBackgroundMap_integrable q lambda positive h inside
  unfold IntegrableOn at *
  with_reducible_and_instances
    have generated:=Integrable.apply_continuousLinearMap (𝕜:=ℂ) (𝕜':=ℂ) (σ:=RingHom.id ℂ)
      (H:=ResponseOp) (E:=ResponseOp) paid (noetherBackgroundInitial q reader h)
    simpa only [smul_apply] using! generated

/-- The nonlinear halfline and the generated field inverse agree on an original source neighborhood. -/
theorem noether_nonlinear_half_background (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    noetherNonlinearHalf q reader lambda=ᶠ[𝓝 0] noetherBackgroundOperator q reader lambda := by
  filter_upwards [timeDomain_source_near q lambda positive,nearTimeHalf_inverse_generated q lambda positive]
    with h inside inverse
  have integral:=physicalBackgroundMap_integrable q lambda positive h inside
  have read:=ContinuousLinearMap.integral_apply integral (noetherBackgroundInitial q reader h)
  calc
    _=nearTimeHalf q lambda h (noetherBackgroundInitial q reader h) := by
      unfold noetherNonlinearHalf nearTimeHalf
      simpa only [smul_apply] using! read.symm
    _=noetherBackgroundOperator q reader lambda h := by
      simpa only [noetherBackgroundOperator] using!
        congrArg (fun T : SourcePropagationResolvent.TransferOp=>T (noetherBackgroundInitial q reader h)) inverse

theorem noether_nonlinear_half_C2 (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    ContDiffAt ℝ 2 (noetherNonlinearHalf q reader lambda) 0 :=
  (noether_background_operator_C2 q reader lambda (ne_of_gt positive) hz hw).congr_of_eventuallyEq
    (noether_nonlinear_half_background q reader lambda positive)

/-- This differentiates the original nonlinear integral through its generated neighborhood identity. -/
theorem noether_nonlinear_half_derivative (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>noetherNonlinearHalf q reader lambda (r • force))
      (noetherStaticHalf q reader force lambda) 0 := by
  have ray : Tendsto (fun r : ℝ=>r • force) (𝓝 0) (𝓝 (0:Field289)) := by
    simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto
  exact (noether_background_operator_derivative q reader force lambda positive hz hw).congr_of_eventuallyEq
    ((noether_nonlinear_half_background q reader lambda positive).comp_tendsto ray)

def noetherNonlinearCoefficient (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (h : Field289) : ℝ :=
  ‖noetherBackgroundInitial q reader h‖*physicalBudget q (lambda.re/4)

def noetherNonlinearTailPrice (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (h : Field289) (T : ℝ) : ℝ :=
  (2/lambda.re)*noetherNonlinearCoefficient q reader lambda h*Real.exp (-(lambda.re/2)*T)

theorem noether_nonlinear_weighted_price (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) (h : Field289) (inside : h∈timeDomain q lambda)
    (t : ℝ) (future : 0≤t) :
    ‖laplaceWeight lambda t • physicalBackgroundMap q h t (noetherBackgroundInitial q reader h)‖ ≤
      noetherNonlinearCoefficient q reader lambda h*Real.exp (-(lambda.re/2)*t) := by
  have applied:=(laplaceWeight lambda t • physicalBackgroundMap q h t).le_opNorm
    (noetherBackgroundInitial q reader h)
  have bounded:=mul_le_mul_of_nonneg_right
    (physicalBackgroundMap_damped_bound q lambda positive h inside t future)
      (norm_nonneg (noetherBackgroundInitial q reader h))
  refine applied.trans (bounded.trans_eq ?_)
  unfold noetherNonlinearCoefficient
  ring

private theorem half_window_difference {A : Type*} [AddCommGroup A] (a b c : A)
    (split : b+c=a) : a-b=c := by
  rw [←split]
  abel

theorem noether_nonlinear_half_tail (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) (h : Field289) (inside : h∈timeDomain q lambda)
    (T : ℝ) (future : 0≤T) :
    ‖noetherNonlinearHalf q reader lambda h-noetherNonlinearWindow q reader lambda h T‖ ≤
      noetherNonlinearTailPrice q reader lambda h T := by
  have full:=noether_nonlinear_half_integrable q reader lambda positive h inside
  have tail:=full.mono_set (Ioi_subset_Ioi future)
  have equation:=intervalIntegral.integral_interval_add_Ioi full tail
  have difference : noetherNonlinearHalf q reader lambda h-noetherNonlinearWindow q reader lambda h T=
      ∫t in Ioi T,laplaceWeight lambda t •
        physicalBackgroundMap q h t (noetherBackgroundInitial q reader h) := by
    apply half_window_difference
    simpa only [noetherNonlinearHalf,noetherNonlinearWindow] using! equation
  have majorant : IntegrableOn (fun t : ℝ=>noetherNonlinearCoefficient q reader lambda h*
      Real.exp (-(lambda.re/2)*t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith) T).const_mul _
  have bounded : ∀ᵐt ∂volume.restrict (Ioi T),
      ‖laplaceWeight lambda t • physicalBackgroundMap q h t (noetherBackgroundInitial q reader h)‖ ≤
        noetherNonlinearCoefficient q reader lambda h*Real.exp (-(lambda.re/2)*t) :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun t ht=>
      noether_nonlinear_weighted_price q reader lambda positive h inside t (future.trans ht.le))
  rw [difference]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae tail.norm majorant bounded).trans_eq ?_)
  rw [integral_const_mul,integral_exp_mul_Ioi (by linarith)]
  unfold noetherNonlinearTailPrice
  field_simp

end LowEnergy.GaussComposite.ActualDressedNonlinearHalf
