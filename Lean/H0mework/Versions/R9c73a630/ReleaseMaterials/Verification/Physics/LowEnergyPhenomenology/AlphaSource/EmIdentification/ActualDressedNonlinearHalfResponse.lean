import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherHalfIntegral
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPolarization

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNonlinearHalf
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalHalfAxis SourcePropagationNearFieldTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedSylvester
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
local instance : NormedAlgebra ℝ ResponseOp := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] dressedEulerObserver dressedNoetherKernel physicalBackgroundMap
  noetherBackgroundInitial noetherBackgroundOperator noetherNonlinearHalf noetherNonlinearWindow noetherStaticHalf

/-- The actual normalized creation minus its unchanged background observes the nonlinear integral. -/
def dressedNoetherHalfSource (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (h : Field289) : Fin 289→ℂ :=
  fun i=>∫t in Ioi (0:ℝ),laplaceWeight lambda t*
    dressedEulerObserver event (dressedNoetherKernel event transfer (fieldUnit i) t h)

def dressedNoetherWindowSource (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (h : Field289) (T : ℝ) : Fin 289→ℂ :=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*
    dressedEulerObserver event (dressedNoetherKernel event transfer (fieldUnit i) t h)

def dressedNoetherBackgroundSource (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (h : Field289) : Fin 289→ℂ :=
  fun i=>dressedEulerObserver event
    (noetherBackgroundOperator (dressedKinematicPoint event transfer) (fieldUnit i) lambda h)

attribute [local irreducible] dressedNoetherHalfSource dressedNoetherWindowSource dressedNoetherBackgroundSource

theorem dressed_noether_half_integrable (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (h : Field289)
    (inside : h∈timeDomain (dressedKinematicPoint event transfer) lambda) (i : Fin 289) :
    IntegrableOn (fun t=>laplaceWeight lambda t*
      dressedEulerObserver event (dressedNoetherKernel event transfer (fieldUnit i) t h)) (Ioi (0:ℝ)) := by
  have paid:=noether_nonlinear_half_integrable (dressedKinematicPoint event transfer) (fieldUnit i)
    lambda positive h inside
  simpa only [IntegrableOn,map_smul,smul_eq_mul,noether_nonlinear_kernel_actual] using!
    (dressedEulerObserver event).integrable_comp paid

theorem dressed_noether_half_read (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (h : Field289)
    (inside : h∈timeDomain (dressedKinematicPoint event transfer) lambda) (i : Fin 289) :
    dressedNoetherHalfSource event transfer lambda h i=
      dressedEulerObserver event
        (noetherNonlinearHalf (dressedKinematicPoint event transfer) (fieldUnit i) lambda h) := by
  have paid:=noether_nonlinear_half_integrable (dressedKinematicPoint event transfer) (fieldUnit i)
    lambda positive h inside
  simpa only [dressedNoetherHalfSource,noetherNonlinearHalf,map_smul,smul_eq_mul,
    noether_nonlinear_kernel_actual] using!
      (dressedEulerObserver event).integral_comp_comm paid

private theorem weighted_noether_continuous (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (h : Field289) : Continuous (fun t=>laplaceWeight lambda t •
      physicalBackgroundMap q h t (noetherBackgroundInitial q reader h)) := by
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  exact weight.smul ((physicalBackgroundMap_continuous q h).clm_apply continuous_const)

theorem dressed_noether_window_read (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (h : Field289) (T : ℝ) (i : Fin 289) :
    dressedNoetherWindowSource event transfer lambda h T i=
      dressedEulerObserver event
        (noetherNonlinearWindow (dressedKinematicPoint event transfer) (fieldUnit i) lambda h T) := by
  have paid:=(weighted_noether_continuous (dressedKinematicPoint event transfer) (fieldUnit i) lambda h).intervalIntegrable (μ:=volume) 0 T
  simpa only [dressedNoetherWindowSource,noetherNonlinearWindow,map_smul,smul_eq_mul,
    noether_nonlinear_kernel_actual] using!
      (dressedEulerObserver event).intervalIntegral_comp_comm paid

theorem dressed_noether_half_background (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) :
    dressedNoetherHalfSource event transfer lambda=ᶠ[𝓝 0] dressedNoetherBackgroundSource event transfer lambda := by
  have readers : ∀ᶠh : Field289 in 𝓝 0,∀i : Fin 289,
      noetherNonlinearHalf (dressedKinematicPoint event transfer) (fieldUnit i) lambda h=
        noetherBackgroundOperator (dressedKinematicPoint event transfer) (fieldUnit i) lambda h :=
    Filter.eventually_all.2 (fun i=>noether_nonlinear_half_background
      (dressedKinematicPoint event transfer) (fieldUnit i) lambda positive)
  filter_upwards [timeDomain_source_near (dressedKinematicPoint event transfer) lambda positive,readers]
    with h inside same
  funext i
  simpa only [dressedNoetherBackgroundSource] using!
    (dressed_noether_half_read event transfer lambda positive h inside i).trans
      (congrArg (dressedEulerObserver event) (same i))

private theorem background_source_C2 (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) :
    ContDiffAt ℝ 2 (dressedNoetherBackgroundSource event transfer lambda) 0 := by
  unfold dressedNoetherBackgroundSource
  apply contDiffAt_pi.mpr
  intro i
  exact ((dressedEulerObserver event).restrictScalars ℝ).contDiff.contDiffAt.comp 0
    (noether_background_operator_C2 (dressedKinematicPoint event transfer) (fieldUnit i) lambda
      (ne_of_gt positive) event.nonreal event.nonreal)

theorem dressed_noether_half_C2 (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) :
    ContDiffAt ℝ 2 (dressedNoetherHalfSource event transfer lambda) 0 :=
  (background_source_C2 event transfer lambda positive).congr_of_eventuallyEq
    (dressed_noether_half_background event transfer lambda positive)

theorem dressed_noether_half_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    HasDerivAt (fun r : ℝ=>dressedNoetherHalfSource event transfer lambda (r • force))
      (fun i=>dressedEulerObserver event
        (noetherStaticHalf (dressedKinematicPoint event transfer) (fieldUnit i) force lambda)) 0 := by
  have generated : HasDerivAt (fun r : ℝ=>dressedNoetherBackgroundSource event transfer lambda (r • force))
      (fun i=>dressedEulerObserver event
        (noetherStaticHalf (dressedKinematicPoint event transfer) (fieldUnit i) force lambda)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have observed:=((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (noether_background_operator_derivative (dressedKinematicPoint event transfer) (fieldUnit i)
        force lambda positive event.nonreal event.nonreal)
    simpa only [dressedNoetherBackgroundSource,Function.comp_def,ContinuousLinearMap.coe_restrictScalars'] using! observed
  have ray : Tendsto (fun r : ℝ=>r • force) (𝓝 0) (𝓝 (0:Field289)) := by
    simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto
  exact generated.congr_of_eventuallyEq ((dressed_noether_half_background event transfer lambda positive).comp_tendsto ray)

/-- Every actual polarization column is now a derivative of the original nonlinear halfline. -/
theorem dressed_noether_half_column_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (j : Fin 289) :
    HasDerivAt (fun r : ℝ=>dressedNoetherHalfSource event transfer lambda (r • fieldUnit j))
      (fun i=>dressedStaticPolarization event transfer lambda i j) 0 := by
  simpa only [dressedStaticPolarization] using!
    dressed_noether_half_derivative event transfer (fieldUnit j) lambda positive

theorem dressed_noether_half_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (h : Field289)
    (inside : h∈timeDomain (dressedKinematicPoint event transfer) lambda)
    (T : ℝ) (future : 0≤T) (i : Fin 289) :
    ‖dressedNoetherHalfSource event transfer lambda h i-dressedNoetherWindowSource event transfer lambda h T i‖ ≤
      2*noetherNonlinearTailPrice (dressedKinematicPoint event transfer) (fieldUnit i) lambda h T := by
  let difference:=noetherNonlinearHalf (dressedKinematicPoint event transfer) (fieldUnit i) lambda h-
    noetherNonlinearWindow (dressedKinematicPoint event transfer) (fieldUnit i) lambda h T
  have read : dressedNoetherHalfSource event transfer lambda h i-dressedNoetherWindowSource event transfer lambda h T i=
      dressedEulerObserver event difference :=
    (congrArg₂ (fun x y : ℂ=>x-y) (dressed_noether_half_read event transfer lambda positive h inside i)
      (dressed_noether_window_read event transfer lambda h T i)).trans
        ((dressedEulerObserver event).map_sub _ _).symm
  calc
    _=‖dressedEulerObserver event difference‖ := congrArg norm read
    _≤‖dressedEulerObserver event‖*‖difference‖ := (dressedEulerObserver event).le_opNorm difference
    _≤2*‖difference‖ := mul_le_mul_of_nonneg_right (dressed_euler_observer_price event) (norm_nonneg difference)
    _≤_ := mul_le_mul_of_nonneg_left
      (noether_nonlinear_half_tail (dressedKinematicPoint event transfer) (fieldUnit i) lambda positive h inside T future)
        (by norm_num)

end LowEnergy.GaussComposite.ActualDressedNonlinearHalf
