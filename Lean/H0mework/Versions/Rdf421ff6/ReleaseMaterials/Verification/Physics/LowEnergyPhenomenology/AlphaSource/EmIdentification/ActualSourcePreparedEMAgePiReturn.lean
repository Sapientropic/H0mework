import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMAgePiWindow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMTemporalFreeReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticHalfPencil
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMAgePiReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalHalfAxis
open PreparationPhysicalPhaseGaugeRealization
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedEMTemporal ActualDressedLeftFreeJet
open ActualDressedNumberField
open ActualDressedSignal ActualDressedPencil ActualDressedSylvester ActualDressedStaticResponse
open ActualSourcePreparedNoetherPi ActualSourcePreparedEMPhaseField ActualSourcePreparedEMTemporalFreeReturn
open ActualSourcePreparedEMAgeFieldReturn ActualSourcePreparedEMAgePiWindow
open Filter Set MeasureTheory
open scoped Topology Interval BigOperators Matrix
attribute [local irreducible] emTemporalJet emTemporalReader dressedEulerObserver
  sourcePreparedPiEntry sourcePreparedEMTemporalPi sourceEMAgePiWindow

private theorem free_time_slope_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) : freeTimeSlope p F force 0=0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [abs_zero,zero_mul] using free_time_slope_price p F force 0)
    (norm_nonneg _)

/-- The two original inverse variations at age zero. The source reader,
compression current, energy and actual observer pair remain unchanged. -/
def sourceEMInitialKernel (event : DressedEvent) (force : Field289) : H →L[ℂ] H :=
  let R := jointCResolvent event.momentum event.frame event.energy 0
  let B := freeCompressionCurrent event.momentum event.frame force
  let J := emTemporalReader event.momentum event.frame;
  -(R*B*R)*J*R+R*J*(-(R*B*R))

theorem source_em_initial_jet (event : DressedEvent) (force : Field289) :
    emTemporalJet event 0 force 0=dressedEulerObserver event (sourceEMInitialKernel event force) := by
  rw [actual_em_temporal_jet_free]
  unfold emFreeSlope sourceEMInitialKernel
  simp only [sub_zero,neg_zero,free_time_slope_zero,SourceFiniteUnitary.time_zero,
    zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero]

/-- The original all-age linear price makes the positive-frequency
terminal vanish. No asymptotic endpoint is supplied by a caller. -/
theorem source_em_weighted_endpoint_limit (event : DressedEvent) (lambda : ℂ)
    (positive : 0<lambda.re) (force : Field289) :
    Tendsto (fun t : ℝ => laplaceWeight lambda t*emTemporalJet event 0 force t)
      atTop (𝓝 0) := by
  have scaled := (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop positive
  have decay : Tendsto (fun t : ℝ => Real.exp (-lambda.re*t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp scaled
  have polynomial := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp scaled).const_mul lambda.re⁻¹
  have linear : Tendsto (fun t : ℝ => t*Real.exp (-lambda.re*t)) atTop (𝓝 0) := by
    have same : (fun t : ℝ => lambda.re⁻¹*((lambda.re*t)^1*Real.exp (-(lambda.re*t)))) =
        (fun t : ℝ => t*Real.exp (-lambda.re*t)) := by
      funext t
      rw [pow_one]
      field_simp
    simpa only [Function.comp_def,id_eq,same,mul_zero] using polynomial
  have majorant : Tendsto (fun t : ℝ => emTemporalPrice event 0 force*
      (Real.exp (-lambda.re*t)+t*Real.exp (-lambda.re*t))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (decay.add linear).const_mul (emTemporalPrice event 0 force)
  apply squeeze_zero_norm' _ majorant
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t future
  rw [norm_mul,laplace_norm]
  have source := mul_le_mul_of_nonneg_left
    (actual_em_temporal_jet_linear_price event 0 force t) (Real.exp_pos (-lambda.re*t)).le
  exact source.trans_eq (by rw [abs_of_nonneg future];ring)

/-- The unchanged static full289 window limit returns the same
preparation Pi, then the original source EM row reads that limit. -/
theorem source_em_age_pi_window_limit (event : DressedEvent) (lambda : ℂ)
    (positive : 0<lambda.re) (j : Fin 289) :
    Tendsto (fun T : ℝ => sourceEMAgePiWindow event lambda T j) atTop
      (𝓝 (sourcePreparedEMTemporalPi event 0 lambda j)) := by
  have whole := static_polarization_window_limit event 0 (0 : Fin 4 → ℂ) rfl lambda positive
  have each (i : Fin 289) : Tendsto
      (fun T : ℝ => ((sourcePhaseGaugeField 0) i : ℂ)*dressedWindowPolarization event 0 0 lambda T i j)
      atTop (𝓝 (((sourcePhaseGaugeField 0) i : ℂ)*sourcePreparedPiEntry event 0 lambda i j)) := by
    have coordinate := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp whole i) j).const_mul
      (((sourcePhaseGaugeField 0) i : ℂ))
    rw [source_prepared_pi_actual event 0 lambda positive i j]
    exact coordinate
  unfold sourceEMAgePiWindow sourcePreparedEMTemporalPi
  rw [source_temporal_force_phase]
  exact tendsto_finsetSum _ (fun i _ => each i)

/-- This is the finite integral of the original EM age residual,
already generated as the age derivative of the same Noether jet. -/
def sourceEMAgeResidualWindow (event : DressedEvent) (lambda : ℂ) (T : ℝ) (j : Fin 289) : ℂ :=
  ∫t in (0 : ℝ)..T, laplaceWeight lambda t*
    dressedEulerObserver event (Complex.I • sourceEMAgeFieldSlope event (fieldUnit j) t)

/-- Positive frequency returns the original full Pi from its generated
initial term and residual improper integral, without deleting the residual. -/
theorem source_em_age_residual_window_limit (event : DressedEvent) (lambda : ℂ)
    (positive : 0<lambda.re) (j : Fin 289) :
    Tendsto (fun T : ℝ => sourceEMAgeResidualWindow event lambda T j) atTop
      (𝓝 (-dressedEulerObserver event (sourceEMInitialKernel event (fieldUnit j))+
        lambda*sourcePreparedEMTemporalPi event 0 lambda j)) := by
  have source := ((source_em_weighted_endpoint_limit event lambda positive (fieldUnit j)).sub
    (tendsto_const_nhds (x:=emTemporalJet event 0 (fieldUnit j) 0))).add
    ((source_em_age_pi_window_limit event lambda positive j).const_mul lambda)
  have same : (fun T : ℝ => sourceEMAgeResidualWindow event lambda T j) =
      (fun T : ℝ => laplaceWeight lambda T*emTemporalJet event 0 (fieldUnit j) T-
        emTemporalJet event 0 (fieldUnit j) 0+lambda*sourceEMAgePiWindow event lambda T j) := by
    funext T
    exact source_em_age_pi_window_boundary event lambda T j
  rw [same]
  simpa only [zero_sub,source_em_initial_jet] using source

/-- A finite error price for that same infinite return retains the actual
terminal and the preparation tail, not an independently assigned remainder. -/
theorem source_em_age_residual_window_price (event : DressedEvent) (lambda : ℂ)
    (positive : 0<lambda.re) (T : ℝ) (future : 0≤T) (j : Fin 289) :
    ‖sourceEMAgeResidualWindow event lambda T j-
      (-dressedEulerObserver event (sourceEMInitialKernel event (fieldUnit j))+
        lambda*sourcePreparedEMTemporalPi event 0 lambda j)‖ ≤
      Real.exp (-lambda.re*T)*emTemporalPrice event 0 (fieldUnit j)*(1+T)+
        ‖lambda‖*(∑i : Fin 289, ‖((sourcePhaseGaugeField 0) i : ℂ)‖)*
          dressedSignalTailPrice event 0 (0 : Fin 4 → ℂ) lambda T := by
  have same : sourcePreparedEMTemporalPi event 0 lambda j =
      ∑i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ)*sourcePreparedPiEntry event 0 lambda i j := by
    unfold sourcePreparedEMTemporalPi
    rw [source_temporal_force_phase]
  have tail := source_em_age_pi_prepared_tail event lambda positive T future j
  rw [←same,norm_sub_rev] at tail
  have terminal : ‖laplaceWeight lambda T*emTemporalJet event 0 (fieldUnit j) T‖ ≤
      Real.exp (-lambda.re*T)*emTemporalPrice event 0 (fieldUnit j)*(1+T) := by
    rw [norm_mul,laplace_norm]
    have price := mul_le_mul_of_nonneg_left
      (actual_em_temporal_jet_linear_price event 0 (fieldUnit j) T) (Real.exp_pos (-lambda.re*T)).le
    simpa only [abs_of_nonneg future,mul_assoc] using price
  unfold sourceEMAgeResidualWindow
  rw [source_em_age_pi_window_boundary,source_em_initial_jet]
  have equation : laplaceWeight lambda T*emTemporalJet event 0 (fieldUnit j) T-
      dressedEulerObserver event (sourceEMInitialKernel event (fieldUnit j))+
      lambda*sourceEMAgePiWindow event lambda T j-
      (-dressedEulerObserver event (sourceEMInitialKernel event (fieldUnit j))+
        lambda*sourcePreparedEMTemporalPi event 0 lambda j) =
      laplaceWeight lambda T*emTemporalJet event 0 (fieldUnit j) T+
        lambda*(sourceEMAgePiWindow event lambda T j-sourcePreparedEMTemporalPi event 0 lambda j) := by ring
  rw [equation]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have combined := add_le_add terminal (mul_le_mul_of_nonneg_left tail (norm_nonneg lambda))
  simpa only [norm_mul,mul_assoc] using combined

end LowEnergy.GaussComposite.ActualSourcePreparedEMAgePiReturn
