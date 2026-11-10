import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMAgeFieldReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMTemporalPrice
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationPhysicalFeedbackField
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMMixedAgeRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection PreparationPhysicalPhaseGaugeRealization
open PreparationVacuumActionFieldLift
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedEMTemporal ActualDressedConstraintRead
open ActualSourcePreparedEMAgeFieldReturn ActualSourcePreparedEMPhaseField PhysicalEMGaugeRealization
open Filter
open scoped Topology BigOperators
abbrev Op := H →L[ℂ] H
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] dressedNoetherKernel dressedEulerObserver noetherReader jointResolvent physicalTime

def sourceEMJointObserver (event : DressedEvent) (u : Field289 × ℝ) : ℂ :=
  dressedEulerObserver event (dressedNoetherKernel event 0 (emGaugeField 0) u.2 u.1)

/-- The original physical time, inverse and Noether C² feed all five factors
of the same prepared observer. No caller smoothness certificate is accepted. -/
theorem source_em_joint_observer_C2 (event : DressedEvent) (age : ℝ) :
    ContDiffAt ℝ 2 (sourceEMJointObserver event) (0,age) := by
  have left := jointPhysicalTime_C2 event.momentum event.frame (-1) age
  have green := (jointResolvent_C2 event.momentum event.frame event.energy event.nonreal).comp
    (0,age) contDiffAt_fst
  have reader := (noetherReader_C2 (emGaugeField 0) event.momentum event.frame).comp
    (0,age) contDiffAt_fst
  have right := jointPhysicalTime_C2 event.momentum event.frame 1 age
  have kernel := ((((left.mul green).mul reader).mul green).mul right)
  have observed := ((dressedEulerObserver event).restrictScalars ℝ).contDiff.contDiffAt.comp (0,age) kernel
  convert! observed using 1
  funext u
  simp only [sourceEMJointObserver,dressedNoetherKernel,jointPhysicalTime,sub_zero,neg_one_mul,
    one_mul,Function.comp_apply,ContinuousLinearMap.coe_restrictScalars']

private theorem first_slice (S : ℝ × ℝ → ℂ) (u : ℝ × ℝ)
    (smooth : ContDiffAt ℝ 2 S u) :
    HasDerivAt (fun r : ℝ => S (r,u.2)) (fderiv ℝ S u (1,0)) u.1 := by
  have source := smooth.differentiableAt (by norm_num) |>.hasFDerivAt
  exact source.comp_hasDerivAt_of_eq u.1
    ((hasDerivAt_id u.1).prodMk (hasDerivAt_const u.1 u.2)) (by simp)

private theorem second_slice (S : ℝ × ℝ → ℂ) (u : ℝ × ℝ)
    (smooth : ContDiffAt ℝ 2 S u) :
    HasDerivAt (fun t : ℝ => S (u.1,t)) (fderiv ℝ S u (0,1)) u.2 := by
  have source := smooth.differentiableAt (by norm_num) |>.hasFDerivAt
  exact source.comp_hasDerivAt_of_eq u.2
    ((hasDerivAt_const u.2 u.1).prodMk (hasDerivAt_id u.2)) (by simp)

private theorem same_mixed_partials (S : ℝ × ℝ → ℂ) (age : ℝ)
    (smooth : ContDiffAt ℝ 2 S (0,age)) :
    ∃ d : ℂ,
      HasDerivAt (fun t : ℝ => deriv (fun r : ℝ => S (r,t)) 0) d age ∧
      HasDerivAt (fun r : ℝ => deriv (fun t : ℝ => S (r,t)) age) d 0 := by
  have second := (smooth.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have alongTime := second.comp_hasDerivAt_of_eq age
    ((hasDerivAt_const age (0:ℝ)).prodMk (hasDerivAt_id age)) rfl
  have appliedTime := alongTime.clm_apply (hasDerivAt_const age ((1,0) : ℝ × ℝ))
  have timePartial : HasDerivAt (fun t : ℝ => fderiv ℝ S (0,t) (1,0))
      (fderiv ℝ (fderiv ℝ S) (0,age) (0,1) (1,0)) age := by
    simpa only [Function.comp_apply,id_eq,map_zero,add_zero] using! appliedTime
  have alongField := second.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const 0 age)) rfl
  have appliedField := alongField.clm_apply (hasDerivAt_const 0 ((0,1) : ℝ × ℝ))
  have fieldPartial : HasDerivAt (fun r : ℝ => fderiv ℝ S (r,age) (0,1))
      (fderiv ℝ (fderiv ℝ S) (0,age) (1,0) (0,1)) 0 := by
    simpa only [Function.comp_apply,id_eq,map_zero,add_zero] using! appliedField
  have nearTime : ∀ᶠ t : ℝ in 𝓝 age, ContDiffAt ℝ 2 S (0,t) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually
      (smooth.eventually (by norm_num))
  have nearField : ∀ᶠ r : ℝ in 𝓝 0, ContDiffAt ℝ 2 S (r,age) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually
      (smooth.eventually (by norm_num))
  have timeActual : HasDerivAt (fun t : ℝ => deriv (fun r : ℝ => S (r,t)) 0)
      (fderiv ℝ (fderiv ℝ S) (0,age) (0,1) (1,0)) age := by
    apply timePartial.congr_of_eventuallyEq
    filter_upwards [nearTime] with t paid
    exact (first_slice S (0,t) paid).deriv
  have fieldActual : HasDerivAt (fun r : ℝ => deriv (fun t : ℝ => S (r,t)) age)
      (fderiv ℝ (fderiv ℝ S) (0,age) (1,0) (0,1)) 0 := by
    apply fieldPartial.congr_of_eventuallyEq
    filter_upwards [nearField] with r paid
    exact (second_slice S (r,age) paid).deriv
  have symmetric := (smooth.isSymmSndFDerivAt (by norm_num)).eq (1,0) (0,1)
  rw [symmetric] at fieldActual
  exact ⟨_,timeActual,fieldActual⟩

private theorem source_em_scalar_field_derivative (event : DressedEvent) (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ => dressedEulerObserver event
      (dressedNoetherKernel event 0 (emGaugeField 0) age (r • force)))
      (emTemporalJet event 0 force age) 0 := by
  rw [source_em_phase_field]
  have ray : Tendsto (fun r : ℝ => r • force) (𝓝 0) (𝓝 (0 : Field289)) := by
    simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto
  have germ := ray.eventually (source_reader_germ (sourcePhaseGaugeField 0) event.momentum event.frame)
  have each (i : Fin 289) := (dressed_noether_action_derivative event 0 force age i).const_mul
    ((sourcePhaseGaugeField 0) i : ℂ)
  have whole := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => each i)
  apply whole.congr_of_eventuallyEq
  filter_upwards [germ] with r flat
  have kernel : dressedNoetherKernel event 0 (sourcePhaseGaugeField 0) age (r • force) =
      ∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ) •
        dressedNoetherKernel event 0 (fieldUnit i) age (r • force) := by
    unfold dressedNoetherKernel
    rw [flat]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_mul_assoc,mul_smul_comm]
  rw [kernel,map_sum]
  simp only [map_smul,smul_eq_mul]

/-- The original EM Π age integrand directly consumes the actual five-word
source residual through the common observer Hessian. -/
theorem source_em_temporal_jet_age_derivative (event : DressedEvent) (force : Field289) (age : ℝ) :
    HasDerivAt (fun t : ℝ => emTemporalJet event 0 force t)
      (dressedEulerObserver event (Complex.I • sourceEMAgeFieldSlope event force age)) age := by
  let S : ℝ × ℝ → ℂ := fun u => sourceEMJointObserver event (u.1 • force,u.2)
  have path : ContDiffAt ℝ 2 (fun u : ℝ × ℝ => (u.1 • force,u.2)) (0,age) :=
    (contDiffAt_fst.smul contDiffAt_const).prodMk contDiffAt_snd
  have aligned : ContDiffAt ℝ 2 (sourceEMJointObserver event) ((0:ℝ) • force,age) := by
    simpa only [zero_smul] using source_em_joint_observer_C2 event age
  have composed := aligned.comp (0,age) path
  have smooth : ContDiffAt ℝ 2 S (0,age) := by
    simpa only [S,Function.comp_def] using! composed
  rcases same_mixed_partials S age smooth with ⟨d,timeActual,fieldActual⟩
  have actual := source_em_actual_noether_age_field_direction event force age
  have identified : d = dressedEulerObserver event (Complex.I • sourceEMAgeFieldSlope event force age) :=
    fieldActual.unique actual
  rw [identified] at timeActual
  apply timeActual.congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => (source_em_scalar_field_derivative event force t).deriv.symm)

end LowEnergy.GaussComposite.ActualSourcePreparedEMMixedAgeRead
