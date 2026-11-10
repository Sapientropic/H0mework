import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMMixedAgeRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMMovingAge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFieldPerturbation PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open PreparationVacuumPhysicalFeedback PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumActionFieldLift
open ActualDressedEMTemporal ActualDressedLeftFreeJet ActualDressedFullCoulomb ActualDressedNoether
open ActualDressedNumberZero ActualDressedNumberField PhysicalEMGaugeRealization ActualDressedConstraintRead
open ActualSourcePreparedEMPhaseField ActualSourcePreparedEMAgeReturn
open Filter
open scoped Topology BigOperators
abbrev Op := H →L[ℂ] H
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointCompression jointCResolvent emTemporalReader dressedEulerObserver
  dressedNoetherKernel noetherReader jointResolvent physicalTime

private theorem moving_age_derivative (CL RL J RR CR : Op)
    (leftCommutes : Commute CL RL) (rightCommutes : Commute CR RR) (age : ℝ) :
    HasDerivAt (fun t : ℝ => SourceFiniteUnitary.time CL (-t)*RL*J*RR*SourceFiniteUnitary.time CR t)
      (Complex.I • (SourceFiniteUnitary.time CL (-age)*RL*(CL*J-J*CR)*RR*
        SourceFiniteUnitary.time CR age)) age := by
  have left := (time_operator_derivative CL (-age)).scomp age ((hasDerivAt_id age).neg)
  have right := time_operator_derivative CR age
  have generated := (((left.mul_const RL).mul_const J).mul_const RR).mul right
  have commuteL := leftCommutes.eq
  have commuteR := rightCommutes.eq
  have commuteT := (SourceFiniteUnitary.time_commutes CR CR (Commute.refl CR) age).eq
  change CL*RL=RL*CL at commuteL
  change CR*RR=RR*CR at commuteR
  convert! generated using 1
  simp only [Function.comp_apply,neg_smul]
  simp only [mul_sub,sub_mul,smul_sub]
  have first : SourceFiniteUnitary.time CL (-age)*RL*CL*J*RR*SourceFiniteUnitary.time CR age =
      SourceFiniteUnitary.time CL (-age)*CL*RL*J*RR*SourceFiniteUnitary.time CR age := by
    calc
      _ = SourceFiniteUnitary.time CL (-age)*(RL*CL)*J*RR*SourceFiniteUnitary.time CR age := by noncomm_ring
      _ = _ := by rw [←commuteL];noncomm_ring
  have second : SourceFiniteUnitary.time CL (-age)*RL*J*CR*RR*SourceFiniteUnitary.time CR age =
      SourceFiniteUnitary.time CL (-age)*RL*J*RR*SourceFiniteUnitary.time CR age*CR := by
    calc
      _ = SourceFiniteUnitary.time CL (-age)*RL*J*(CR*RR)*SourceFiniteUnitary.time CR age := by noncomm_ring
      _ = SourceFiniteUnitary.time CL (-age)*RL*J*RR*(CR*SourceFiniteUnitary.time CR age) := by
        rw [commuteR];noncomm_ring
      _ = _ := by rw [commuteT];noncomm_ring
  simp only [one_smul,mul_neg,neg_neg,mul_smul_comm,smul_mul_assoc,
    ←mul_assoc,first,second,sub_eq_add_neg]

/-- The actual two-momentum residual. Both original time and inverse
legs retain their own compression; the EM reader is the unchanged source reader. -/
def sourceEMMovingAgeKernel (event : DressedEvent) (transfer : PhysicalMomentum)
    (age : ℝ) (h : Field289) : Op :=
  let CL := jointCompression (event.momentum-transfer) event.frame h
  let CR := jointCompression event.momentum event.frame h
  let RL := jointCResolvent (event.momentum-transfer) event.frame event.energy h
  let RR := jointCResolvent event.momentum event.frame event.energy h
  let J := emTemporalReader event.momentum event.frame
  SourceFiniteUnitary.time CL (-age)*RL*(CL*J-J*CR)*RR*SourceFiniteUnitary.time CR age

theorem source_em_moving_actual_age_germ (event : DressedEvent) (transfer : PhysicalMomentum) :
    ∀ᶠ h : Field289 in 𝓝 0, ∀ age : ℝ,
      HasDerivAt (fun t : ℝ => dressedEulerObserver event
        (dressedNoetherKernel event transfer (emGaugeField 0) t h))
        (dressedEulerObserver event (Complex.I • sourceEMMovingAgeKernel event transfer age h)) age := by
  filter_upwards [actual_joint_free_units_near_zero (event.momentum-transfer) event.frame
    event.energy event.nonreal,actual_joint_free_units_near_zero event.momentum event.frame
    event.energy event.nonreal,actual_em_temporal_observer_germ event transfer] with h unitL unitR same
  intro age
  let CL := jointCompression (event.momentum-transfer) event.frame h
  let CR := jointCompression event.momentum event.frame h
  let RL := jointCResolvent (event.momentum-transfer) event.frame event.energy h
  let RR := jointCResolvent event.momentum event.frame event.energy h
  let J := emTemporalReader event.momentum event.frame
  have commutingL : Commute CL RL := by
    unfold RL jointCResolvent
    exact inverse_commuting _ _ unitL ((Commute.refl CL).sub_right ((Commute.one_right CL).smul_right _))
  have commutingR : Commute CR RR := by
    unfold RR jointCResolvent
    exact inverse_commuting _ _ unitR ((Commute.refl CR).sub_right ((Commute.one_right CR).smul_right _))
  have kernel := moving_age_derivative CL RL J RR CR commutingL commutingR age
  have read := ((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt age kernel
  have original : HasDerivAt (fun t : ℝ => dressedEulerObserver event (emTemporalFreeKernel event transfer t h))
      (dressedEulerObserver event (Complex.I • sourceEMMovingAgeKernel event transfer age h)) age := by
    convert! read using 1
  apply original.congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => by rw [source_em_phase_field];exact same t)

/-- Each of the original driven words keeps its own actual momentum.
The central insertion is the full BL J minus J BR, across every source force. -/
def sourceEMMovingAgeSlope (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) : Op :=
  let CL := jointCompression (event.momentum-transfer) event.frame 0
  let CR := jointCompression event.momentum event.frame 0
  let RL := jointCResolvent (event.momentum-transfer) event.frame event.energy 0
  let RR := jointCResolvent event.momentum event.frame event.energy 0
  let J := emTemporalReader event.momentum event.frame
  let BL := freeCompressionCurrent (event.momentum-transfer) event.frame force
  let BR := freeCompressionCurrent event.momentum event.frame force
  let left := SourceFiniteUnitary.time CL (-age)
  let right := SourceFiniteUnitary.time CR age
  let core := CL*J-J*CR
  freeTimeSlope (event.momentum-transfer) event.frame force (-age)*RL*core*RR*right+
    left*(-(RL*BL*RL))*core*RR*right+
    left*RL*(BL*J-J*BR)*RR*right+
    left*RL*core*(-(RR*BR*RR))*right+
    left*RL*core*RR*freeTimeSlope event.momentum event.frame force age

theorem source_em_moving_age_kernel_direction (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ => sourceEMMovingAgeKernel event transfer age (r • force))
      (sourceEMMovingAgeSlope event transfer force age) 0 := by
  have left := free_time_direction (event.momentum-transfer) event.frame force (-age)
  have greenL := free_green_direction (event.momentum-transfer) event.frame event.energy event.nonreal force
  have greenR := free_green_direction event.momentum event.frame event.energy event.nonreal force
  have core := ((free_compression_direction (event.momentum-transfer) event.frame force).mul_const
    (emTemporalReader event.momentum event.frame)).sub
    ((free_compression_direction event.momentum event.frame force).const_mul
      (emTemporalReader event.momentum event.frame))
  have right := free_time_direction event.momentum event.frame force age
  have generated := ((((left.mul greenL).mul core).mul greenR).mul right)
  unfold sourceEMMovingAgeKernel sourceEMMovingAgeSlope
  convert! generated using 1
  simp only [zero_smul,Pi.mul_apply,Pi.sub_apply,add_mul]

theorem source_em_moving_noether_age_direction (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ => deriv (fun t : ℝ => dressedEulerObserver event
      (dressedNoetherKernel event transfer (emGaugeField 0) t (r • force))) age)
      (dressedEulerObserver event (Complex.I • sourceEMMovingAgeSlope event transfer force age)) 0 := by
  have kernel := (source_em_moving_age_kernel_direction event transfer force age).const_smul Complex.I
  have read := ((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 kernel
  have ray : Tendsto (fun r : ℝ => r • force) (𝓝 0) (𝓝 (0 : Field289)) := by
    simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto
  apply read.congr_of_eventuallyEq
  filter_upwards [ray.eventually (source_em_moving_actual_age_germ event transfer)] with r actual
  exact (actual age).deriv

def sourceEMMovingJointObserver (event : DressedEvent) (transfer : PhysicalMomentum)
    (u : Field289 × ℝ) : ℂ :=
  dressedEulerObserver event (dressedNoetherKernel event transfer (emGaugeField 0) u.2 u.1)

theorem source_em_moving_joint_observer_C2 (event : DressedEvent) (transfer : PhysicalMomentum) (age : ℝ) :
    ContDiffAt ℝ 2 (sourceEMMovingJointObserver event transfer) (0,age) := by
  have left := jointPhysicalTime_C2 (event.momentum-transfer) event.frame (-1) age
  have greenL := (jointResolvent_C2 (event.momentum-transfer) event.frame event.energy event.nonreal).comp
    (0,age) contDiffAt_fst
  have reader := (noetherReader_C2 (emGaugeField 0) event.momentum event.frame).comp
    (0,age) contDiffAt_fst
  have greenR := (jointResolvent_C2 event.momentum event.frame event.energy event.nonreal).comp
    (0,age) contDiffAt_fst
  have right := jointPhysicalTime_C2 event.momentum event.frame 1 age
  have kernel := ((((left.mul greenL).mul reader).mul greenR).mul right)
  have observed := ((dressedEulerObserver event).restrictScalars ℝ).contDiff.contDiffAt.comp (0,age) kernel
  convert! observed using 1
  funext u
  simp only [sourceEMMovingJointObserver,dressedNoetherKernel,jointPhysicalTime,neg_one_mul,
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

private theorem source_em_scalar_field_derivative (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ => dressedEulerObserver event
      (dressedNoetherKernel event transfer (emGaugeField 0) age (r • force)))
      (emTemporalJet event transfer force age) 0 := by
  rw [source_em_phase_field]
  have ray : Tendsto (fun r : ℝ => r • force) (𝓝 0) (𝓝 (0 : Field289)) := by
    simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto
  have germ := ray.eventually (source_reader_germ (sourcePhaseGaugeField 0) event.momentum event.frame)
  have each (i : Fin 289) := (dressed_noether_action_derivative event transfer force age i).const_mul
    ((sourcePhaseGaugeField 0) i : ℂ)
  have whole := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => each i)
  apply whole.congr_of_eventuallyEq
  filter_upwards [germ] with r flat
  have kernel : dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age (r • force) =
      ∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ) •
        dressedNoetherKernel event transfer (fieldUnit i) age (r • force) := by
    unfold dressedNoetherKernel
    rw [flat]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_mul_assoc,mul_smul_comm]
  rw [kernel,map_sum]
  simp only [map_smul,smul_eq_mul]

/-- The same actual observer Hessian identifies the age derivative of every
original EM jet at its own moving transfer, retaining both source momenta. -/
theorem source_em_moving_temporal_jet_age_derivative (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289) (age : ℝ) :
    HasDerivAt (fun t : ℝ => emTemporalJet event transfer force t)
      (dressedEulerObserver event (Complex.I • sourceEMMovingAgeSlope event transfer force age)) age := by
  let S : ℝ × ℝ → ℂ := fun u => sourceEMMovingJointObserver event transfer (u.1 • force,u.2)
  have path : ContDiffAt ℝ 2 (fun u : ℝ × ℝ => (u.1 • force,u.2)) (0,age) :=
    (contDiffAt_fst.smul contDiffAt_const).prodMk contDiffAt_snd
  have aligned : ContDiffAt ℝ 2 (sourceEMMovingJointObserver event transfer) ((0:ℝ) • force,age) := by
    simpa only [zero_smul] using source_em_moving_joint_observer_C2 event transfer age
  have composed := aligned.comp (0,age) path
  have smooth : ContDiffAt ℝ 2 S (0,age) := by
    simpa only [S,Function.comp_def] using! composed
  rcases same_mixed_partials S age smooth with ⟨d,timeActual,fieldActual⟩
  have actual := source_em_moving_noether_age_direction event transfer force age
  have identified : d = dressedEulerObserver event (Complex.I • sourceEMMovingAgeSlope event transfer force age) :=
    fieldActual.unique actual
  rw [identified] at timeActual
  apply timeActual.congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => (source_em_scalar_field_derivative event transfer force t).deriv.symm)

end LowEnergy.GaussComposite.ActualSourcePreparedEMMovingAge
