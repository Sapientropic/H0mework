import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMAgeReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMAgeFieldReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFieldPerturbation PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open ActualDressedEMTemporal ActualDressedLeftFreeJet ActualDressedFullCoulomb ActualDressedNoether
open ActualDressedNumberZero ActualDressedNumberField PhysicalEMGaugeRealization
open ActualSourcePreparedEMPhaseField ActualSourcePreparedEMAgeReturn
open Filter
open scoped Topology
abbrev Op := H →L[ℂ] H
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointCompression jointCResolvent emTemporalReader dressedEulerObserver

private theorem source_age_kernel_derivative (C R J : Op) (commuting : Commute C R) (age : ℝ) :
    HasDerivAt (fun t : ℝ => SourceFiniteUnitary.time C (-t)*R*J*R*SourceFiniteUnitary.time C t)
      (Complex.I • (SourceFiniteUnitary.time C (-age)*R*(C*J-J*C)*R*SourceFiniteUnitary.time C age)) age := by
  have left := (time_operator_derivative C (-age)).scomp age ((hasDerivAt_id age).neg)
  have right := time_operator_derivative C age
  have generated := (((left.mul_const R).mul_const J).mul_const R).mul right
  have commuteR := commuting.eq
  have commuteT := (SourceFiniteUnitary.time_commutes C C (Commute.refl C) age).eq
  change C*R=R*C at commuteR
  convert! generated using 1
  simp only [Function.comp_apply,neg_smul]
  simp only [mul_sub,sub_mul,smul_sub]
  have first : SourceFiniteUnitary.time C (-age)*R*C*J*R*SourceFiniteUnitary.time C age =
      SourceFiniteUnitary.time C (-age)*C*R*J*R*SourceFiniteUnitary.time C age := by
    calc
      _ = SourceFiniteUnitary.time C (-age)*(R*C)*J*R*SourceFiniteUnitary.time C age := by noncomm_ring
      _ = _ := by rw [←commuteR];noncomm_ring
  have second : SourceFiniteUnitary.time C (-age)*R*J*C*R*SourceFiniteUnitary.time C age =
      SourceFiniteUnitary.time C (-age)*R*J*R*SourceFiniteUnitary.time C age*C := by
    calc
      _ = SourceFiniteUnitary.time C (-age)*R*J*(C*R)*SourceFiniteUnitary.time C age := by noncomm_ring
      _ = SourceFiniteUnitary.time C (-age)*R*J*R*(C*SourceFiniteUnitary.time C age) := by
        rw [commuteR];noncomm_ring
      _ = _ := by rw [commuteT];noncomm_ring
  simp only [one_smul,mul_neg,neg_neg,mul_smul_comm,smul_mul_assoc,
    ←mul_assoc,first,second,sub_eq_add_neg]
/-- The original compression-reader residual at every actual field point. -/
def sourceEMAgeFieldKernel (event : DressedEvent) (age : ℝ) (h : Field289) : Op :=
  SourceFiniteUnitary.time (jointCompression event.momentum event.frame h) (-age)*
    jointCResolvent event.momentum event.frame event.energy h*
    (jointCompression event.momentum event.frame h*emTemporalReader event.momentum event.frame-
      emTemporalReader event.momentum event.frame*jointCompression event.momentum event.frame h)*
    jointCResolvent event.momentum event.frame event.energy h*
    SourceFiniteUnitary.time (jointCompression event.momentum event.frame h) age

/-- Both source inverse units and the actual EM observer germ pay the
whole-field age derivative on their original common neighborhood. -/
theorem source_em_actual_age_field_germ (event : DressedEvent) :
    ∀ᶠ h : Field289 in 𝓝 0, ∀ age : ℝ,
      HasDerivAt (fun t : ℝ => dressedEulerObserver event
        (dressedNoetherKernel event 0 (emGaugeField 0) t h))
        (dressedEulerObserver event (Complex.I • sourceEMAgeFieldKernel event age h)) age := by
  filter_upwards [actual_joint_free_units_near_zero event.momentum event.frame event.energy event.nonreal,
    actual_em_temporal_observer_germ event 0] with h unit same
  intro age
  let C := jointCompression event.momentum event.frame h
  let R := jointCResolvent event.momentum event.frame event.energy h
  let J := emTemporalReader event.momentum event.frame
  have commuting : Commute C R := by
    unfold R jointCResolvent
    exact inverse_commuting _ _ unit ((Commute.refl C).sub_right ((Commute.one_right C).smul_right _))
  have kernel := source_age_kernel_derivative C R J commuting age
  have read := ((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt age kernel
  have original : HasDerivAt (fun t : ℝ => dressedEulerObserver event (emTemporalFreeKernel event 0 t h))
      (dressedEulerObserver event (Complex.I • sourceEMAgeFieldKernel event age h)) age := by
    convert! read using 1
    · funext t
      simp only [ContinuousLinearMap.coe_restrictScalars',Function.comp_apply,emTemporalFreeKernel,sub_zero,C,R,J]
  apply original.congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => by rw [source_em_phase_field];exact same t)

/-- Five original driven factors: two time legs, two inverse legs, and
the complete all289 compression-reader residual insertion. -/
def sourceEMAgeFieldSlope (event : DressedEvent) (force : Field289) (age : ℝ) : Op :=
  let C := jointCompression event.momentum event.frame 0
  let R := jointCResolvent event.momentum event.frame event.energy 0
  let J := emTemporalReader event.momentum event.frame
  let B := freeCompressionCurrent event.momentum event.frame force
  let left := SourceFiniteUnitary.time C (-age)
  let right := SourceFiniteUnitary.time C age
  let core := C*J-J*C
  freeTimeSlope event.momentum event.frame force (-age)*R*core*R*right+
    left*(-(R*B*R))*core*R*right+
    left*R*(B*J-J*B)*R*right+
    left*R*core*(-(R*B*R))*right+
    left*R*core*R*freeTimeSlope event.momentum event.frame force age

theorem source_em_age_field_kernel_direction (event : DressedEvent) (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ => sourceEMAgeFieldKernel event age (r • force))
      (sourceEMAgeFieldSlope event force age) 0 := by
  have left := free_time_direction event.momentum event.frame force (-age)
  have green := free_green_direction event.momentum event.frame event.energy event.nonreal force
  have core := ((free_compression_direction event.momentum event.frame force).mul_const
    (emTemporalReader event.momentum event.frame)).sub
    ((free_compression_direction event.momentum event.frame force).const_mul
      (emTemporalReader event.momentum event.frame))
  have right := free_time_direction event.momentum event.frame force age
  have generated := ((((left.mul green).mul core).mul green).mul right)
  unfold sourceEMAgeFieldKernel sourceEMAgeFieldSlope
  convert! generated using 1
  simp only [zero_smul,Pi.mul_apply,Pi.sub_apply,add_mul]

/-- The original dressed Noether age derivative is differentiated in the
original force direction; both source mixed-derivative orders remain distinct. -/
theorem source_em_actual_noether_age_field_direction (event : DressedEvent)
    (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ => deriv (fun t : ℝ => dressedEulerObserver event
      (dressedNoetherKernel event 0 (emGaugeField 0) t (r • force))) age)
      (dressedEulerObserver event (Complex.I • sourceEMAgeFieldSlope event force age)) 0 := by
  have kernel := (source_em_age_field_kernel_direction event force age).const_smul Complex.I
  have read := ((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 kernel
  have ray : Tendsto (fun r : ℝ => r • force) (𝓝 0) (𝓝 (0 : Field289)) := by
    simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto
  apply read.congr_of_eventuallyEq
  filter_upwards [ray.eventually (source_em_actual_age_field_germ event)] with r actual
  exact (actual age).deriv

end LowEnergy.GaussComposite.ActualSourcePreparedEMAgeFieldReturn
