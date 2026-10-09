import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
open FiniteContinuation
noncomputable section
abbrev Phase := FiniteContinuation.Phase

-- The receiver coordinate is a control clock; its conjugate quantity has energy units.
def receiverJoule (current : Material) (phase : Phase) (second : ℝ) : ℝ :=
  energyJoule*receiver current phase (second/timeSecond)

def receiverPower (current : Material) (phase : Phase) (second : ℝ) : ℝ :=
  energyJoule/timeSecond*receiverForce current phase (second/timeSecond)

def segmentSeconds : ℝ := duration*timeSecond

theorem segment_positive : 0 < segmentSeconds := mul_pos FiniteActuation.duration_positive time_positive

theorem receiver_equation_si (current : Material) (phase : Phase) (second : ℝ) :
    HasDerivAt (receiverJoule current phase) (receiverPower current phase second) second := by
  have clock := (hasDerivAt_id second).div_const timeSecond
  have change := ((receiver_equation current phase (second/timeSecond)).comp second clock).const_mul energyJoule
  unfold receiverJoule receiverPower
  convert change using 1 <;> first | rfl | ring

theorem receiver_integral_si (current : Material) (phase : Phase) :
    receiverJoule current phase segmentSeconds-receiverJoule current phase 0=
      ∫ second in (0 : ℝ)..segmentSeconds, receiverPower current phase second := by
  have regular : Continuous (receiverPower current phase) := by
    unfold receiverPower FiniteContinuation.receiverForce FiniteContinuation.kineticRate
      FiniteActuation.progress FiniteActuation.progressRate
    cases phase <;> fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun second _ => receiver_equation_si current phase second) (regular.intervalIntegrable 0 segmentSeconds)).symm

theorem receiver_endpoints_si (current : Material) (valid : Admissible current) :
    receiverJoule current .enter 0=energyJoule*current.body.resource.momentum ∧
    receiverJoule current .leave segmentSeconds=energyJoule*(nextMaterial current).body.resource.momentum := by
  constructor
  · simp [receiverJoule,receiver]
  · rw [receiverJoule,segmentSeconds,mul_div_cancel_right₀ _ time_positive.ne']
    exact congrArg (energyJoule*·) (receiver_endpoints current valid).2

theorem total_receiver_integral_si (current : Material) (valid : Admissible current) :
    energyJoule*(nextMaterial current).body.resource.momentum-energyJoule*current.body.resource.momentum=
      (∫ second in (0 : ℝ)..segmentSeconds, receiverPower current .enter second)+
      (∫ second in (0 : ℝ)..segmentSeconds, receiverPower current .drive second)+
      (∫ second in (0 : ℝ)..segmentSeconds, receiverPower current .leave second) := by
  rw [← receiver_integral_si,← receiver_integral_si,← receiver_integral_si]
  have first := (receiver_endpoints_si current valid).1
  have last := (receiver_endpoints_si current valid).2
  have join0 : receiverJoule current .enter segmentSeconds=receiverJoule current .drive 0 := by
    simp only [receiverJoule,segmentSeconds,mul_div_cancel_right₀ _ time_positive.ne',zero_div]
    exact congrArg (energyJoule*·) (state_junctions current).2.2.2.2.1
  have join1 : receiverJoule current .drive segmentSeconds=receiverJoule current .leave 0 := by
    simp only [receiverJoule,segmentSeconds,mul_div_cancel_right₀ _ time_positive.ne',zero_div]
    exact congrArg (energyJoule*·) (state_junctions current).2.2.2.2.2.1
  linarith only [first,last,join0,join1]

theorem source_actual_work_positive :
    0 < energyJoule*sourceMaterial.body.resource.momentum-
      energyJoule*(FiniteContinuation.Runtime.readCurrent sourceRuntime.tick.next).body.resource.momentum := by
  have debit := (FiniteContinuation.Runtime.actual_change sourceRuntime).2.2
  exact sub_pos.mpr (mul_lt_mul_of_pos_left debit energy_positive)

theorem source_actual_work_integrated :
    energyJoule*(FiniteContinuation.Runtime.readCurrent sourceRuntime.tick.next).body.resource.momentum-
      energyJoule*sourceMaterial.body.resource.momentum=
      (∫ second in (0 : ℝ)..segmentSeconds, receiverPower sourceMaterial .enter second)+
      (∫ second in (0 : ℝ)..segmentSeconds, receiverPower sourceMaterial .drive second)+
      (∫ second in (0 : ℝ)..segmentSeconds, receiverPower sourceMaterial .leave second) :=
  total_receiver_integral_si sourceMaterial (FiniteContinuation.Runtime.current_admissible sourceRuntime)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
