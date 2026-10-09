import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Receiver

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
open FiniteContinuation
noncomputable section

def positionMeter (current : Material) (phase : Phase) (second : ℝ) (i : Coordinate) : ℝ :=
  lengthMeter*nuclearPosition current phase (second/timeSecond) i

def momentumPathSI (current : Material) (phase : Phase) (second : ℝ) (i : Coordinate) : ℝ :=
  momentumSI*nuclearMomentum current phase (second/timeSecond) i

def velocitySI (current : Material) (phase : Phase) (second : ℝ) (i : Coordinate) : ℝ :=
  lengthMeter/timeSecond*velocity current phase (second/timeSecond) i

def forceNewton (current : Material) (phase : Phase) (second : ℝ) (i : Coordinate) : ℝ :=
  momentumSI/timeSecond*nuclearForce current phase (second/timeSecond) i

def nucleusMassKilogram (i : Coordinate) : ℝ := massKilogram*mass i

def kineticJoule (momentum : Configuration) : ℝ := ∑ i, momentum i^2/(2*nucleusMassKilogram i)

theorem nucleus_mass_positive (i : Coordinate) : 0 < nucleusMassKilogram i :=
  mul_pos mass_positive (ReceiverBody.mass_positive i)

theorem kinetic_from_physical_momenta (momentum : Configuration) :
    kineticJoule (fun i => momentumSI*momentum i)=energyJoule*nuclearKinetic momentum := by
  unfold kineticJoule nuclearKinetic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← kinetic_units]
  unfold nucleusMassKilogram
  field_simp

theorem momentum_rate_units : momentumSI/timeSecond=energyJoule/lengthMeter := by
  unfold timeSecond momentumSI
  field_simp [hbar_positive.ne',energy_positive.ne',length_positive.ne']

theorem hamilton_velocity_units : energyJoule/momentumSI=lengthMeter/timeSecond := by
  unfold timeSecond momentumSI
  field_simp [hbar_positive.ne',energy_positive.ne',length_positive.ne']

theorem position_equation_si (current : Material) (phase : Phase) (second : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => positionMeter current phase time i) (velocitySI current phase second i) second := by
  have clock := (hasDerivAt_id second).div_const timeSecond
  have generated := ((position_equation current phase (second/timeSecond) i).comp second clock).const_mul lengthMeter
  unfold positionMeter velocitySI
  convert generated using 1 <;> first | rfl | ring

theorem momentum_equation_si (current : Material) (phase : Phase) (second : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => momentumPathSI current phase time i) (forceNewton current phase second i) second := by
  have clock := (hasDerivAt_id second).div_const timeSecond
  have generated := ((momentum_equation current phase (second/timeSecond) i).comp second clock).const_mul momentumSI
  unfold momentumPathSI forceNewton
  convert generated using 1 <;> first | rfl | ring

theorem position_integral_si (current : Material) (phase : Phase) (i : Coordinate) :
    positionMeter current phase segmentSeconds i-positionMeter current phase 0 i=
      ∫ second in (0 : ℝ)..segmentSeconds, velocitySI current phase second i := by
  have regular : Continuous (fun second => velocitySI current phase second i) := by
    unfold velocitySI FiniteContinuation.velocity FiniteActuation.onRate FiniteActuation.offRate
      FiniteActuation.rampMomentum FiniteActuation.onTime FiniteActuation.offTime
    cases phase <;> fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun second _ => position_equation_si current phase second i) (regular.intervalIntegrable 0 segmentSeconds)).symm

theorem momentum_integral_si (current : Material) (phase : Phase) (i : Coordinate) :
    momentumPathSI current phase segmentSeconds i-momentumPathSI current phase 0 i=
      ∫ second in (0 : ℝ)..segmentSeconds, forceNewton current phase second i := by
  have regular : Continuous (fun second => forceNewton current phase second i) := by
    unfold forceNewton FiniteContinuation.nuclearForce FiniteContinuation.pulseForce
      FiniteActuation.onRate FiniteActuation.offRate FiniteActuation.progressRate
    cases phase <;> fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun second _ => momentum_equation_si current phase second i) (regular.intervalIntegrable 0 segmentSeconds)).symm

theorem momentum_endpoints_si (current : Material) (valid : Admissible current) (i : Coordinate) :
    momentumPathSI current .enter 0 i=momentumSI*(current.body.frame.momentum i.1 i.2 : ℝ) ∧
    momentumPathSI current .leave segmentSeconds i=momentumSI*((nextMaterial current).body.frame.momentum i.1 i.2 : ℝ) := by
  constructor
  · simp only [momentumPathSI,zero_div,(source_endpoints current valid i).2.1]
  · simp only [momentumPathSI,segmentSeconds,mul_div_cancel_right₀ _ time_positive.ne',
      (target_endpoints current valid i).2.1]

theorem total_momentum_integral_si (current : Material) (valid : Admissible current) (i : Coordinate) :
    momentumSI*((nextMaterial current).body.frame.momentum i.1 i.2 : ℝ)-momentumSI*(current.body.frame.momentum i.1 i.2 : ℝ)=
      (∫ second in (0 : ℝ)..segmentSeconds, forceNewton current .enter second i)+
      (∫ second in (0 : ℝ)..segmentSeconds, forceNewton current .drive second i)+
      (∫ second in (0 : ℝ)..segmentSeconds, forceNewton current .leave second i) := by
  rw [← momentum_integral_si,← momentum_integral_si,← momentum_integral_si]
  have first := (momentum_endpoints_si current valid i).1
  have last := (momentum_endpoints_si current valid i).2
  have join0 : momentumPathSI current .enter segmentSeconds i=momentumPathSI current .drive 0 i := by
    simp only [momentumPathSI,segmentSeconds,mul_div_cancel_right₀ _ time_positive.ne',zero_div]
    exact congrArg (momentumSI*·) (congrFun (state_junctions current).2.2.1 i)
  have join1 : momentumPathSI current .drive segmentSeconds i=momentumPathSI current .leave 0 i := by
    simp only [momentumPathSI,segmentSeconds,mul_div_cancel_right₀ _ time_positive.ne',zero_div]
    exact congrArg (momentumSI*·) (congrFun (state_junctions current).2.2.2.1 i)
  linarith only [first,last,join0,join1]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
