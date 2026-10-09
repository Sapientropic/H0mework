import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Extract.Port
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.Timeline
open Collision Quantum Load.Producer.StrictThermal
open Blocks.EnergyFrame Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

attribute [local irreducible] Weak.execution pointerControlHamiltonian Pointer.baselineHamiltonian initialJoint controlledJoint

/-- The post-quench load continues the same quantum occurrence; the switch takes no elapsed time. -/
def loadPath (initial time : ℝ) : ClockBody :=
  ⟨conjugation (Pointer.loadPulse (time-(nativeClockStep : ℝ))) controlledJoint,time,sourceOff initial⟩

def beforePath (initial time : ℝ) : ClockBody :=
  ⟨conjugation (Pointer.loadPulse time) initialJoint,time,initial⟩

def atTime (initial time : ℝ) : ClockBody :=
  if time < 0 then beforePath initial time else
    if time < (nativeClockStep : ℝ) then pulsePath initial time else loadPath initial time

def hamiltonianAt (time : ℝ) : PointerJoint :=
  if time < 0 then Pointer.baselineHamiltonian else
    if time < (nativeClockStep : ℝ) then pointerControlHamiltonian else Pointer.baselineHamiltonian

private theorem flow_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H rho : Matrix ι ι ℂ) : bodyFlow H rho 0=rho := by
  simp [bodyFlow,hamiltonianFlow]

theorem load_body_flow (initial time : ℝ) :
    (loadPath initial time).body=bodyFlow Pointer.baselineHamiltonian controlledJoint (time-(nativeClockStep : ℝ)) := by
  rw [loadPath,conjugation_apply,Pointer.loadPulse_baseline]
  rfl

theorem load_body_derivative (initial time : ℝ) :
    HasDerivAt (fun t => (loadPath initial t).body)
      (-Complex.I • (Pointer.baselineHamiltonian*(loadPath initial time).body-
        (loadPath initial time).body*Pointer.baselineHamiltonian)) time := by
  simp only [load_body_flow]
  have shift : HasDerivAt (fun s : ℝ => s-(nativeClockStep : ℝ)) 1 time := by
    simpa only [id_eq] using! ((hasDerivAt_id time).sub_const (nativeClockStep : ℝ))
  have h := (body_flow_liouville Pointer.baselineHamiltonian controlledJoint
    Pointer.baselineHamiltonian_hermitian (time-(nativeClockStep : ℝ))).scomp time shift
  simpa only [Function.comp_apply,id_eq,one_smul] using! h

theorem jump_preserves_body (initial : ℝ) :
    (pulsePath initial (nativeClockStep : ℝ)).body=(loadPath initial (nativeClockStep : ℝ)).body := by
  rw [load_body_flow,sub_self,flow_zero]
  rw [pulsePath,controlledJoint]

theorem jump_integrates_force (initial : ℝ) :
    (loadPath initial (nativeClockStep : ℝ)).momentum-
      (pulsePath initial (nativeClockStep : ℝ)).momentum =
        ∫ _x in (0 : ℝ)..1, force pointerControlHamiltonian Pointer.baselineHamiltonian
          (pulsePath initial (nativeClockStep : ℝ)).body := by
  have body : (pulsePath initial (nativeClockStep : ℝ)).body=controlledJoint := by
    rw [pulsePath,controlledJoint]
  rw [body]
  exact momentum_path_integral pointerControlHamiltonian Pointer.baselineHamiltonian controlledJoint (sourceOn initial)

theorem load_energy_preserved (time : ℝ) (rho : PointerJoint) :
    energy Pointer.baselineHamiltonian (conjugation (Pointer.loadPulse time) rho)=
      energy Pointer.baselineHamiltonian rho := by
  have commutes := matrix_generator_commutes Pointer.baselineHamiltonian time
  rw [← Pointer.loadPulse_baseline] at commutes
  simpa only [conjugation_apply] using
    PreparationEnergy.commuting_energy Pointer.baselineHamiltonian rho (Pointer.loadPulse time) commutes

theorem on_energy_conserved (initial time : ℝ) (paid : preparationBudget < initial) :
    energy pointerControlHamiltonian (pulsePath initial time).body+kinetic (pulsePath initial time).momentum =
      energy Pointer.baselineHamiltonian (prepared initial).body+kinetic (prepared initial).momentum := by
  have initialPositive : 0 < initial := lt_of_le_of_lt (mul_nonneg (by norm_num) switching_size_nonnegative) paid
  have onPositive : 0 < sourceOn initial := prepared_on_positive initial 1 paid (by norm_num) (by norm_num)
  simp only [pulsePath,prepared,kinetic,abs_of_pos initialPositive,abs_of_pos onPositive,
    pointer_control_conserved]
  exact source_on_balance initial

theorem off_energy_conserved (initial time : ℝ) (paid : preparationBudget < initial) :
    energy Pointer.baselineHamiltonian (loadPath initial time).body+kinetic (loadPath initial time).momentum =
      energy Pointer.baselineHamiltonian (prepared initial).body+kinetic (prepared initial).momentum := by
  simp only [loadPath,load_energy_preserved]
  exact complete_port_energy initial paid

theorem full_energy_conserved (initial time : ℝ) (paid : preparationBudget < initial) :
    energy (hamiltonianAt time) (atTime initial time).body+kinetic (atTime initial time).momentum =
      energy Pointer.baselineHamiltonian (prepared initial).body+kinetic (prepared initial).momentum := by
  by_cases before : time < 0
  · simp only [atTime,hamiltonianAt,if_pos before,beforePath,load_energy_preserved,prepared]
  · by_cases on : time < (nativeClockStep : ℝ)
    · simpa only [atTime,hamiltonianAt,if_neg before,if_pos on] using on_energy_conserved initial time paid
    · simpa only [atTime,hamiltonianAt,if_neg before,if_neg on] using off_energy_conserved initial time paid

theorem at_extraction_clock (initial : ℝ) :
    atTime initial (nativeClockStep : ℝ)=completed initial := by
  rw [atTime,if_neg (not_lt.mpr nativeClock_small.1.le),if_neg (lt_irrefl _)]
  have body : (loadPath initial (nativeClockStep : ℝ)).body=(completed initial).body := by
    rw [load_body_flow,sub_self,flow_zero]
    rfl
  exact congrArg (fun rho => ClockBody.mk rho (nativeClockStep : ℝ) (sourceOff initial)) body

theorem all_after_output (initial time : ℝ) (paid : preparationBudget < initial)
    (after : (nativeClockStep : ℝ) ≤ time) :
    (7/5 : ℝ) < kinetic (atTime initial time).momentum-kinetic (prepared initial).momentum := by
  rw [atTime,if_neg (not_lt.mpr (nativeClock_small.1.le.trans after)),if_neg (not_lt.mpr after)]
  exact receiver_energy_gain_positive initial paid

theorem before_body_flow (initial time : ℝ) :
    (beforePath initial time).body=bodyFlow Pointer.baselineHamiltonian initialJoint time := by
  rw [beforePath,conjugation_apply,Pointer.loadPulse_baseline]
  rfl

theorem before_body_derivative (initial time : ℝ) :
    HasDerivAt (fun t => (beforePath initial t).body)
      (-Complex.I • (Pointer.baselineHamiltonian*(beforePath initial time).body-
        (beforePath initial time).body*Pointer.baselineHamiltonian)) time := by
  simpa only [before_body_flow] using!
    body_flow_liouville Pointer.baselineHamiltonian initialJoint Pointer.baselineHamiltonian_hermitian time

theorem first_jump_preserves_body (initial : ℝ) :
    (beforePath initial 0).body=(pulsePath initial 0).body := by
  rw [before_body_flow,pulse_body_flow,flow_zero,flow_zero]

theorem first_jump_integrates_force (initial : ℝ) :
    (pulsePath initial 0).momentum-(beforePath initial 0).momentum =
      ∫ _x in (0 : ℝ)..1, force Pointer.baselineHamiltonian pointerControlHamiltonian
        (beforePath initial 0).body := by
  rw [before_body_flow,flow_zero]
  exact momentum_path_integral Pointer.baselineHamiltonian pointerControlHamiltonian initialJoint initial

theorem classical_position (initial time : ℝ) : (atTime initial time).position=time := by
  simp only [atTime,beforePath,pulsePath,loadPath]
  split_ifs <;> rfl

theorem clock_equation (initial time : ℝ) :
    HasDerivAt (fun t => (atTime initial t).position) 1 time := by
  simpa only [classical_position] using! hasDerivAt_id time

theorem quantum_equation (initial time : ℝ) (first : time ≠ 0)
    (last : time ≠ (nativeClockStep : ℝ)) :
    HasDerivAt (fun t => (atTime initial t).body)
      (-Complex.I • (hamiltonianAt time*(atTime initial time).body-
        (atTime initial time).body*hamiltonianAt time)) time := by
  by_cases before : time < 0
  · have near : (fun t => (atTime initial t).body) =ᶠ[nhds time] (fun t => (beforePath initial t).body) := by
      filter_upwards [Iio_mem_nhds before] with t ht
      change t < 0 at ht
      simp only [atTime,if_pos ht]
    simpa only [hamiltonianAt,if_pos before,near.eq_of_nhds] using!
      (before_body_derivative initial time).congr_of_eventuallyEq near
  · have positive : 0 < time := lt_of_le_of_ne (not_lt.mp before) (Ne.symm first)
    by_cases during : time < (nativeClockStep : ℝ)
    · have near : (fun t => (atTime initial t).body) =ᶠ[nhds time] (fun t => (pulsePath initial t).body) := by
        filter_upwards [Ioi_mem_nhds positive,Iio_mem_nhds during] with t lo hi
        change 0 < t at lo
        change t < (nativeClockStep : ℝ) at hi
        simp only [atTime,if_neg (not_lt.mpr lo.le),if_pos hi]
      simpa only [hamiltonianAt,if_neg before,if_pos during,near.eq_of_nhds] using!
        (source_quantum_equation initial time).congr_of_eventuallyEq near
    · have after : (nativeClockStep : ℝ) < time := lt_of_le_of_ne (not_lt.mp during) (Ne.symm last)
      have near : (fun t => (atTime initial t).body) =ᶠ[nhds time] (fun t => (loadPath initial t).body) := by
        filter_upwards [Ioi_mem_nhds after] with t ht
        change (nativeClockStep : ℝ) < t at ht
        simp only [atTime,if_neg (not_lt.mpr (nativeClock_small.1.le.trans ht.le)),if_neg (not_lt.mpr ht.le)]
      simpa only [hamiltonianAt,if_neg before,if_neg during,near.eq_of_nhds] using!
        (load_body_derivative initial time).congr_of_eventuallyEq near

theorem momentum_positive (initial time : ℝ) (paid : preparationBudget < initial) :
    0 < (atTime initial time).momentum := by
  rw [atTime]
  split_ifs
  · exact lt_of_le_of_lt (mul_nonneg (by norm_num) switching_size_nonnegative) paid
  · exact prepared_on_positive initial 1 paid (by norm_num) (by norm_num)
  · exact prepared_off_positive initial 1 paid (by norm_num) (by norm_num)

theorem body_continuous (initial : ℝ) : Continuous (fun t => (atTime initial t).body) := by
  have pulseContinuous : Continuous (fun t => (pulsePath initial t).body) :=
    continuous_iff_continuousAt.mpr (fun t => (source_quantum_equation initial t).continuousAt)
  have loadContinuous : Continuous (fun t => (loadPath initial t).body) :=
    continuous_iff_continuousAt.mpr (fun t => (load_body_derivative initial t).continuousAt)
  have beforeContinuous : Continuous (fun t => (beforePath initial t).body) :=
    continuous_iff_continuousAt.mpr (fun t => (before_body_derivative initial t).continuousAt)
  have tailContinuous : Continuous (fun t => if t < (nativeClockStep : ℝ) then
      (pulsePath initial t).body else (loadPath initial t).body) := by
    apply pulseContinuous.if _ loadContinuous
    intro t ht
    change t ∈ frontier (Set.Iio (nativeClockStep : ℝ)) at ht
    have point : t=(nativeClockStep : ℝ) := by simpa only [frontier_Iio,Set.mem_singleton_iff] using ht
    subst t
    exact jump_preserves_body initial
  have whole : Continuous (fun t => if t < 0 then (beforePath initial t).body else
      if t < (nativeClockStep : ℝ) then (pulsePath initial t).body else (loadPath initial t).body) := by
    apply beforeContinuous.if _ tailContinuous
    intro t ht
    change t ∈ frontier (Set.Iio (0 : ℝ)) at ht
    have point : t=0 := by simpa only [frontier_Iio,Set.mem_singleton_iff] using ht
    subst t
    rw [if_pos nativeClock_small.1]
    exact first_jump_preserves_body initial
  apply whole.congr
  intro t
  by_cases before : t < 0
  · simp only [atTime,if_pos before]
  · by_cases during : t < (nativeClockStep : ℝ)
    · simp only [atTime,if_neg before,if_pos during]
    · simp only [atTime,if_neg before,if_neg during]

private theorem step_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c : E) (time : ℝ) (first : time ≠ 0) (last : time ≠ (nativeClockStep : ℝ)) :
    HasDerivAt (fun t : ℝ => if t < 0 then a else if t < (nativeClockStep : ℝ) then b else c) 0 time := by
  by_cases before : time < 0
  · apply (hasDerivAt_const time a).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds before] with t ht
    change t < 0 at ht
    exact if_pos ht
  · have positive : 0 < time := lt_of_le_of_ne (not_lt.mp before) (Ne.symm first)
    by_cases during : time < (nativeClockStep : ℝ)
    · apply (hasDerivAt_const time b).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds positive,Iio_mem_nhds during] with t lo hi
      change 0 < t at lo
      change t < (nativeClockStep : ℝ) at hi
      simp only [if_neg (not_lt.mpr lo.le),if_pos hi]
    · have after : (nativeClockStep : ℝ) < time := lt_of_le_of_ne (not_lt.mp during) (Ne.symm last)
      apply (hasDerivAt_const time c).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds after] with t ht
      change (nativeClockStep : ℝ) < t at ht
      simp only [if_neg (not_lt.mpr (nativeClock_small.1.le.trans ht.le)),if_neg (not_lt.mpr ht.le)]

theorem momentum_equation (initial time : ℝ) (first : time ≠ 0)
    (last : time ≠ (nativeClockStep : ℝ)) :
    HasDerivAt (fun t => (atTime initial t).momentum) 0 time := by
  have presentation : (fun t => (atTime initial t).momentum)=
      fun t => if t < 0 then initial else if t < (nativeClockStep : ℝ) then sourceOn initial else sourceOff initial := by
    funext t
    rw [atTime]
    split_ifs <;> rfl
  rw [presentation]
  exact step_derivative initial (sourceOn initial) (sourceOff initial) time first last

theorem hamiltonian_derivative (time : ℝ) (first : time ≠ 0)
    (last : time ≠ (nativeClockStep : ℝ)) : HasDerivAt hamiltonianAt 0 time :=
  step_derivative Pointer.baselineHamiltonian pointerControlHamiltonian Pointer.baselineHamiltonian time first last

theorem at_next_load_clock (initial : ℝ) :
    (atTime initial (2*(nativeClockStep : ℝ))).body=(Runtime.readCurrent Runtime.afterSecond).joint := by
  have after : (nativeClockStep : ℝ) ≤ 2*(nativeClockStep : ℝ) := by linarith [nativeClock_small.1]
  rw [atTime,if_neg (not_lt.mpr (nativeClock_small.1.le.trans after)),if_neg (not_lt.mpr after)]
  change conjugation (Pointer.loadPulse (2*(nativeClockStep : ℝ)-(nativeClockStep : ℝ))) controlledJoint=_
  rw [show 2*(nativeClockStep : ℝ)-(nativeClockStep : ℝ)=(nativeClockStep : ℝ) by ring]
  rw [controlled_joint_exact,Runtime.actual_sequence.2.2,Runtime.actual_sequence.2.1,Live.loadNext_joint]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.Timeline
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
