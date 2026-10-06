import H0mework.Versions.AB.Physics.LowEnergyEvolution.Generator

/-! The local existence engine is consumed on every admissible source state. Positivity of
the reconstructed coframe and clock is retained on the generated interval. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open scoped ContDiff Topology
noncomputable section

structure Solution (initial : State) extends LocalOrbit initial where
  admissible : ∀ time ∈ Set.Ioo (-radius) radius, Admissible (curve time)
  smooth : ContDiffOn ℝ ∞ curve (Set.Ioo (-radius) radius)

theorem initialSolution_exists (initial : State) (admissible : Admissible initial) :
    Nonempty (Solution initial) := by
  obtain ⟨raw⟩ := initialLocalOrbit_exists initial admissible
  have origin : (0 : ℝ) ∈ Set.Ioo (-raw.radius) raw.radius :=
    ⟨neg_neg_of_pos raw.positive, raw.positive⟩
  have continuous := (raw.evolves 0 origin).continuousAt
  have source : {x : State | Admissible x} ∈ 𝓝 (raw.curve 0) := by
    rw [raw.starts]
    exact admissible_isOpen.mem_nhds admissible
  have near : {t : ℝ | Admissible (raw.curve t)} ∈ 𝓝 (0 : ℝ) := continuous source
  obtain ⟨delta, delta_positive, ball⟩ := Metric.mem_nhds_iff.mp near
  let radius := min raw.radius delta / 2
  have positive : 0 < radius := div_pos (lt_min raw.positive delta_positive) (by norm_num)
  have smaller : radius < raw.radius ∧ radius < delta := by
    have first := min_le_left raw.radius delta
    have second := min_le_right raw.radius delta
    dsimp [radius] at *
    constructor <;> linarith
  have inside (time : ℝ) (ht : time ∈ Set.Icc (-radius) radius) :
      time ∈ Set.Ioo (-raw.radius) raw.radius := by
    constructor <;> linarith [ht.1, ht.2, smaller.1]
  have guard (time : ℝ) (ht : time ∈ Set.Icc (-radius) radius) :
      Admissible (raw.curve time) := by
    apply ball
    have bound : |time| ≤ radius := abs_le.mpr ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt bound smaller.2
  have generator_smooth : ContDiffOn ℝ ∞
      (Function.uncurry (fun (_ : ℝ) (x : State) => generator x))
      (Set.Icc (-radius) radius ×ˢ {x : State | Admissible x}) := by
    intro point hpoint
    exact ((generator_contDiffAt point.2 hpoint.2).comp point contDiffAt_snd).contDiffWithinAt
  have smooth : ContDiffOn ℝ ∞ raw.curve (Set.Icc (-radius) radius) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt generator_smooth
      (fun time ht => (raw.evolves time (inside time ht)).hasDerivWithinAt) guard
  exact ⟨{
    radius := radius
    positive := positive
    curve := raw.curve
    starts := raw.starts
    evolves := fun time ht => raw.evolves time (inside time ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    admissible := fun time ht => guard time ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    smooth := smooth.mono Set.Ioo_subset_Icc_self }⟩

theorem solution_exists (parameter : ℝ) : Nonempty (Solution (seed parameter)) :=
  initialSolution_exists (seed parameter) (seed_admissible parameter)

def initialSolution (initial : State) (admissible : Admissible initial) : Solution initial :=
  Classical.choice (initialSolution_exists initial admissible)

def solution (parameter : ℝ) : Solution (seed parameter) :=
  initialSolution (seed parameter) (seed_admissible parameter)

theorem initialSolution_initial (initial : State) (admissible : Admissible initial) :
    (initialSolution initial admissible).curve 0 = initial :=
  (initialSolution initial admissible).starts

theorem Solution.initial_evolution {initial : State} (flow : Solution initial) :
    HasDerivAt flow.curve (generator initial) 0 := by
  have derivative := flow.evolves 0 ⟨neg_neg_of_pos flow.positive, flow.positive⟩
  simpa only [flow.starts] using derivative

theorem source_initial (parameter : ℝ) : (solution parameter).curve 0 = seed parameter :=
  (solution parameter).starts

theorem source_clock (parameter : ℝ) : clock ((solution parameter).curve 0) = Contact.Slice.clock parameter := by
  rw [source_initial, clock_seed]

theorem source_evolution (parameter time : ℝ)
    (inside : time ∈ Set.Ioo (-(solution parameter).radius) (solution parameter).radius) :
    HasDerivAt (solution parameter).curve (generator ((solution parameter).curve time)) time ∧
      Admissible ((solution parameter).curve time) :=
  ⟨(solution parameter).evolves time inside, (solution parameter).admissible time inside⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
