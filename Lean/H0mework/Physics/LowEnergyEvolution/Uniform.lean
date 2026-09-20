import H0mework.Physics.LowEnergyEvolution.Full

/-! Picard-generated common time and initial-data neighborhoods for the same nine-field solution. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineDiracDualFormNativeJointResidualCarrier Set Filter Metric
open scoped Topology ContDiff NNReal
noncomputable section

structure UniformDevelopment (base : State) where
  initialRadius : ℝ
  initialPositive : 0 < initialRadius
  timeRadius : ℝ
  timePositive : 0 < timeRadius
  curve : State → ℝ → State
  starts : ∀ initial ∈ closedBall base initialRadius, curve initial 0 = initial
  evolves : ∀ initial ∈ closedBall base initialRadius,
    ∀ time ∈ Ioo (-timeRadius) timeRadius, HasDerivAt (curve initial) (generator (curve initial time)) time
  admissible : ∀ initial ∈ closedBall base initialRadius,
    ∀ time ∈ Ioo (-timeRadius) timeRadius, Admissible (curve initial time)
  smooth : ∀ initial ∈ closedBall base initialRadius,
    ContDiffOn ℝ ∞ (curve initial) (Ioo (-timeRadius) timeRadius)
  dependenceConstant : ℝ≥0
  lipschitz : ∀ time ∈ Ioo (-timeRadius) timeRadius,
    LipschitzOnWith dependenceConstant (curve · time) (closedBall base initialRadius)

def UniformDevelopment.solution {base : State} (family : UniformDevelopment base)
    (initial : State) (inside : initial ∈ closedBall base family.initialRadius) : Solution initial where
  radius := family.timeRadius
  positive := family.timePositive
  curve := family.curve initial
  starts := family.starts initial inside
  evolves := family.evolves initial inside
  admissible := family.admissible initial inside
  smooth := family.smooth initial inside

theorem uniformDevelopment_exists (base : State) (allowed : Admissible base) :
    Nonempty (UniformDevelopment base) := by
  have smooth : ContDiffAt ℝ 1 generator base :=
    (generator_contDiffAt base allowed).of_le (by simp)
  obtain ⟨time, timePositive, a, r, L, K, rPositive, picard⟩ := IsPicardLindelof.of_contDiffAt_one smooth
  obtain ⟨curve, evolution, C, lipschitz⟩ :=
    (picard 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  simp only [zero_sub, zero_add] at evolution lipschitz
  have rPositiveReal : 0 < (r : ℝ) := rPositive
  have continuous : ContinuousOn (Function.uncurry curve) (closedBall base (r:ℝ) ×ˢ Icc (-time) time) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ C _ lipschitz
    exact fun initial inside => HasDerivWithinAt.continuousOn (evolution initial inside).2
  have domain : closedBall base (r:ℝ) ×ˢ Icc (-time) time ∈ 𝓝 (base, (0:ℝ)) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (closedBall_mem_nhds base rPositiveReal) (Icc_mem_nhds (by linarith) timePositive)
  have initialValue : Function.uncurry curve (base, (0:ℝ)) = base :=
    (evolution base (mem_closedBall_self (le_of_lt rPositiveReal))).1
  have near : {p : State × ℝ | Admissible (curve p.1 p.2)} ∈ 𝓝 (base,(0:ℝ)) := by
    change Function.uncurry curve ⁻¹' {x : State | Admissible x} ∈ 𝓝 (base,(0:ℝ))
    apply (continuous.continuousAt domain).preimage_mem_nhds
    rw [initialValue]
    exact admissible_isOpen.mem_nhds allowed
  obtain ⟨delta, deltaPositive, localAllowed⟩ := Metric.mem_nhds_iff.mp near
  let initialRadius := min (r:ℝ) delta / 2
  let timeRadius := min time delta / 2
  have initialPositive : 0 < initialRadius := div_pos (lt_min rPositiveReal deltaPositive) (by norm_num)
  have timeRadiusPositive : 0 < timeRadius := div_pos (lt_min timePositive deltaPositive) (by norm_num)
  have initialSmaller : initialRadius < (r:ℝ) ∧ initialRadius < delta := by
    have left := min_le_left (r:ℝ) delta
    have right := min_le_right (r:ℝ) delta
    dsimp [initialRadius] at *
    constructor <;> linarith
  have timeSmaller : timeRadius < time ∧ timeRadius < delta := by
    have left := min_le_left time delta
    have right := min_le_right time delta
    dsimp [timeRadius] at *
    constructor <;> linarith
  have initialSubset : closedBall base initialRadius ⊆ closedBall base (r:ℝ) :=
    closedBall_subset_closedBall (le_of_lt initialSmaller.1)
  have temporal (t : ℝ) (inside : t ∈ Icc (-timeRadius) timeRadius) : t ∈ Ioo (-time) time := by
    constructor <;> linarith [inside.1, inside.2, timeSmaller.1]
  have guard (initial : State) (inside : initial ∈ closedBall base initialRadius)
      (t : ℝ) (timeInside : t ∈ Icc (-timeRadius) timeRadius) : Admissible (curve initial t) := by
    change (initial,t) ∈ {p : State × ℝ | Admissible (curve p.1 p.2)}
    apply localAllowed
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt (lt_of_le_of_lt inside initialSmaller.2)
      (lt_of_le_of_lt (abs_le.mpr timeInside) timeSmaller.2)
  have derivative (initial : State) (inside : initial ∈ closedBall base initialRadius)
      (t : ℝ) (timeInside : t ∈ Icc (-timeRadius) timeRadius) :
      HasDerivAt (curve initial) (generator (curve initial t)) t :=
    (evolution initial (initialSubset inside)).2 t (Ioo_subset_Icc_self (temporal t timeInside))
      |>.hasDerivAt (Icc_mem_nhds (temporal t timeInside).1 (temporal t timeInside).2)
  have generatorSmooth : ContDiffOn ℝ ∞
      (Function.uncurry (fun (_ : ℝ) (x : State) => generator x))
      (Icc (-timeRadius) timeRadius ×ˢ {x : State | Admissible x}) := by
    intro point inside
    exact ((generator_contDiffAt point.2 inside.2).comp point contDiffAt_snd).contDiffWithinAt
  have curveSmooth (initial : State) (inside : initial ∈ closedBall base initialRadius) :
      ContDiffOn ℝ ∞ (curve initial) (Ioo (-timeRadius) timeRadius) := by
    have closed := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt generatorSmooth
      (fun t ht => (derivative initial inside t ht).hasDerivWithinAt) (guard initial inside)
    exact closed.mono Ioo_subset_Icc_self
  exact ⟨{
    initialRadius := initialRadius
    initialPositive := initialPositive
    timeRadius := timeRadius
    timePositive := timeRadiusPositive
    curve := curve
    starts := fun initial inside => (evolution initial (initialSubset inside)).1
    evolves := fun initial inside t ht => derivative initial inside t (Ioo_subset_Icc_self ht)
    admissible := fun initial inside t ht => guard initial inside t (Ioo_subset_Icc_self ht)
    smooth := curveSmooth
    dependenceConstant := C
    lipschitz := fun t ht => (lipschitz t (Ioo_subset_Icc_self
      (temporal t (Ioo_subset_Icc_self ht)))).mono initialSubset }⟩

theorem UniformDevelopment.joint_zero {base : State} (family : UniformDevelopment base)
    (initial : State) (inside : initial ∈ closedBall base family.initialRadius)
    (point : BasePoint) (timeInside : point 0 ∈ Ioo (-family.timeRadius) family.timeRadius) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      (family.solution initial inside).configuration point = 0 :=
  (family.solution initial inside).joint_zero point timeInside

theorem UniformDevelopment.norm_control {base : State} (family : UniformDevelopment base)
    (first second : State) (firstInside : first ∈ closedBall base family.initialRadius)
    (secondInside : second ∈ closedBall base family.initialRadius)
    (time : ℝ) (inside : time ∈ Ioo (-family.timeRadius) family.timeRadius) :
    ‖family.curve first time-family.curve second time‖ ≤
      family.dependenceConstant*‖first-second‖ := by
  simpa only [dist_eq_norm] using
    (family.lipschitz time inside).dist_le_mul first firstInside second secondInside

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
