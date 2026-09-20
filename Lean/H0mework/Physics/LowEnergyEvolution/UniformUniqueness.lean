import H0mework.Physics.LowEnergyEvolution.Uniform
import Mathlib.Topology.Connected.Clopen

/-! Local Lipschitz uniqueness identifies the common Picard family with every earlier solution. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open Set Filter Metric
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open Stage9C.Material.SpinPair Response.Radial
open scoped Topology ContDiff
noncomputable section

theorem UniformDevelopment.continuous {base : State} (family : UniformDevelopment base) :
    ContinuousOn (Function.uncurry family.curve)
      (closedBall base family.initialRadius ×ˢ Ioo (-family.timeRadius) family.timeRadius) := by
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ family.dependenceConstant _ family.lipschitz
  exact fun initial inside => HasDerivAt.continuousOn (family.evolves initial inside)

theorem Solution.unique_germ {firstInitial secondInitial : State}
    (first : Solution firstInitial) (second : Solution secondInitial)
    (time : ℝ) (firstInside : time ∈ Ioo (-first.radius) first.radius)
    (secondInside : time ∈ Ioo (-second.radius) second.radius)
    (same : first.curve time = second.curve time) : first.curve =ᶠ[𝓝 time] second.curve := by
  have smooth : ContDiffAt ℝ 1 generator (first.curve time) :=
    (generator_contDiffAt _ (first.admissible time firstInside)).of_le (by simp)
  obtain ⟨K, s, neighborhood, lipschitz⟩ := smooth.exists_lipschitzOnWith
  have firstValues : ∀ᶠ t in 𝓝 time, first.curve t ∈ s :=
    (first.evolves time firstInside).continuousAt neighborhood
  have secondNeighborhood : s ∈ 𝓝 (second.curve time) := by rwa [← same]
  have secondValues : ∀ᶠ t in 𝓝 time, second.curve t ∈ s :=
    (second.evolves time secondInside).continuousAt secondNeighborhood
  have firstTimes : ∀ᶠ t in 𝓝 time, t ∈ Ioo (-first.radius) first.radius :=
    isOpen_Ioo.mem_nhds firstInside
  have secondTimes : ∀ᶠ t in 𝓝 time, t ∈ Ioo (-second.radius) second.radius :=
    isOpen_Ioo.mem_nhds secondInside
  apply ODE_solution_unique_of_eventually (v := fun _ => generator) (s := fun _ => s)
    (Filter.Eventually.of_forall (fun _ => lipschitz)) _ _ same
  · filter_upwards [firstTimes, firstValues] with t ht hs
    exact ⟨first.evolves t ht, hs⟩
  · filter_upwards [secondTimes, secondValues] with t ht hs
    exact ⟨second.evolves t ht, hs⟩

theorem Solution.unique_on_overlap {initial : State} (first second : Solution initial) :
    EqOn first.curve second.curve
      (Ioo (-min first.radius second.radius) (min first.radius second.radius)) := by
  let interval := Ioo (-min first.radius second.radius) (min first.radius second.radius)
  have firstInside (time : interval) : (time : ℝ) ∈ Ioo (-first.radius) first.radius := by
    have le := min_le_left first.radius second.radius
    exact ⟨by linarith [time.property.1], lt_of_lt_of_le time.property.2 le⟩
  have secondInside (time : interval) : (time : ℝ) ∈ Ioo (-second.radius) second.radius := by
    have le := min_le_right first.radius second.radius
    exact ⟨by linarith [time.property.1], lt_of_lt_of_le time.property.2 le⟩
  have firstContinuous : Continuous (fun time : interval => first.curve time) := by
    apply continuous_iff_continuousAt.mpr
    intro time
    exact (first.evolves time (firstInside time)).continuousAt.comp continuous_subtype_val.continuousAt
  have secondContinuous : Continuous (fun time : interval => second.curve time) := by
    apply continuous_iff_continuousAt.mpr
    intro time
    exact (second.evolves time (secondInside time)).continuousAt.comp continuous_subtype_val.continuousAt
  let equalTimes : Set interval := {time | first.curve time = second.curve time}
  have closed : IsClosed equalTimes := isClosed_eq firstContinuous secondContinuous
  have opened : IsOpen equalTimes := by
    apply isOpen_iff_mem_nhds.mpr
    intro time equal
    have germ := first.unique_germ second time (firstInside time) (secondInside time) equal
    have pulled := continuous_subtype_val.continuousAt germ
    exact pulled
  let : PreconnectedSpace interval := Subtype.preconnectedSpace isPreconnected_Ioo
  have positive : 0 < min first.radius second.radius := lt_min first.positive second.positive
  have origin : (0:ℝ) ∈ interval := ⟨neg_neg_of_pos positive, positive⟩
  have inhabited : equalTimes.Nonempty := ⟨⟨0,origin⟩, first.starts.trans second.starts.symm⟩
  have all : equalTimes = univ := (show IsClopen equalTimes from ⟨closed,opened⟩).eq_univ inhabited
  intro time inside
  have belongs : (⟨time,inside⟩ : interval) ∈ equalTimes := by rw [all]; trivial
  exact belongs

theorem UniformDevelopment.agrees_with_initialSolution {base : State} (family : UniformDevelopment base)
    (initial : State) (inside : initial ∈ closedBall base family.initialRadius)
    (admissible : Admissible initial) :
    EqOn (family.curve initial) (initialSolution initial admissible).curve
      (Ioo (-min family.timeRadius (initialSolution initial admissible).radius)
        (min family.timeRadius (initialSolution initial admissible).radius)) :=
  (family.solution initial inside).unique_on_overlap (initialSolution initial admissible)

theorem Solution.primitive_eq_on_overlap {initial : State} (first second : Solution initial)
    (point : BasePoint)
    (inside : point 0 ∈ Ioo (-min first.radius second.radius) (min first.radius second.radius)) :
    first.configuration.coframe point = second.configuration.coframe point ∧
    first.configuration.gaugeConnection point = second.configuration.gaugeConnection point ∧
    first.configuration.scalar point = second.configuration.scalar point ∧
    first.configuration.matter point = second.configuration.matter point ∧
    first.configuration.conjugateMatter point = second.configuration.conjugateMatter point := by
  have state : first.pointState point = second.pointState point := first.unique_on_overlap second inside
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [first.coframe, second.coframe, state]
  · change gaugePotential (first.pointState point 2) = gaugePotential (second.pointState point 2)
    rw [state]
  · change direction+first.pointState point 4 • direction = direction+second.pointState point 4 • direction
    rw [state]
  · rw [first.matter, second.matter, state]
  · rw [first.dual, second.dual, state]

theorem Solution.point_field_eq_on_overlap {initial : State} (first second : Solution initial)
    (point : BasePoint)
    (inside : point 0 ∈ Ioo (-min first.radius second.radius) (min first.radius second.radius)) :
    toContinuumPointField first.configuration point = toContinuumPointField second.configuration point := by
  have state : first.pointState point = second.pointState point := first.unique_on_overlap second inside
  have firstInside : point 0 ∈ Ioo (-first.radius) first.radius := by
    have le := min_le_left first.radius second.radius
    constructor <;> linarith [inside.1, inside.2]
  have secondInside : point 0 ∈ Ioo (-second.radius) second.radius := by
    have le := min_le_right first.radius second.radius
    constructor <;> linarith [inside.1, inside.2]
  have primitives := first.primitive_eq_on_overlap second point inside
  apply StageNineContinuumPointField.ext
  · exact primitives.1
  · change holonomicGravityCurvature first.configuration point = holonomicGravityCurvature second.configuration point
    rw [first.gravity_curvature point firstInside, second.gravity_curvature point secondInside, state]
  · change physicalIIPlusBivector (diagonalCoframe (clock (first.pointState point)) (first.pointState point 0)) =
      physicalIIPlusBivector (diagonalCoframe (clock (second.pointState point)) (second.pointState point 0))
    rw [state]
  · change first.configuration.gravitySimplicityMultiplier point = second.configuration.gravitySimplicityMultiplier point
    rw [first.gravity_reaction point firstInside, second.gravity_reaction point secondInside, state]
  · change holonomicGaugeCurvature first.configuration point = holonomicGaugeCurvature second.configuration point
    rw [first.gauge_curvature point firstInside, second.gauge_curvature point secondInside, state]
  · change first.configuration.gaugeAuxiliary point = second.configuration.gaugeAuxiliary point
    rw [first.gauge_auxiliary point firstInside, second.gauge_auxiliary point secondInside, state]
  · exact primitives.2.2.1
  · funext mu
    change holonomicScalarCovariantDerivative first.configuration point mu =
      holonomicScalarCovariantDerivative second.configuration point mu
    rw [first.scalar_covariant point firstInside, second.scalar_covariant point secondInside, state]
  · exact primitives.2.2.2.1
  · funext mu
    change holonomicMatterCovariantDerivative first.configuration point mu =
      holonomicMatterCovariantDerivative second.configuration point mu
    induction mu using Fin.cases with
    | zero => rw [first.matter_covariant_time point firstInside, second.matter_covariant_time point secondInside, state]
    | succ axis =>
      rw [first.matter_covariant_spatial point firstInside, second.matter_covariant_spatial point secondInside,
        state, primitives.2.2.2.1]
  · exact primitives.2.2.2.2

theorem Solution.point_field_germ {initial : State} (first second : Solution initial)
    (point : BasePoint)
    (inside : point 0 ∈ Ioo (-min first.radius second.radius) (min first.radius second.radius)) :
    (fun p => toContinuumPointField first.configuration p) =ᶠ[𝓝 point]
      fun p => toContinuumPointField second.configuration p := by
  have neighborhood : ∀ᶠ p : BasePoint in 𝓝 point,
      p 0 ∈ Ioo (-min first.radius second.radius) (min first.radius second.radius) :=
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).continuous.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds inside)
  filter_upwards [neighborhood] with p hp
  exact first.point_field_eq_on_overlap second p hp

theorem Solution.configuration_germ {initial : State} (first second : Solution initial)
    (point : BasePoint)
    (inside : point 0 ∈ Ioo (-min first.radius second.radius) (min first.radius second.radius)) :
    ∀ᶠ p in 𝓝 point,
      first.configuration.coframe p = second.configuration.coframe p ∧
      first.configuration.gravityConnection p = second.configuration.gravityConnection p ∧
      first.configuration.gravityAuxiliary p = second.configuration.gravityAuxiliary p ∧
      first.configuration.gravitySimplicityMultiplier p = second.configuration.gravitySimplicityMultiplier p ∧
      first.configuration.gaugeConnection p = second.configuration.gaugeConnection p ∧
      first.configuration.gaugeAuxiliary p = second.configuration.gaugeAuxiliary p ∧
      first.configuration.scalar p = second.configuration.scalar p ∧
      first.configuration.matter p = second.configuration.matter p ∧
      first.configuration.conjugateMatter p = second.configuration.conjugateMatter p := by
  have neighborhood : ∀ᶠ p : BasePoint in 𝓝 point,
      p 0 ∈ Ioo (-min first.radius second.radius) (min first.radius second.radius) :=
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).continuous.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds inside)
  filter_upwards [neighborhood] with p hp
  have state : first.pointState p = second.pointState p := first.unique_on_overlap second hp
  have firstInside : p 0 ∈ Ioo (-first.radius) first.radius := by
    have le := min_le_left first.radius second.radius
    constructor <;> linarith [hp.1, hp.2]
  have secondInside : p 0 ∈ Ioo (-second.radius) second.radius := by
    have le := min_le_right first.radius second.radius
    constructor <;> linarith [hp.1, hp.2]
  have connection : first.configuration.gravityConnection p = second.configuration.gravityConnection p := by
    rw [first.connection_generated p firstInside, second.connection_generated p secondInside, state]
  have fields := first.point_field_eq_on_overlap second p hp
  have primitives := first.primitive_eq_on_overlap second p hp
  exact ⟨primitives.1, connection, congrArg StageNineContinuumPointField.gravityAuxiliary fields,
    congrArg StageNineContinuumPointField.gravitySimplicityMultiplier fields, primitives.2.1,
    congrArg StageNineContinuumPointField.gaugeAuxiliary fields, primitives.2.2.1,
    primitives.2.2.2.1, primitives.2.2.2.2⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
