import H0mework.Physics.LowEnergyEvolution.MatterCoframe
import H0mework.Physics.LowEnergyEvolution.Coframe
import H0mework.Physics.LowEnergyEvolution.GaugeStress
import H0mework.Physics.LowEnergyEvolution.GaugeEquation
import H0mework.Physics.LowEnergyEvolution.Adjoint
import H0mework.Physics.LowEnergyEvolution.Constraints

/-! All nine original variational channels vanish on one generated open
time strip. The primitive coframe and every auxiliary stay the same fields. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeCoframeLocalVariation
open Stage9C.Material.SpinPair
open scoped Topology
noncomputable section

theorem Solution.coframe_euler_coordinates {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (row col : LorentzianIndex) :
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField flow.configuration point) (Matrix.single row col 1) = 0 := by
  rw [diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
    positiveSmoothUnifiedSource point (toContinuumPointField flow.configuration point)
      (flow.nondegenerate_at point inside),
    flow.gauge_coframe_coordinates point inside, flow.matter_coframe point inside,
    flow.gravity_reaction_coordinates point inside]
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  by_cases diagonal : row = col
  · subst col
    fin_cases row <;> simp [scalarCoframeForce, diracCoframeForce]
    · have balance := temporal_zero (flow.pointState point) admissible
      unfold temporalResidual denominator at balance
      convert balance using 1
      ring
    all_goals
      convert spatial_zero (flow.pointState point) admissible using 1
      ring
  · fin_cases row <;> fin_cases col <;> simp_all [scalarCoframeForce, diracCoframeForce]

theorem Solution.coframe_euler_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField flow.configuration point) = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  change diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
    (toContinuumPointField flow.configuration point) variation = 0
  rw [Matrix.matrix_eq_sum_single variation, map_sum]
  apply Finset.sum_eq_zero
  intro row _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro col _
  rw [show Matrix.single row col (variation row col) =
      variation row col • Matrix.single row col (1 : ℝ) by simp [Matrix.smul_single],
    map_smul, flow.coframe_euler_coordinates point inside row col, smul_zero]

theorem Solution.joint_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource flow.configuration point = 0 := by
  obtain ⟨multiplier, gravityAuxiliary, gaugeAuxiliary, lorentz⟩ := flow.four_constraints point inside
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext _ _ multiplier gravityAuxiliary gaugeAuxiliary lorentz
  · exact flow.gauge_euler_zero point inside
  · funext test
    exact flow.scalar_euler_zero point inside test
  · funext test
    exact flow.adjoint_euler_zero point inside test
  · funext test
    exact flow.primal_euler_zero point inside test
  · exact flow.coframe_euler_zero point inside

theorem source_joint_zero (parameter : ℝ) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-(solution parameter).radius) (solution parameter).radius) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      (solution parameter).configuration point = 0 :=
  (solution parameter).joint_zero point inside

theorem source_local_development (parameter : ℝ) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ point : BasePoint, point 0 ∈ Set.Ioo (-radius) radius →
        diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
          (solution parameter).configuration point = 0 :=
  ⟨(solution parameter).radius, (solution parameter).positive, source_joint_zero parameter⟩

theorem source_initial_development (initial : State) (admissible : Admissible initial) :
    ∃ radius : ℝ, 0 < radius ∧
      (initialSolution initial admissible).curve 0 = initial ∧
      HasDerivAt (initialSolution initial admissible).curve (generator initial) 0 ∧
      ∀ point : BasePoint, point 0 ∈ Set.Ioo (-radius) radius →
        diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
          (initialSolution initial admissible).configuration point = 0 :=
  ⟨(initialSolution initial admissible).radius, (initialSolution initial admissible).positive,
    initialSolution_initial initial admissible, (initialSolution initial admissible).initial_evolution,
    (initialSolution initial admissible).joint_zero⟩

theorem source_directional_development (initial : State) (admissible : Admissible initial)
    (variation : State) :
    ∃ amplitudeRadius : ℝ, 0 < amplitudeRadius ∧
      ∀ amplitude : ℝ, |amplitude| < amplitudeRadius →
        ∃ flow : Solution (initial + amplitude • variation),
          ∀ point : BasePoint, point 0 ∈ Set.Ioo (-flow.radius) flow.radius →
            diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
              flow.configuration point = 0 := by
  have near : {t : ℝ | Admissible (initial+t • variation)} ∈ 𝓝 (0 : ℝ) := by
    have continuous : ContinuousAt (fun t : ℝ => initial+t • variation) 0 := by fun_prop
    change (fun t : ℝ => initial+t • variation) ⁻¹' {x : State | Admissible x} ∈ 𝓝 (0 : ℝ)
    apply continuous.preimage_mem_nhds
    apply admissible_isOpen.mem_nhds
    simpa only [Set.mem_ofPred_eq, zero_smul, add_zero] using admissible
  obtain ⟨radius, positive, ball⟩ := Metric.mem_nhds_iff.mp near
  refine ⟨radius, positive, ?_⟩
  intro amplitude bound
  have allowed : Admissible (initial+amplitude • variation) := by
    apply ball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using bound
  exact ⟨initialSolution (initial+amplitude • variation) allowed,
    (initialSolution (initial+amplitude • variation) allowed).joint_zero⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
