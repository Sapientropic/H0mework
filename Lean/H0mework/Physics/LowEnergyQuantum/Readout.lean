import H0mework.Physics.LowEnergyQuantum.Preparation
import H0mework.Physics.LowEnergyEvolution.Full

/-! The full native response of the same nonlinear nine-field development.
The independent dual is evaluated before any endpoint restriction. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Quantum
open Evolution ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDiracDualFormNativeJointResidualCarrier
open Stage9C.Material.SpinPair DiracExteriorMatterAction
open scoped Matrix
noncomputable section

theorem moving_prepared {initial : State} (flow : Solution initial) (point : BasePoint) :
    flow.configuration.matter point = preparedSpinor (dilution (flow.pointState point 0)) (flow.pointState point 6) := by
  rw [flow.matter]
  simp [preparedSpinor, phase, spinAmplitude]

theorem moving_prepared_dual {initial : State} (flow : Solution initial) (point : BasePoint) :
    flow.configuration.conjugateMatter point =
      spinPairDual ((spinScale : ℂ)*(dilution (flow.pointState point 0) : ℂ)*phase (flow.pointState point 6))
        ((spinScale : ℂ)*(dilution (flow.pointState point 0) : ℂ)*phase (-(flow.pointState point 6))) := by
  rw [flow.dual]
  simp [phase, spinAmplitude, mul_assoc]

theorem moving_pair {initial : State} (flow : Solution initial) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    coordinatePair (flow.configuration.matter point) (flow.configuration.matter point) =
      ((4/(flow.pointState point 0)^3 : ℝ) : ℂ) := by
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  rw [moving_prepared, prepared_pair, dilution_square _ admissible.1]
  congr 1
  ring

theorem moving_response {initial : State} (flow : Solution initial) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (action : Module.End ℂ DiracExteriorMatterCarrier) :
    flow.configuration.conjugateMatter point (action (flow.configuration.matter point)) =
      ((4*spinScale/(flow.pointState point 0)^3 : ℝ) : ℂ)*normalizedRead (flow.pointState point 6) action := by
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  rw [moving_prepared, moving_prepared_dual, prepared_response,
    dilution_square _ admissible.1]
  congr 1
  push_cast
  ring

theorem moving_composite_response {initial : State} (flow : Solution initial) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (first second : Module.End ℂ DiracExteriorMatterCarrier) :
    flow.configuration.conjugateMatter point (first (second (flow.configuration.matter point))) =
      ((4*spinScale/(flow.pointState point 0)^3 : ℝ) : ℂ) *
        ∑ index, star (coordinates (preparedSpinor (1/2) (flow.pointState point 6)) index) *
          ((operatorMatrix spinExchange*(operatorMatrix first*operatorMatrix second)) *ᵥ
            coordinates (preparedSpinor (1/2) (flow.pointState point 6))) index := by
  have response := moving_response flow point inside (first.comp second)
  simpa only [normalizedRead, matrix_composition, LinearMap.comp_apply] using response

theorem source_joint_and_response (initial : State) (admissible : Admissible initial) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-(initialSolution initial admissible).radius) (initialSolution initial admissible).radius)
    (action : Module.End ℂ DiracExteriorMatterCarrier) :
    let flow := initialSolution initial admissible
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource flow.configuration point = 0 ∧
      flow.configuration.conjugateMatter point (action (flow.configuration.matter point)) =
        ((4*spinScale/(flow.pointState point 0)^3 : ℝ) : ℂ)*normalizedRead (flow.pointState point 6) action :=
  ⟨(initialSolution initial admissible).joint_zero point inside,
    moving_response _ point inside action⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Quantum
