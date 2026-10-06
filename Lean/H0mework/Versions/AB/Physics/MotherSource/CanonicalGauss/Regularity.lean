import H0mework.Versions.AB.Physics.MotherSource.CanonicalGauss.Poisson
import H0mework.Versions.R2.Physics.RootRuntime.RecoveryConsumer
import H0mework.Physics.GaugeAction.P286JointYangMillsGradientFlowRegularity

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.CanonicalGauss
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286JointYangMillsGradientFlowRegularity
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open Stage9C.Material.SpinPair
open scoped ContDiff
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

theorem primitive_smooth (potential : BasePoint → ℝ) (smooth : ContDiff ℝ ∞ potential) :
    (TemporalGauge.primitive (abelianPotential potential)).Smooth := by
  rcases Recovery.stageOneThroughTenClosure.final.classical.smooth with
    ⟨coframe, gravity, auxiliary, multiplier, gauge, gaugeAux, scalar, matter, dual⟩
  refine ⟨coframe, gravity, auxiliary, multiplier, ?_, gaugeAux, scalar, matter, dual⟩
  intro direction
  simp only [TemporalGauge.primitive, map_add, abelianPotential]
  by_cases zero : direction = 0
  · simp only [zero, ite_true, map_smul]
    exact (gauge 0).add (smooth.smul_const _)
  · simp only [zero, ite_false, map_zero, add_zero]
    exact gauge direction

theorem primitive_nondegenerate (potential : TemporalGauge.Potential) :
    (TemporalGauge.primitive potential).Nondegenerate := by
  change Runtime.configuration.Nondegenerate
  rw [Runtime.configuration_eq]
  exact actual_nondegenerate

theorem base_smooth (potential : BasePoint → ℝ) (smooth : ContDiff ℝ ∞ potential) :
    (TemporalGauge.configuration (abelianPotential potential)).Smooth :=
  formNativeP286GaugeConstitutiveReadout_smooth Runtime.source _
    (primitive_smooth potential smooth) (primitive_nondegenerate _)

theorem generated_configuration_smooth (potential : BasePoint → ℝ) (smooth : ContDiff ℝ ∞ potential) :
    (configuration (abelianPotential potential)).Smooth := by
  apply normalConstraint_smooth _ (base_smooth potential smooth) _ (noncharacteristic _)
  intro point
  rw [base_coframe, Runtime.configuration_eq]
  exact actual_nondegenerate point

end
end SaturationMonoid.PhysicsCore.Stage10.CanonicalGauss
