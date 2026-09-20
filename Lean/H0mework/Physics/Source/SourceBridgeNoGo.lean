import H0mework.Physics.Holonomic.AnholonomicSource
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Stage-9 source-bridge typed no-go

Stage 9 asks the current proof-free source phase transport to generate a
continuous complex-unitary dynamics, rather than accepting a Hamiltonian or a
unitary-flow certificate from the caller.  The current source phase carrier is
an `Int`-valued cochain on two finite three-cycles.  This module tests the
minimal exact-determination law required of that producer mouth: sampling a
continuous one-parameter unitary flow on every phase-cochain value must be
faithful.

It is not faithful.  The stationary flow and the nontrivial `2 * pi` winding
flow are both genuine continuous one-parameter groups in `U(1)`.  They agree
on every integer phase value of every current source, but differ at time
`1 / 2`.  Hence a continuous unitary interpolation cannot be selected from
the current phase transport without additional source data or an externally
supplied choice.

The geometric positive regression is retained: the same raw source does
generate a smooth coframe field, and `positiveSource` generates nonzero origin
curvature.  This does not upgrade the existing pointwise identity gluing to a
global principal-bundle/holonomy producer.  Since the phase bridge already
fails even when the geometric obligation is weakened to the existing smooth
coframe and origin-curvature projection, the full Stage-9 S9-0 gate cannot
close on the current source type.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceBridgeNoGo

open ProofFreeRicherAnholonomicSource

noncomputable section

/-- The frozen Stage-9 source mouth is exactly the current proof-free source.
The abbreviation adds no metric, connection, curvature, Hamiltonian, state,
or quantum certificate. -/
abbrev SmoothUnifiedSource := Source

/-- A scalar complex-unitary one-parameter dynamics.  `Circle` is the actual
unitary group of the one-dimensional complex carrier; continuity and the group
law are data of the dynamics, not Boolean receipts. -/
structure ComplexUnitaryOneParameterFlow where
  evolve : ℝ → Circle
  evolve_zero : evolve 0 = 1
  evolve_add : ∀ first second,
    evolve (first + second) = evolve first * evolve second
  continuous_evolve : Continuous evolve

/-- The stationary continuous unitary flow. -/
def stationaryFlow : ComplexUnitaryOneParameterFlow where
  evolve := fun _ => 1
  evolve_zero := rfl
  evolve_add := by simp
  continuous_evolve := continuous_const

/-- The nontrivial continuous unitary flow with one full winding per unit
time. -/
def windingFlow : ComplexUnitaryOneParameterFlow where
  evolve := Real.fourierChar
  evolve_zero := by simp
  evolve_add := by
    intro first second
    exact AddChar.map_add_eq_mul Real.fourierChar first second
  continuous_evolve := Real.continuous_fourierChar

/-- A full winding is invisible at every integer time. -/
theorem fourierChar_intCast_eq_one (integer : Int) :
    Real.fourierChar (integer : ℝ) = 1 := by
  rw [Real.fourierChar_apply']
  rw [show 2 * Real.pi * (integer : ℝ) =
      (integer : ℝ) * (2 * Real.pi) by ring]
  rw [Circle.exp_intCast_mul]
  simp

/-- The only unitary information obtainable from the current phase mouth:
evaluate a candidate continuous flow on every actual integer cochain value. -/
def sourcePhaseSample
    (source : SmoothUnifiedSource)
    (flow : ComplexUnitaryOneParameterFlow) :
    Sum ThreeCycleTime ThreeCycleTime →
      Sum ThreeCycleTime ThreeCycleTime → Circle :=
  fun initial terminal =>
    flow.evolve (source.phaseCochain initial terminal : ℝ)

/-- Positive regression: the two actual continuous unitary flows have exactly
the same readout on every phase edge of every current source. -/
theorem stationary_winding_same_sourcePhaseSample
    (source : SmoothUnifiedSource) :
    sourcePhaseSample source stationaryFlow =
      sourcePhaseSample source windingFlow := by
  funext initial terminal
  change (1 : Circle) =
    Real.fourierChar (source.phaseCochain initial terminal : ℝ)
  exact (fourierChar_intCast_eq_one
    (source.phaseCochain initial terminal)).symm

/-- Negative regression: the two flows are nevertheless distinct continuous
dynamics; the winding flow has phase `pi` at half a unit of time. -/
theorem stationary_winding_distinct : stationaryFlow ≠ windingFlow := by
  intro heq
  have hhalf := congrArg
    (fun flow => flow.evolve (2 : ℝ)⁻¹) heq
  change (1 : Circle) = Real.fourierChar (2 : ℝ)⁻¹ at hhalf
  rw [Real.fourierChar_apply'] at hhalf
  have harg : 2 * Real.pi * (2 : ℝ)⁻¹ = Real.pi := by
    field_simp
  rw [harg] at hhalf
  exact Circle.exp_pi_ne_one hhalf.symm

/-- Minimal anti-hand-fill condition for the current phase mouth: its complete
edge sampling must determine the continuous unitary flow. -/
def SourcePhaseSamplingFaithful (source : SmoothUnifiedSource) : Prop :=
  Function.Injective (sourcePhaseSample source)

/-- Typed phase-bridge no-go: integer-valued source phase transport does not
determine a continuous complex-unitary dynamics. -/
theorem sourcePhaseSampling_not_faithful
    (source : SmoothUnifiedSource) :
    ¬ SourcePhaseSamplingFaithful source := by
  intro hfaithful
  exact stationary_winding_distinct
    (hfaithful (stationary_winding_same_sourcePhaseSample source))

/-- Componentwise smoothness avoids imposing an unnecessary normed-group
instance on the full matrix-valued function space. -/
def CoframeComponentwiseSmooth (source : SmoothUnifiedSource) : Prop :=
  ∀ internal coordinate,
    ContDiff ℝ ⊤
      (fun point => source.coframeAt point internal coordinate)

theorem source_coframeComponentwiseSmooth
    (source : SmoothUnifiedSource) :
    CoframeComponentwiseSmooth source := by
  intro internal coordinate
  unfold Source.coframeAt
  simp only [Matrix.of_apply]
  fun_prop

/-- Geometric positive regression.  The no-go does not erase the real current
source producer: `positiveSource` has a componentwise smooth coframe and
nonzero generated origin curvature. -/
theorem positiveSource_smoothCoframe_nonzeroOriginCurvature :
    CoframeComponentwiseSmooth positiveSource ∧
      positiveSource.coordinateCurvatureAtOrigin 0 1 0 1 =
        -(1 / 4 : ℝ) :=
  ⟨source_coframeComponentwiseSmooth positiveSource,
    positiveSource_curvature_nonzero_component⟩

/-- Deliberately weakened S9-0 gate.  Its geometric fields require only the
already generated smooth coframe and origin geometry, while its phase field is
the minimal faithful continuous-unitary bridge.  Failure of this weaker gate
implies failure of the stronger global bundle/holonomy Stage-9 gate. -/
structure StageNineS9ZeroCurrentSourceGate
    (source : SmoothUnifiedSource) : Prop where
  smoothGeometricProjection : CoframeComponentwiseSmooth source
  originGeometryGenerated :
    (generatedOriginGeometry source).lorentzCurvature =
      source.lorentzCurvatureAtOrigin
  phaseTransportDeterminesUnitaryFlow :
    SourcePhaseSamplingFaithful source

/-- S9-0 diagnostic theorem for the old/current source mouth.  It is retained
as a negative regression after source enrichment; it is not the Stage-9
completion theorem.  No value of the old source type can pass even the
weakened producer gate. -/
theorem currentSource_stageNineS9Zero_typedNoGo
    (source : SmoothUnifiedSource) :
    ¬ StageNineS9ZeroCurrentSourceGate source := by
  intro gate
  exact sourcePhaseSampling_not_faithful source
    gate.phaseTransportDeterminesUnitaryFlow

end

end SaturationMonoid.PhysicsCore.StageNineSourceBridgeNoGo
