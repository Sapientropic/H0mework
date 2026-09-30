import H0mework.Computation.AIGHold.ClockedLeakyHold
import H0mework.Physics.RLCNetlist.DimensionedRun
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # The holding capacitor and its actual RLC load generate one coupled trajectory -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer
open scoped Matrix Matrix.Norms.Operator

noncomputable section

/-- The load current is present in the holding-capacitor row, not hidden in an ideal driver. -/
def capacitorRLCMatrix (cell : LoadedConductanceCellSource) (hold : ClockedLeakyHoldSource cell)
    (plant : DimensionedSeriesRLCSource) (channel : FiniteEmbodimentChannel) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun plant
  !![-1 / (hold.holdResistance.value * cell.capacitance.value), 0, -1 / cell.capacitance.value;
    0, 0, 1 / (run.capacitanceAt channel).value;
    1 / (run.inductanceAt channel).value, -1 / (run.inductanceAt channel).value,
      -(run.seriesResistanceAt channel).value / (run.inductanceAt channel).value]

def capacitorRLCInitial (holdInitial voltageInitial : SIVolt) (currentInitial : SIAmpere) : Fin 3 → ℝ :=
  ![holdInitial.value, voltageInitial.value, currentInitial.value]

/-- Coordinates are holding voltage, recipient capacitor voltage, and common series current. -/
def capacitorRLCStateAt (cell : LoadedConductanceCellSource) (hold : ClockedLeakyHoldSource cell)
    (plant : DimensionedSeriesRLCSource) (channel : FiniteEmbodimentChannel)
    (holdInitial voltageInitial : SIVolt) (currentInitial : SIAmpere) (time : ℝ) : Fin 3 → ℝ :=
  (NormedSpace.exp (time • capacitorRLCMatrix cell hold plant channel)) *ᵥ
    capacitorRLCInitial holdInitial voltageInitial currentInitial

private theorem matrixExponentialAction_hasDerivAt
    (matrix : Matrix (Fin 3) (Fin 3) ℝ) (initial : Fin 3 → ℝ) (time : ℝ) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • matrix)) *ᵥ initial)
      (matrix *ᵥ ((NormedSpace.exp (time • matrix)) *ᵥ initial)) time := by
  let read : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ) :=
    ((Matrix.mulVecBilin ℝ ℝ).flip initial).toContinuousLinearMap
  have generated := read.hasFDerivAt.comp_hasDerivAt time (hasDerivAt_exp_smul_const' matrix time)
  change HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • matrix)).mulVec initial)
    ((matrix * NormedSpace.exp (time • matrix)).mulVec initial) time at generated
  simpa only [Matrix.mulVec_mulVec] using generated

variable (cell : LoadedConductanceCellSource) (hold : ClockedLeakyHoldSource cell)
  (plant : DimensionedSeriesRLCSource) (channel : FiniteEmbodimentChannel)
  (holdInitial voltageInitial : SIVolt) (currentInitial : SIAmpere)

theorem capacitorRLCStateAt_initial :
    capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial 0 =
      capacitorRLCInitial holdInitial voltageInitial currentInitial := by
  simp only [capacitorRLCStateAt, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]

theorem capacitorRLCStateAt_hasDerivAt (time : ℝ) :
    HasDerivAt (capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial)
      (capacitorRLCMatrix cell hold plant channel *ᵥ
        capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time) time :=
  matrixExponentialAction_hasDerivAt (capacitorRLCMatrix cell hold plant channel)
    (capacitorRLCInitial holdInitial voltageInitial currentInitial) time

theorem capacitorRLCStateAt_continuous :
    Continuous (capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial) :=
  continuous_iff_continuousAt.mpr fun time =>
    (capacitorRLCStateAt_hasDerivAt cell hold plant channel holdInitial voltageInitial currentInitial time).continuousAt

theorem capacitorRLCStateAt_hold_hasDerivAt (time : ℝ) :
    HasDerivAt (fun t => capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial t 0)
      (-capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 0 /
          (hold.holdResistance.value * cell.capacitance.value) -
        capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 2 /
          cell.capacitance.value) time := by
  have generated := (hasDerivAt_pi.mp
    (capacitorRLCStateAt_hasDerivAt cell hold plant channel holdInitial voltageInitial currentInitial time)) 0
  convert generated using 1 <;> first | rfl | (
    simp [capacitorRLCMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv]
    ; ring)

theorem capacitorRLCStateAt_voltage_hasDerivAt (time : ℝ) :
    HasDerivAt (fun t => capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial t 1)
      (capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 2 /
        ((compileFiniteDimensionedSeriesRLCNetlistRun plant).capacitanceAt channel).value) time := by
  have generated := (hasDerivAt_pi.mp
    (capacitorRLCStateAt_hasDerivAt cell hold plant channel holdInitial voltageInitial currentInitial time)) 1
  convert generated using 1 <;> first | rfl | (
    simp [capacitorRLCMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv, mul_comm])

theorem capacitorRLCStateAt_current_hasDerivAt (time : ℝ) :
    HasDerivAt (fun t => capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial t 2)
      ((capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 0 -
          ((compileFiniteDimensionedSeriesRLCNetlistRun plant).seriesResistanceAt channel).value *
            capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 2 -
          capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 1) /
        ((compileFiniteDimensionedSeriesRLCNetlistRun plant).inductanceAt channel).value) time := by
  have generated := (hasDerivAt_pi.mp
    (capacitorRLCStateAt_hasDerivAt cell hold plant channel holdInitial voltageInitial currentInitial time)) 2
  convert generated using 1 <;> first | rfl | (
    simp [capacitorRLCMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv]
    ; ring)

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
