import H0mework.Physics.GlobalOrbit.Energy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The mechanical global orbit generates the original Dirac phase by FTC.
No boundedness assumption is imposed on the passive phase coordinate. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
open Stage9C.Material.SpinPair MeasureTheory

noncomputable section

variable {impulse : ℝ}

def MechanicalFlow.phaseRate (flow : MechanicalFlow impulse) (time : ℝ) : ℝ :=
  3*lapse/2*(spinScale-(flow.curve time).1)

theorem MechanicalFlow.phaseRate_continuous (flow : MechanicalFlow impulse) : Continuous flow.phaseRate := by
  have trajectory : Continuous flow.curve := continuous_iff_continuousAt.mpr
    (fun time => (flow.original_evolves time).continuousAt)
  exact continuous_const.mul (continuous_const.sub trajectory.fst)

def MechanicalFlow.phase (flow : MechanicalFlow impulse) (time : ℝ) : ℝ :=
  ∫ candidate in 0..time, flow.phaseRate candidate

theorem MechanicalFlow.phase_derivative (flow : MechanicalFlow impulse) (time : ℝ) :
    HasDerivAt flow.phase (flow.phaseRate time) time :=
  intervalIntegral.integral_hasDerivAt_right (flow.phaseRate_continuous.intervalIntegrable 0 time)
    (flow.phaseRate_continuous.stronglyMeasurableAtFilter volume _) flow.phaseRate_continuous.continuousAt

def MechanicalFlow.completedCurve (flow : MechanicalFlow impulse) (time : ℝ) : PhaseSpace :=
  ((flow.curve time).1, (flow.curve time).2, flow.phase time)

theorem MechanicalFlow.completed_initial (flow : MechanicalFlow impulse) :
    flow.completedCurve 0 = seed impulse := by
  simp [MechanicalFlow.completedCurve, flow.starts, initialMechanical, MechanicalFlow.phase, Nonlinear.seed]

theorem MechanicalFlow.completed_evolves (flow : MechanicalFlow impulse) (time : ℝ) :
    HasDerivAt flow.completedCurve (generator (flow.completedCurve time)) time := by
  have position := flow.position_derivative time
  have momentum := flow.momentum_derivative time
  rw [flow.cutoff_one, one_mul] at position
  rw [flow.cutoff_one, neg_one_mul] at momentum
  have joint := position.prodMk (momentum.prodMk (flow.phase_derivative time))
  rw [generator_eq]
  exact joint

structure CompleteOrbit (impulse : ℝ) where
  curve : ℝ → PhaseSpace
  starts : curve 0 = seed impulse
  evolves : ∀ time, HasDerivAt curve (generator (curve time)) time

theorem completeOrbit_exists (impulse : ℝ) : Nonempty (CompleteOrbit impulse) := by
  obtain ⟨mechanical⟩ := mechanicalFlow_exists impulse
  exact ⟨⟨mechanical.completedCurve, mechanical.completed_initial, mechanical.completed_evolves⟩⟩

def completeOrbit (impulse : ℝ) : CompleteOrbit impulse := Classical.choice (completeOrbit_exists impulse)

def CompleteOrbit.local (trajectory : CompleteOrbit impulse) (radius : ℝ) (positive : 0 < radius) :
    LocalOrbit (seed impulse) 0 where
  radius := radius
  positive := positive
  curve := trajectory.curve
  starts := trajectory.starts
  evolves := fun time _ => trajectory.evolves time

theorem CompleteOrbit.unique (first second : CompleteOrbit impulse) : first.curve = second.curve := by
  funext time
  let radius := |time|+1
  have positive : 0 < radius := by dsimp [radius]; positivity
  have inside : time ∈ (first.local radius positive).window := by
    constructor <;> dsimp [LocalOrbit.window, CompleteOrbit.local, radius] <;>
      linarith [le_abs_self time, neg_abs_le time]
  exact (first.local radius positive).unique_on (second.local radius positive) ⟨inside, inside⟩

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global
