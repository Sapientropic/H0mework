import H0mework.Physics.ConductanceCell.Dynamics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp

/-!
# Actual nonautonomous trajectory of a driven conductance cell

Both time-varying coefficients come from the fixed local conductance laws and
the two input voltage trajectories. The integrating factor constructs the
output voltage; input continuity generates its derivative and KCL equation.
Neither a coefficient family, output trajectory, nor output band is supplied
as source data. Constant-input operation is not substituted for a moving input.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface
open MeasureTheory

noncomputable section
namespace LoadedConductanceCellSource

def drivenRate (source : LoadedConductanceCellSource) (left right : ℝ → SIVolt) (time : ℝ) : ℝ :=
  source.rate (left time) (right time)

def drivenForcing (source : LoadedConductanceCellSource) (left right : ℝ → SIVolt) (time : ℝ) : ℝ :=
  source.pullUp (left time) (right time) * source.supply.value / source.capacitance.value

def accumulatedRate (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (time : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..time, source.drivenRate left right s

/-- Source-generated integrating-factor trajectory of the actual time-varying cell. -/
def drivenVoltageAt (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ) : ℝ :=
  Real.exp (-source.accumulatedRate left right time) *
    (initial.value + ∫ s in (0 : ℝ)..time,
      Real.exp (source.accumulatedRate left right s) * source.drivenForcing left right s)

theorem drivenCoefficients_continuous (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) :
    Continuous (source.drivenRate left right) ∧ Continuous (source.drivenForcing left right) := by
  have nl : Continuous (fun t => source.nConductance (left t)) := by
    unfold nConductance normalizedGate quarticNFactor
    fun_prop
  have nr : Continuous (fun t => source.nConductance (right t)) := by
    unfold nConductance normalizedGate quarticNFactor
    fun_prop
  have pl : Continuous (fun t => source.pConductance (left t)) := by
    unfold pConductance normalizedGate quarticPFactor
    fun_prop
  have pr : Continuous (fun t => source.pConductance (right t)) := by
    unfold pConductance normalizedGate quarticPFactor
    fun_prop
  have up : Continuous (fun t => source.pullUp (left t) (right t)) := pl.add pr
  have down : Continuous (fun t => source.pullDown (left t) (right t)) :=
    (nl.mul nr).div (nl.add nr) (fun t =>
      ne_of_gt (add_pos (source.nConductance_pos (left t)) (source.nConductance_pos (right t))))
  exact ⟨(up.add down).div_const _, (up.mul continuous_const).div_const _⟩

theorem drivenRate_continuous (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) :
    Continuous (source.drivenRate left right) :=
  (source.drivenCoefficients_continuous left right leftContinuous rightContinuous).1

theorem drivenForcing_continuous (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) :
    Continuous (source.drivenForcing left right) :=
  (source.drivenCoefficients_continuous left right leftContinuous rightContinuous).2

theorem drivenVoltageAt_initial (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) :
    source.drivenVoltageAt left right initial 0 = initial.value := by
  simp [drivenVoltageAt, accumulatedRate]

/-- FTC generates the derivative from the source coefficients, not an assumed ODE solution. -/
theorem drivenVoltageAt_hasDerivAt (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) (time : ℝ) :
    HasDerivAt (source.drivenVoltageAt left right initial)
      (source.drivenForcing left right time - source.drivenRate left right time *
        source.drivenVoltageAt left right initial time) time := by
  obtain ⟨rateContinuous, forcingContinuous⟩ :=
    source.drivenCoefficients_continuous left right leftContinuous rightContinuous
  let A := source.accumulatedRate left right
  have derivative : ∀ t, HasDerivAt A (source.drivenRate left right t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (rateContinuous.intervalIntegrable _ _)
      rateContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter rateContinuous.continuousAt
  have primitiveContinuous : Continuous A :=
    (intervalIntegral.differentiable_integral_of_continuous rateContinuous).continuous
  have integrandContinuous : Continuous (fun t => Real.exp (A t) * source.drivenForcing left right t) :=
    (Real.continuous_exp.comp primitiveContinuous).mul forcingContinuous
  have integralDerivative := intervalIntegral.integral_hasDerivAt_right
    (integrandContinuous.intervalIntegrable 0 time)
    integrandContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter integrandContinuous.continuousAt
  have generated := ((derivative time).neg.exp).mul
    ((hasDerivAt_const time initial.value).add integralDerivative)
  convert generated using 1 <;> first | rfl | (
    dsimp only [drivenVoltageAt, A, Pi.neg_apply, Pi.add_apply]
    simp only [Real.exp_neg]
    field_simp
    ring)

theorem drivenVoltageAt_continuous (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) :
    Continuous (source.drivenVoltageAt left right initial) :=
  continuous_iff_continuousAt.mpr fun time =>
    (source.drivenVoltageAt_hasDerivAt left right initial leftContinuous rightContinuous time).continuousAt

theorem drivenVoltageAt_kcl (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) (time : ℝ) :
    HasDerivAt (source.drivenVoltageAt left right initial)
      ((source.pullUp (left time) (right time) *
          (source.supply.value - source.drivenVoltageAt left right initial time) -
        source.pullDown (left time) (right time) * source.drivenVoltageAt left right initial time) /
          source.capacitance.value) time := by
  convert source.drivenVoltageAt_hasDerivAt left right initial
    leftContinuous rightContinuous time using 1
  dsimp only [drivenForcing, drivenRate, rate]
  ring

end LoadedConductanceCellSource
end

end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
