import H0mework.Physics.ConductanceCell.Trajectory
import H0mework.NavierStokes.Galerkin.CriticalGronwall

/-!
# Generated rail invariance under time-varying gate inputs

The imported comparison theorem is scalar and substrate-neutral despite its
historical NS path. The actual cell trajectory supplies its derivative; no
solution or target rail certificate enters the trajectory compiler.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface Set
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall

noncomputable section

private theorem evolving_le_zero {f f' rate : ℝ → ℝ} {first last : ℝ}
    (ordered : first ≤ last) (ode : ∀ t ∈ Icc first last, HasDerivAt f (f' t) t)
    (rateContinuous : Continuous rate)
    (bound : ∀ t ∈ Icc first last, f' t ≤ -rate t * f t)
    (initial : f first ≤ 0) : f last ≤ 0 := by
  have compare := le_initial_mul_exp_integral_of_hasDerivAt_le_mul ode
    rateContinuous.neg.continuousOn bound last ⟨ordered, le_rfl⟩
  exact compare.trans (mul_nonpos_of_nonpos_of_nonneg initial (Real.exp_pos _).le)

namespace LoadedConductanceCellSource

theorem drivenForcing_nonneg (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (time : ℝ) : 0 ≤ source.drivenForcing left right time :=
  (div_pos (mul_pos (source.pullUp_pos (left time) (right time)) source.supply_pos)
    source.capacitance_pos).le

theorem drivenForcing_eq_rate_mul_equilibrium (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (time : ℝ) :
    source.drivenForcing left right time =
      source.drivenRate left right time * (source.equilibrium (left time) (right time)).value := by
  have totalNonzero := ne_of_gt (add_pos
    (source.pullUp_pos (left time) (right time)) (source.pullDown_pos (left time) (right time)))
  have capNonzero := ne_of_gt source.capacitance_pos
  unfold drivenForcing drivenRate rate equilibrium
  dsimp only
  field_simp

theorem drivenForcing_le_rate_mul_supply (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (time : ℝ) :
    source.drivenForcing left right time ≤ source.drivenRate left right time * source.supply.value := by
  rw [source.drivenForcing_eq_rate_mul_equilibrium]
  exact mul_le_mul_of_nonneg_left (source.equilibrium_mem_rail (left time) (right time)).2
    (source.rate_pos (left time) (right time)).le

theorem drivenVoltageAt_mem_rail (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (initialRail : InRail source initial) (time : ℝ) (nonnegative : 0 ≤ time) :
    InRail source ⟨source.drivenVoltageAt left right initial time⟩ := by
  have ode := source.drivenVoltageAt_hasDerivAt left right initial leftContinuous rightContinuous
  have coefficient := source.drivenRate_continuous left right leftContinuous rightContinuous
  constructor
  · have low := evolving_le_zero (f := fun t => -source.drivenVoltageAt left right initial t)
      (f' := fun t => -(source.drivenForcing left right t - source.drivenRate left right t *
        source.drivenVoltageAt left right initial t)) nonnegative
      (fun t _ => (ode t).neg) coefficient
      (fun t _ => by have forcing := source.drivenForcing_nonneg left right t; nlinarith)
      (by rw [source.drivenVoltageAt_initial]; exact neg_nonpos.mpr initialRail.1)
    exact neg_nonpos.mp low
  · have high := evolving_le_zero (f := fun t => source.drivenVoltageAt left right initial t - source.supply.value)
      (f' := fun t => source.drivenForcing left right t - source.drivenRate left right t *
        source.drivenVoltageAt left right initial t) nonnegative
      (fun t _ => (ode t).sub_const source.supply.value) coefficient
      (fun t _ => by have forcing := source.drivenForcing_le_rate_mul_supply left right t; nlinarith)
      (by rw [source.drivenVoltageAt_initial]; exact sub_nonpos.mpr initialRail.2)
    exact sub_nonpos.mp high

end LoadedConductanceCellSource
end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
