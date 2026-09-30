import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Step
import Mathlib.Algebra.Order.Floor.Ring

/-! A finite source-sized partition generates the resolvent at every real gauge amplitude. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace ProofFreeRicherAnholonomicSource PerturbedGreen
noncomputable section

def iterate (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (delta : ℝ)
    (small : |delta| * damping⁻¹*‖W‖<1) :
    (n : ℕ) → ResolventAt point energy damping positive W ((n : ℝ)*delta)
  | 0 => by simpa only [Nat.cast_zero,zero_mul] using initial point energy damping positive W
  | n+1 => by
    have next := advance point energy damping positive W symmetric ((n : ℝ)*delta) delta
      (iterate point energy damping positive W symmetric delta small n) small
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using next

def count (damping : ℝ) (W : SpatialOperators) (parameter : ℝ) : ℕ :=
  Nat.ceil (|parameter| * damping⁻¹*‖W‖)+1

theorem count_pos (damping : ℝ) (W : SpatialOperators) (parameter : ℝ) :
    0<(count damping W parameter : ℝ) := by unfold count; positivity

theorem divided_step_small (damping : ℝ) (W : SpatialOperators) (parameter : ℝ) :
    |parameter/(count damping W parameter : ℝ)| * damping⁻¹*‖W‖<1 := by
  have positive := count_pos damping W parameter
  have above : |parameter| * damping⁻¹*‖W‖<(count damping W parameter : ℝ) := by
    have rounded := Nat.le_ceil (|parameter| * damping⁻¹*‖W‖)
    simp only [count,Nat.cast_add,Nat.cast_one]
    linarith
  calc
    _ = (|parameter| * damping⁻¹*‖W‖)/(count damping W parameter : ℝ) := by
      rw [abs_div,abs_of_pos positive]
      ring
    _ < 1 := (div_lt_one positive).mpr above

def complete (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter : ℝ) :
    ResolventAt point energy damping positive W parameter := by
  have generated := iterate point energy damping positive W symmetric
    (parameter/(count damping W parameter : ℝ)) (divided_step_small damping W parameter) (count damping W parameter)
  have endpoint : (count damping W parameter : ℝ)*(parameter/(count damping W parameter : ℝ))=parameter := by
    exact mul_div_cancel₀ parameter (count_pos damping W parameter).ne'
  rw [endpoint] at generated
  exact generated

def gaugeR (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter : ℝ) : SpatialOperators :=
  (complete point energy damping positive W symmetric parameter).value

theorem gaugeR_solves (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter : ℝ) (source : FullMatterL2) :
    Equation point energy damping positive W parameter (gaugeR point energy damping positive W symmetric parameter source) source :=
  (complete point energy damping positive W symmetric parameter).solves source

theorem gaugeR_unique (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter : ℝ) (field source : FullMatterL2)
    (solves : Equation point energy damping positive W parameter field source) :
    field=gaugeR point energy damping positive W symmetric parameter source :=
  equation_unique point energy damping positive W symmetric parameter field _ source solves
    (gaugeR_solves point energy damping positive W symmetric parameter source)

theorem gaugeR_norm (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter : ℝ) :
    ‖gaugeR point energy damping positive W symmetric parameter‖≤damping⁻¹ :=
  (complete point energy damping positive W symmetric parameter).norm point energy damping positive W symmetric parameter

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
