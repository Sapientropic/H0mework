import H0mework.Versions.AB.Physics.LowEnergyEvolution.Flow

/-! Direct consumers of the generated flow: the temporal constraint and
the densitized scalar momentum equation are identities of that same curve. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open Stage9C.Material.SpinPair Contact
noncomputable section

def temporalResidual (x : State) : ℝ :=
  3 * x 0 * gaugeEnergy x / (4 * sourceCoupling * (clock x)^2) - denominator x

theorem temporal_zero (x : State) (h : Admissible x) : temporalResidual x = 0 := by
  unfold temporalResidual
  rw [clock_squared x h]
  field_simp [sourceCoupling_eq, ne_of_gt h.1, ne_of_gt h.2.1, ne_of_gt h.2.2]
  ring

theorem spatial_zero (x : State) (h : Admissible x) :
    -gaugeEnergy x / (4 * sourceCoupling * clock x) +
      clock x * (2 * spinScale * (contorsion x - x 2) / (x 0)^2 -
        Stress.weight * (x 0)^2 * ((x 4)^2 + (x 5)^2 / 2) -
        3 * (x 0)^2 - (x 1)^2 + (contorsion x)^2) -
      2 * x 0 * generator x 1 = 0 := by
  change _ - 2 * x 0 * (_ / (2 * x 0)) = 0
  rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) (ne_of_gt h.1)), sub_self]

theorem gauge_zero (x : State) (h : Admissible x) :
    generator x 3 / sourceCoupling + 2 * x 0 * (x 2)^3 / (sourceCoupling * clock x) -
      4 * clock x * spinScale / x 0 = 0 := by
  change (4 * sourceCoupling * clock x * spinScale / x 0 -
    2 * x 0 * (x 2)^3 / clock x) / sourceCoupling + _ - _ = 0
  field_simp [sourceCoupling_eq, ne_of_gt (clock_positive x h), ne_of_gt h.1]
  ring

theorem Solution.coordinate_derivative {initial : State} (flow : Solution initial)
    (time : ℝ) (inside : time ∈ Set.Ioo (-flow.radius) flow.radius) (i : Fin 7) :
    HasDerivAt (fun t => flow.curve t i) (generator (flow.curve time) i) time :=
  hasDerivAt_pi.mp (flow.evolves time inside) i

def scalarMomentum (x : State) : ℝ := -(x 0)^3 * x 5
def scalarAlgebraic (x : State) : ℝ := -2 * clock x * (x 0)^3 * x 4

theorem Solution.scalar_momentum_derivative {initial : State} (flow : Solution initial)
    (time : ℝ) (inside : time ∈ Set.Ioo (-flow.radius) flow.radius) :
    HasDerivAt (fun t => scalarMomentum (flow.curve t)) (scalarAlgebraic (flow.curve time)) time := by
  have derivative := (((flow.coordinate_derivative time inside 0).pow 3).neg).mul
    (flow.coordinate_derivative time inside 5)
  convert! derivative using 1
  change -2 * clock (flow.curve time) * (flow.curve time 0)^3 * flow.curve time 4 =
    -(3 * (flow.curve time 0)^2 * (clock (flow.curve time) * flow.curve time 1)) * flow.curve time 5 +
      -(flow.curve time 0)^3 * (clock (flow.curve time) *
        (2 * flow.curve time 4 - 3 * flow.curve time 1 * flow.curve time 5 / flow.curve time 0))
  field_simp [ne_of_gt (flow.admissible time inside).1]
  ring

def seedVelocity (parameter : ℝ) (index : Fin 7) : ℝ :=
  match index.val with
  | 1 => Slice.scaleAcceleration parameter / Slice.clock parameter
  | 3 => Slice.clock parameter * Slice.gaugeAcceleration parameter
  | 4 => Slice.impulse parameter
  | 6 => Slice.rate parameter
  | _ => 0

theorem generator_seed (parameter : ℝ) : generator (seed parameter) = seedVelocity parameter := by
  have nonzero := ne_of_gt (Slice.clock_positive parameter)
  funext i
  fin_cases i <;> simp [generator, clock_seed, seedVelocity, seed, contorsion, gaugeEnergy]
  · have balance := Slice.spatial_balance parameter
    field_simp [nonzero, sourceCoupling_eq] at balance ⊢
    nlinarith [balance]
  · unfold Slice.gaugeAcceleration
    field_simp [nonzero]
  · field_simp [nonzero]
  · unfold Slice.rate
    ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
