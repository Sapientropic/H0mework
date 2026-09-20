import H0mework.Physics.LowEnergyContact.Prolongation
import Mathlib.Analysis.ODE.ExistUnique

/-! Coupled homogeneous normal-form evolution with the lapse determined by
the same coframe constraint. The original source fixes every coefficient.
Identification of this normal form with the nine-field residual is separate. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open Stage9C.Material.SpinPair Contact
open scoped ContDiff Topology
noncomputable section

/-- Scale, frame velocity, gauge amplitude, gauge momentum, scalar displacement,
scalar frame velocity and matter phase, in that order. -/
abbrev State := Fin 7 → ℝ

def contorsion (x : State) : ℝ := spinScale / (x 0)^2
def gaugeEnergy (x : State) : ℝ := (x 3)^2 + (x 2)^4
def denominator (x : State) : ℝ :=
  6 * spinScale * (contorsion x - x 2) / x 0 +
    Stress.weight * (x 0)^3 * ((x 4)^2 - (x 5)^2 / 2) +
    3 * (x 0)^3 + 3 * x 0 * (x 1)^2 - 3 * x 0 * (contorsion x)^2
def clock (x : State) : ℝ :=
  Real.sqrt (3 * x 0 * gaugeEnergy x / (4 * sourceCoupling * denominator x))
def Admissible (x : State) : Prop :=
  0 < x 0 ∧ 0 < gaugeEnergy x ∧ 0 < denominator x

theorem clock_positive (x : State) (h : Admissible x) : 0 < clock x := by
  apply Real.sqrt_pos.2
  unfold Admissible at h
  rw [sourceCoupling_eq]
  exact div_pos (mul_pos (mul_pos (by norm_num) h.1) h.2.1)
    (mul_pos (by norm_num) h.2.2)

theorem clock_squared (x : State) (h : Admissible x) :
    (clock x)^2 = 3 * x 0 * gaugeEnergy x / (4 * sourceCoupling * denominator x) := by
  apply Real.sq_sqrt
  have hx := h.1
  have hg := h.2.1
  have hd := h.2.2
  rw [sourceCoupling_eq]
  positivity

def generator (x : State) (index : Fin 7) : ℝ :=
  let n := clock x
  match index.val with
  | 0 => n * x 1
  | 1 =>
    (-gaugeEnergy x / (4 * sourceCoupling * n) +
      n * (2 * spinScale * (contorsion x - x 2) / (x 0)^2 -
        Stress.weight * (x 0)^2 * ((x 4)^2 + (x 5)^2 / 2) -
        3 * (x 0)^2 - (x 1)^2 + (contorsion x)^2)) / (2 * x 0)
  | 2 => x 0 * x 3 / n
  | 3 => 4 * sourceCoupling * n * spinScale / x 0 - 2 * x 0 * (x 2)^3 / n
  | 4 => n * x 5
  | 5 => n * (2 * x 4 - 3 * x 1 * x 5 / x 0)
  | _ => 3 * n * (contorsion x - x 2) / (2 * x 0)

def seed (parameter : ℝ) (index : Fin 7) : ℝ :=
  match index.val with
  | 0 => 1
  | 2 => gaugeScale
  | 5 => Slice.impulse parameter / Slice.clock parameter
  | _ => 0

theorem denominator_seed (parameter : ℝ) :
    denominator (seed parameter) =
      3 * gaugeScale^4 / (4 * sourceCoupling * (Slice.clock parameter)^2) := by
  have balance := Slice.temporal_balance parameter
  norm_num [denominator, seed, contorsion]
  field_simp [ne_of_gt (Slice.clock_positive parameter), sourceCoupling_eq] at balance ⊢
  nlinarith [balance]

theorem seed_admissible (parameter : ℝ) : Admissible (seed parameter) := by
  refine ⟨by norm_num [seed], ?_, ?_⟩
  · simpa [gaugeEnergy, seed] using pow_pos gaugeScale_pos 4
  · rw [denominator_seed, sourceCoupling_eq]
    exact div_pos (mul_pos (by norm_num) (pow_pos gaugeScale_pos 4))
      (mul_pos (by norm_num) (sq_pos_of_pos (Slice.clock_positive parameter)))

theorem clock_seed (parameter : ℝ) : clock (seed parameter) = Slice.clock parameter := by
  unfold clock
  rw [denominator_seed]
  have energy : gaugeEnergy (seed parameter) = gaugeScale^4 := by norm_num [gaugeEnergy, seed]
  rw [show seed parameter 0 = 1 from rfl, energy, mul_one]
  have ratio : 3 * gaugeScale^4 /
      (4 * sourceCoupling * (3 * gaugeScale^4 / (4 * sourceCoupling * (Slice.clock parameter)^2))) =
      (Slice.clock parameter)^2 := by
    field_simp [sourceCoupling_eq, ne_of_gt gaugeScale_pos, ne_of_gt (Slice.clock_positive parameter)]
  rw [ratio, Real.sqrt_sq (le_of_lt (Slice.clock_positive parameter))]

theorem denominator_contDiffAt (x : State) (nonzero : x 0 ≠ 0) :
    ContDiffAt ℝ ∞ denominator x := by
  have coordinate (i : Fin 7) : ContDiffAt ℝ ∞ (fun x : State => x i) x := by fun_prop
  have torsion : ContDiffAt ℝ ∞ contorsion x := by
    unfold contorsion
    exact contDiffAt_const.div ((coordinate 0).pow 2) (pow_ne_zero _ nonzero)
  unfold denominator
  fun_prop (disch := assumption)

theorem admissible_isOpen : IsOpen {x : State | Admissible x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x h
  have scale : ContinuousAt (fun y : State => y 0) x := (continuous_apply (0 : Fin 7)).continuousAt
  have energy : ContinuousAt gaugeEnergy x := by unfold gaugeEnergy; fun_prop
  have denom := (denominator_contDiffAt x (ne_of_gt h.1)).continuousAt
  have hs : ∀ᶠ y in 𝓝 x, 0 < y 0 := scale (lt_mem_nhds h.1)
  have he : ∀ᶠ y in 𝓝 x, 0 < gaugeEnergy y := energy (lt_mem_nhds h.2.1)
  have hd : ∀ᶠ y in 𝓝 x, 0 < denominator y := denom (lt_mem_nhds h.2.2)
  exact hs.and (he.and hd)

theorem clock_contDiffAt (x : State) (h : Admissible x) : ContDiffAt ℝ ∞ clock x := by
  have coordinate (i : Fin 7) : ContDiffAt ℝ ∞ (fun x : State => x i) x := by fun_prop
  have energy : ContDiffAt ℝ ∞ gaugeEnergy x :=
    ((coordinate 3).pow 2).add ((coordinate 2).pow 4)
  have denom := denominator_contDiffAt x (ne_of_gt h.1)
  have quotient : ContDiffAt ℝ ∞
      (fun y : State => 3 * y 0 * gaugeEnergy y / (4 * sourceCoupling * denominator y)) x := by
    apply ((contDiffAt_const.mul (coordinate 0)).mul energy).div (contDiffAt_const.mul denom)
    rw [sourceCoupling_eq]
    exact mul_ne_zero (by norm_num) (ne_of_gt h.2.2)
  have quotient_positive : 0 < 3 * x 0 * gaugeEnergy x / (4 * sourceCoupling * denominator x) := by
    rw [sourceCoupling_eq]
    exact div_pos (mul_pos (mul_pos (by norm_num) h.1) h.2.1) (mul_pos (by norm_num) h.2.2)
  exact quotient.sqrt (ne_of_gt quotient_positive)

theorem generator_contDiffAt (x : State) (h : Admissible x) : ContDiffAt ℝ ∞ generator x := by
  have coordinate (i : Fin 7) : ContDiffAt ℝ ∞ (fun x : State => x i) x := by fun_prop
  have scale_nonzero : x 0 ≠ 0 := ne_of_gt h.1
  have torsion : ContDiffAt ℝ ∞ contorsion x := by
    unfold contorsion
    exact contDiffAt_const.div ((coordinate 0).pow 2) (pow_ne_zero _ scale_nonzero)
  have energy : ContDiffAt ℝ ∞ gaugeEnergy x :=
    ((coordinate 3).pow 2).add ((coordinate 2).pow 4)
  have time := clock_contDiffAt x h
  have time_nonzero := ne_of_gt (clock_positive x h)
  have coupling_positive : 0 < sourceCoupling := by rw [sourceCoupling_eq]; norm_num
  unfold generator
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp only []
  all_goals fun_prop (disch := positivity)

structure LocalOrbit (initial : State) where
  radius : ℝ
  positive : 0 < radius
  curve : ℝ → State
  starts : curve 0 = initial
  evolves : ∀ time ∈ Set.Ioo (-radius) radius,
    HasDerivAt curve (generator (curve time)) time

theorem initialLocalOrbit_exists (initial : State) (admissible : Admissible initial) :
    Nonempty (LocalOrbit initial) := by
  have smooth : ContDiffAt ℝ 1 generator initial :=
    (generator_contDiffAt initial admissible).of_le (by simp)
  obtain ⟨curve, starts, radius, positive, evolves⟩ :=
    smooth.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (0 : ℝ)
  exact ⟨⟨radius, positive, curve, starts, by simpa using evolves⟩⟩

theorem localOrbit_exists (parameter : ℝ) : Nonempty (LocalOrbit (seed parameter)) :=
  initialLocalOrbit_exists (seed parameter) (seed_admissible parameter)

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
