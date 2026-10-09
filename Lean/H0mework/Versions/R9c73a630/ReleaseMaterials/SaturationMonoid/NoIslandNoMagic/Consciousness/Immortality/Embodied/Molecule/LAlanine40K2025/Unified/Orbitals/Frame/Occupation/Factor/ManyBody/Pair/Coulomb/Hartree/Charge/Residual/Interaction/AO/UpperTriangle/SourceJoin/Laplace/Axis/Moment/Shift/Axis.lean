import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Axis

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
open MeasureTheory
noncomputable section

def axisShiftIntegrand (power : ℕ) (p q A B C t : ℝ) (z : ℝ × ℝ) : ℝ :=
  (z.1-C)^power * Axis.coupledAxis p q A B t z.1 z.2

def axisShiftClosed (power : ℕ) (p q A B C t : ℝ) : ℝ :=
  if power = 0 then Moment.sAxisClosed p q A B t
  else if power = 1 then
    Moment.firstAxisClosed p q A B t +
      (A-C)*Moment.sAxisClosed p q A B t
  else
    Moment.Second.secondAxisClosed p q A B t +
      2*(A-C)*Moment.firstAxisClosed p q A B t +
      (A-C)^2*Moment.sAxisClosed p q A B t

theorem axis_shift_first (p q A B C t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, axisShiftIntegrand 1 p q A B C t z) =
      axisShiftClosed 1 p q A B C t := by
  have h0 := Axis.coupled_axis_integrable p q A B t hp hq
  have h1 := Moment.coupled_axis_first_integrable p q A B t hp hq
  unfold axisShiftIntegrand axisShiftClosed
  simp only [pow_one, Nat.one_ne_zero, ↓reduceIte]
  calc
    (∫ z : ℝ × ℝ, (z.1-C)*Axis.coupledAxis p q A B t z.1 z.2) =
        ∫ z : ℝ × ℝ,
          (z.1-A)*Axis.coupledAxis p q A B t z.1 z.2 +
          (A-C)*Axis.coupledAxis p q A B t z.1 z.2 := by
      congr 1
      funext z
      ring
    _ = Moment.firstAxisClosed p q A B t +
          (A-C)*Moment.sAxisClosed p q A B t := by
      rw [integral_add h1 (h0.const_mul (A-C)), integral_const_mul,
        Moment.coupled_axis_first_pair p q A B t hp hq ht,
        Axis.coupled_axis_pair_closed p q A B t hp hq ht]
      rfl

theorem axis_shift_second (p q A B C t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, axisShiftIntegrand 2 p q A B C t z) =
      axisShiftClosed 2 p q A B C t := by
  have h0 := Axis.coupled_axis_integrable p q A B t hp hq
  have h1 := Moment.coupled_axis_first_integrable p q A B t hp hq
  have h2 := Moment.Second.coupled_axis_second_integrable p q A B t hp hq
  have h0eval :
      (∫ z : ℝ × ℝ, Axis.coupledAxis p q A B t z.1 z.2) =
        Moment.sAxisClosed p q A B t :=
    Axis.coupled_axis_pair_closed p q A B t hp hq ht
  have h1eval :
      (∫ z : ℝ × ℝ, (z.1-A)*Axis.coupledAxis p q A B t z.1 z.2) =
        Moment.firstAxisClosed p q A B t :=
    Moment.coupled_axis_first_pair p q A B t hp hq ht
  have h2eval :
      (∫ z : ℝ × ℝ, (z.1-A)^2*Axis.coupledAxis p q A B t z.1 z.2) =
        Moment.Second.secondAxisClosed p q A B t :=
    Moment.Second.coupled_axis_second_pair p q A B t hp hq ht
  unfold axisShiftIntegrand axisShiftClosed
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  calc
    (∫ z : ℝ × ℝ, (z.1-C)^2*Axis.coupledAxis p q A B t z.1 z.2) =
        ∫ z : ℝ × ℝ,
          (z.1-A)^2*Axis.coupledAxis p q A B t z.1 z.2 +
          ((2*(A-C))*((z.1-A)*Axis.coupledAxis p q A B t z.1 z.2) +
          (A-C)^2*Axis.coupledAxis p q A B t z.1 z.2) := by
      congr 1
      funext z
      ring
    _ = Moment.Second.secondAxisClosed p q A B t +
          2*(A-C)*Moment.firstAxisClosed p q A B t +
          (A-C)^2*Moment.sAxisClosed p q A B t := by
      calc
        _ = (∫ z : ℝ × ℝ,
              (z.1-A)^2*Axis.coupledAxis p q A B t z.1 z.2) +
            (∫ z : ℝ × ℝ,
              (2*(A-C))*((z.1-A)*Axis.coupledAxis p q A B t z.1 z.2) +
              (A-C)^2*Axis.coupledAxis p q A B t z.1 z.2) := by
            exact integral_add h2
              ((h1.const_mul (2*(A-C))).add (h0.const_mul ((A-C)^2)))
        _ = _ := by
          rw [integral_add (h1.const_mul (2*(A-C)))
              (h0.const_mul ((A-C)^2)), integral_const_mul, integral_const_mul,
            h2eval, h1eval, h0eval]
          ring

theorem axis_shift_integral (power : ℕ) (p q A B C t : ℝ)
    (hpower : power < 3) (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, axisShiftIntegrand power p q A B C t z) =
      axisShiftClosed power p q A B C t := by
  interval_cases power
  · simp only [axisShiftIntegrand, axisShiftClosed, pow_zero, one_mul]
    exact Axis.coupled_axis_pair_closed p q A B t hp hq ht
  · exact axis_shift_first p q A B C t hp hq ht
  · exact axis_shift_second p q A B C t hp hq ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
