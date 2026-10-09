import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Polynomial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Axis

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open MeasureTheory
noncomputable section

theorem pair_moment_one_zero (d e rate : ℝ) :
    High.pairMomentClosed 1 0 d e rate =
      d*Real.sqrt (Real.pi/rate) := by
  simp [High.pairMomentClosed, High.coeff,
    Finset.sum_range_succ, High.rawMoment]

theorem target_first_inner (q B E t x : ℝ)
    (hq : 0 < q) (ht : 0 < t) :
    (∫ y : ℝ,
      (y-E)*Real.exp (-q*(y-B)^2) * Real.exp (-(t^2)*(y-x)^2)) =
      Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) *
        (centre q (t^2) B x-E) * Real.sqrt (Real.pi/(q+t^2)) := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hqt : 0 < q+t^2 := add_pos hq ht2
  let Q : ℝ := centre q (t^2) B x
  have hpoint (y : ℝ) :
      (y-E)*Real.exp (-q*(y-B)^2) * Real.exp (-(t^2)*(y-x)^2) =
        Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) *
          ((y-E)*Real.exp (-(q+t^2)*(y-Q)^2)) := by
    have hexp := exponential_product q (t^2) B x y (ne_of_gt hqt)
    calc
      _ = (y-E)*(Real.exp (-q*(y-B)^2) *
            Real.exp (-(t^2)*(y-x)^2)) := by ring
      _ = (y-E)*(Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) *
            Real.exp (-(q+t^2)*(y-Q)^2)) := by
          dsimp [Q]
          rw [hexp]
      _ = _ := by ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hshift := High.shifted_pair_gaussian_integral
    1 0 E Q Q (q+t^2) (by omega) (by omega) hqt
  simp only [pow_one,pow_zero,mul_one] at hshift
  rw [hshift, pair_moment_one_zero]
  dsimp [Q]
  ring

def targetFirstAxisIntegrand (a b : ℕ) (p q A B C D E t : ℝ)
    (z : ℝ × ℝ) : ℝ :=
  (z.1-C)^a * (z.1-D)^b * (z.2-E) *
    Axis.coupledAxis p q A B t z.1 z.2

def targetFirstAxisClosed (a b : ℕ) (p q A B C D E t : ℝ) : ℝ :=
  let r := q*t^2/(q+t^2)
  let P := centre p r A B
  let u := t^2/(q+t^2)
  let v := centre q (t^2) B P-E
  Real.sqrt (Real.pi/(q+t^2)) *
    Real.exp (-(p*r/(p+r)*(A-B)^2)) *
      pairMomentLinear a b (P-C) (P-D) (p+r) u v

theorem target_first_axis_integrable (a b : ℕ)
    (p q A B C D E t : ℝ)
    (ha : a < 3) (hb : b < 3) (hp : 0 < p) (hq : 0 < q) :
    Integrable (targetFirstAxisIntegrand a b p q A B C D E t) := by
  have hx := High.shifted_pair_gaussian_integrable a b C D A p ha hb hp
  have hy := High.shifted_pair_gaussian_integrable
    1 0 E B B q (by omega) (by omega) hq
  simp only [pow_one,pow_zero,mul_one] at hy
  have base := hx.mul_prod hy
  have heatBound (z : ℝ × ℝ) :
      ‖Real.exp (-(t^2)*(z.2-z.1)^2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t))
        (sq_nonneg _))
  have heatMeasurable : Measurable (fun z : ℝ × ℝ =>
      Real.exp (-(t^2)*(z.2-z.1)^2)) := by fun_prop
  have result := base.mul_bdd heatMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall heatBound)
  have hfun : targetFirstAxisIntegrand a b p q A B C D E t =
      (fun z : ℝ × ℝ =>
        ((z.1-C)^a * (z.1-D)^b * Real.exp (-p*(z.1-A)^2)) *
          ((z.2-E)*Real.exp (-q*(z.2-B)^2)) *
          Real.exp (-(t^2)*(z.2-z.1)^2)) := by
    funext z
    dsimp [targetFirstAxisIntegrand, Axis.coupledAxis]
    ring
  rw [hfun]
  simpa only [Measure.volume_eq_prod] using result

theorem target_first_axis_integral (a b : ℕ)
    (p q A B C D E t : ℝ)
    (ha : a < 3) (hb : b < 3)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ,
      targetFirstAxisIntegrand a b p q A B C D E t z) =
        targetFirstAxisClosed a b p q A B C D E t := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hqt : 0 < q+t^2 := add_pos hq ht2
  let r : ℝ := q*t^2/(q+t^2)
  have hr : 0 < r := div_pos (mul_pos hq ht2) hqt
  let P : ℝ := centre p r A B
  let u : ℝ := t^2/(q+t^2)
  let v : ℝ := centre q (t^2) B P-E
  have hpq : p+r ≠ 0 := ne_of_gt (add_pos hp hr)
  have hlin (x : ℝ) :
      centre q (t^2) B x-E = u*(x-P)+v := by
    dsimp [u,v]
    unfold centre
    field_simp [ne_of_gt hqt]
    ring
  have hprod := integral_prod
    (targetFirstAxisIntegrand a b p q A B C D E t)
    (target_first_axis_integrable a b p q A B C D E t ha hb hp hq)
  have hiter :
      (∫ z : ℝ × ℝ, targetFirstAxisIntegrand a b p q A B C D E t z) =
        ∫ x : ℝ, ∫ y : ℝ,
          targetFirstAxisIntegrand a b p q A B C D E t (x,y) := by
    simpa only [Measure.volume_eq_prod] using hprod
  rw [hiter]
  have inner (x : ℝ) :
      (∫ y : ℝ, targetFirstAxisIntegrand a b p q A B C D E t (x,y)) =
        ((x-C)^a * (x-D)^b * Real.exp (-p*(x-A)^2)) *
          (Real.exp (-(r*(B-x)^2)) *
            (centre q (t^2) B x-E) *
              Real.sqrt (Real.pi/(q+t^2))) := by
    calc
      _ = ((x-C)^a * (x-D)^b * Real.exp (-p*(x-A)^2)) *
          (∫ y : ℝ,
            (y-E)*Real.exp (-q*(y-B)^2) *
              Real.exp (-(t^2)*(y-x)^2)) := by
        rw [← integral_const_mul]
        congr 1
        funext y
        unfold targetFirstAxisIntegrand Axis.coupledAxis
        ring
      _ = _ := by rw [target_first_inner q B E t x hq ht]
  simp_rw [inner]
  have hpoint (x : ℝ) :
      ((x-C)^a * (x-D)^b * Real.exp (-p*(x-A)^2)) *
        (Real.exp (-(r*(B-x)^2)) *
          (centre q (t^2) B x-E) * Real.sqrt (Real.pi/(q+t^2))) =
        Real.sqrt (Real.pi/(q+t^2)) *
          (Real.exp (-(p*r/(p+r)*(A-B)^2)) *
            ((x-C)^a * (x-D)^b * (u*(x-P)+v) *
              Real.exp (-(p+r)*(x-P)^2))) := by
    have hexp := exponential_product p r A B x hpq
    have hs : (B-x)^2 = (x-B)^2 := by ring
    rw [hs,hlin]
    calc
      _ = Real.sqrt (Real.pi/(q+t^2)) *
            ((x-C)^a * (x-D)^b * (u*(x-P)+v) *
              (Real.exp (-p*(x-A)^2) * Real.exp (-r*(x-B)^2))) := by ring
      _ = Real.sqrt (Real.pi/(q+t^2)) *
            ((x-C)^a * (x-D)^b * (u*(x-P)+v) *
              (Real.exp (-(p*r/(p+r)*(A-B)^2)) *
                Real.exp (-(p+r)*(x-P)^2))) := by
          dsimp [P]
          rw [hexp]
      _ = _ := by ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_const_mul,
    shifted_pair_gaussian_linear_integral a b C D P (p+r) u v
      ha hb (add_pos hp hr)]
  unfold targetFirstAxisClosed
  dsimp [r,P,u,v]
  ring

def targetAxisIntegrand (a b m : ℕ) (p q A B C D E t : ℝ)
    (z : ℝ × ℝ) : ℝ :=
  (z.1-C)^a * (z.1-D)^b * (z.2-E)^m *
    Axis.coupledAxis p q A B t z.1 z.2

def targetAxisClosed (a b m : ℕ) (p q A B C D E t : ℝ) : ℝ :=
  if m = 0 then High.axisPairClosed a b p q A B C D t
  else targetFirstAxisClosed a b p q A B C D E t

theorem target_axis_integral (a b m : ℕ) (p q A B C D E t : ℝ)
    (ha : a < 3) (hb : b < 3) (hm : m < 2)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, targetAxisIntegrand a b m p q A B C D E t z) =
      targetAxisClosed a b m p q A B C D E t := by
  interval_cases m
  · simpa [targetAxisIntegrand,targetAxisClosed,High.axisPairIntegrand] using
      High.axis_pair_integral a b p q A B C D t ha hb hp hq ht
  · simpa [targetAxisIntegrand,targetAxisClosed,targetFirstAxisIntegrand] using
      target_first_axis_integral a b p q A B C D E t ha hb hp hq ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
