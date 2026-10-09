import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.Calculus
import H0mework.Versions.AB.Chemistry.LAlanineBandGlobalSource.Integrability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open BasinRefinement SourceGaussianModel SourceFiniteData GlobalSource
open MeasureTheory
noncomputable section

def linePoint (d : Point) (t : ℝ) (x : Point) : Point := fun k => x k - t * d k

def lineRate (terms : List Term) (jet : MultiIndex) (d : Point) (t : ℝ) (x : Point) : ℝ :=
  -(∑ k : Fin 3, d k * orbital terms (raise jet k) (linePoint d t x))

theorem centred_line (term : Term) (jet : MultiIndex) (d : Point) (t : ℝ) (x : Point) :
    centredValue term jet (fun k => (term.centre k : ℝ) + t * d k) x = value term jet (linePoint d t x) := by
  unfold centredValue
  congr 1
  funext k
  dsimp only [linePoint]
  ring

theorem value_line_derivative (term : Term) (jet : MultiIndex) (d : Point) (t : ℝ) (x : Point) :
    HasDerivAt (fun time => value term jet (linePoint d time x))
      (-(∑ k : Fin 3, d k * value term (raise jet k) (linePoint d t x))) t := by
  have motion (k : Fin 3) : HasDerivAt (fun time => (term.centre k : ℝ) + time * d k) (d k) t := by
    simpa only [mul_one,one_mul] using! ((hasDerivAt_id t).mul_const (d k)).const_add (term.centre k : ℝ)
  simpa only [centred_line] using!
    centred_value_derivative term jet (fun time k => (term.centre k : ℝ) + time * d k) d t x motion

theorem orbital_line_derivative (terms : List Term) (jet : MultiIndex) (d : Point) (t : ℝ) (x : Point) :
    HasDerivAt (fun time => orbital terms jet (linePoint d time x)) (lineRate terms jet d t x) t := by
  induction terms with
  | nil => simpa only [orbital,lineRate,List.map_nil,List.sum_nil,mul_zero,Finset.sum_const_zero,neg_zero] using hasDerivAt_const t (0 : ℝ)
  | cons term rest prior =>
      have total := (value_line_derivative term jet d t x).add prior
      convert! total using 1
      simp only [lineRate,orbital,List.map_cons,List.sum_cons,mul_add,Finset.sum_add_distrib]
      ring

theorem line_rate_continuous (terms : List Term) (jet : MultiIndex) (d x : Point) :
    Continuous (fun t => lineRate terms jet d t x) := by
  unfold lineRate
  apply Continuous.neg
  apply continuous_finsetSum
  intro k _
  exact ((orbital_contDiff terms (raise jet k) 0).continuous.comp (by unfold linePoint; fun_prop)).const_mul (d k)

theorem orbital_line_integral (terms : List Term) (jet : MultiIndex) (d x : Point) :
    orbital terms jet (x - d) - orbital terms jet x = ∫ t in (0 : ℝ)..1, lineRate terms jet d t x := by
  have integral := (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => orbital_line_derivative terms jet d t x)
    ((line_rate_continuous terms jet d x).intervalIntegrable (0 : ℝ) 1)).symm
  have finish : linePoint d 1 x = x - d := by funext k; simp only [linePoint,one_mul,Pi.sub_apply]
  have start : linePoint d 0 x = x := by funext k; simp only [linePoint,zero_mul,sub_zero]
  rw [finish,start] at integral
  exact integral

/-- Variance positivity on the unit interval gives scalar Cauchy without an Lp coercion. -/
theorem integral_square_le (f : ℝ → ℝ) (regular : Continuous f) :
    (∫ t in (0 : ℝ)..1, f t)^2 ≤ ∫ t in (0 : ℝ)..1, (f t)^2 := by
  let mean := ∫ t in (0 : ℝ)..1, f t
  have nonnegative : 0 ≤ ∫ t in (0 : ℝ)..1, (f t - mean)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg _)
  have expansion : (∫ t in (0 : ℝ)..1, (f t - mean)^2) =
      (∫ t in (0 : ℝ)..1, (f t)^2) - mean^2 := by
    simp_rw [sub_sq]
    have sqInt : IntervalIntegrable (fun t => (f t)^2) volume 0 1 := (regular.pow 2).intervalIntegrable _ _
    have prodInt : IntervalIntegrable (fun t => 2 * f t * mean) volume 0 1 :=
      ((regular.const_mul 2).mul_const mean).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (sqInt.sub prodInt) intervalIntegrable_const,
      intervalIntegral.integral_sub sqInt prodInt]
    simp only [intervalIntegral.integral_const,sub_zero,one_smul]
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul]
    dsimp only [mean]
    ring
  rw [expansion] at nonnegative
  dsimp only [mean] at nonnegative
  linarith only [nonnegative]

theorem orbital_line_square_le (terms : List Term) (jet : MultiIndex) (d x : Point) :
    (orbital terms jet (x - d) - orbital terms jet x)^2 ≤
      ∫ t in (0 : ℝ)..1, (lineRate terms jet d t x)^2 := by
  rw [orbital_line_integral]
  exact integral_square_le _ (line_rate_continuous terms jet d x)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
