import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Bounds
import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalLinear

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAttractor
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceIntegerGrid
open SourceJetIncidence ContinuousGradient IntervalParameterMap WholeBandGenerated
open WholeBandGenerated.Taylor
open scoped BigOperators
noncomputable section

def evaluatedField (rows : Fin (HighJet.jetCount 0) → Interval) : FieldBox where
  gradient a := HighJet.densityBounds 0 rows (sourceJetIndex (raise zeroJet a))
  hessian a b := HighJet.densityBounds 0 rows (sourceJetIndex (raise (raise zeroJet a) b))

theorem evaluatedField_contains (rows : Fin (HighJet.jetCount 0) → Interval) (x : Point)
    (contains : ∀ j, Holds (grid (rows j))
      (Taylor.sourceJet (HighJet.prefixJet (HighJet.count_le 0) j) x)) :
    FieldHolds (evaluatedField rows) x := by
  have jet (m : MultiIndex) (hm : jetOrder m ≤ 3) :
      Holds (HighJet.densityBounds 0 rows (sourceJetIndex m)) (densityJet m x) := by
    have bound := HighJet.densityBounds_contains 0 rows (sourceJetIndex m) (by
      rw [source_jet_recovered m (by omega)]
      exact hm) x contains
    rwa [Taylor.sourceJet_recovered m (by omega)] at bound
  constructor
  · intro a
    have bound := jet (raise zeroJet a) (by simp only [jetOrder_raise]; norm_num [zeroJet,jetOrder])
    rwa [densityJet_first] at bound
  · intro a b
    have bound := jet (raise (raise zeroJet a) b)
      (by simp only [jetOrder_raise]; norm_num [zeroJet,jetOrder])
    rwa [densityJet_second] at bound

/-- The Pi norm consumes the original three rows of the shifted actual Hessian. -/
theorem shifted_hessian_norm (x : Point) (α k : ℝ) (hk : 0 ≤ k)
    (entries : ∀ i j : Fin 3, |(if i = j then 1 else 0) + α * sourceHessian x i j| ≤ k/3) :
    ‖ContinuousLinearMap.id ℝ Point + α • sourceHessianLinear x‖ ≤ k := by
  apply ContinuousLinearMap.opNorm_le_bound _ hk
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hk (norm_nonneg v))).mpr
  intro i
  have identity : v i = ∑ j : Fin 3, (if i = j then (1 : ℝ) else 0) * v j := by simp
  change |v i + α * (sourceHessianLinear x v) i| ≤ k * ‖v‖
  rw [sourceHessianLinear_apply, identity, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    |∑ j : Fin 3, ((if i = j then 1 else 0) * v j + α * (sourceHessian x i j * v j))| ≤
        ∑ j : Fin 3, |((if i = j then 1 else 0) + α * sourceHessian x i j) * v j| := by
      convert Finset.abs_sum_le_sum_abs
        (fun j : Fin 3 => ((if i = j then (1 : ℝ) else 0) + α * sourceHessian x i j) * v j)
        Finset.univ using 1 <;> congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ _j : Fin 3, (k/3) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (entries i j) (norm_le_pi_norm v j) (abs_nonneg _) (by positivity)
    _ = k * ‖v‖ := by simp; ring

end
end LAlanine40K2025.BasinRefinement.WholeBandAttractor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
