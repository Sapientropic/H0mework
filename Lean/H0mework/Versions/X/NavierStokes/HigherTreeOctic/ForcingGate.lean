import H0mework.Versions.X.NavierStokes.HigherTreeOctic.Dissipation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedTreeTime
noncomputable section
variable {nu : Viscosity}
variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (i j response outside l m p q r s u v : Coordinate) (selected : Fin 7) (a b : Coordinate)

theorem forcingVector_integrable (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    IntervalIntegrable
      (forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed)
      volume first last := by
  have each (entry : Address) : IntervalIntegrable
      (fun time => forcing seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
      volume first last := by
    have paid := NativeUnheatedTreeWindow.forcing_integrable seed
      (slots slot leaf position newest i j outside l m p q r s u v selected b entry)
      first last first0 last0
    exact ⟨paid.1.smul_const _, paid.2.smul_const _⟩
  convert! IntervalIntegrable.sum observed (fun entry _ => each entry) using 1
  funext time
  simp only [forcingVector, Finset.sum_apply]

theorem boundaryCost_integrable (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    IntervalIntegrable (fun time =>
      ‖boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖^2)
      volume first last := by
  have each (entry : Address) : ContinuousOn
      (fun time => product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
        boundaryBasis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
      (uIcc first last) :=
    (NativeUnheatedTreeTime.product_ac seed
      (slots slot leaf position newest i j outside l m p q r s u v selected b entry)
      first last first0 last0).continuousOn.smul continuousOn_const
  have continuous : ContinuousOn
      (fun time => ∑ entry ∈ observed,
        product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
          boundaryBasis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
      (uIcc first last) := continuousOn_finsetSum observed (fun entry _ => each entry)
  have equal :
      (fun time => ∑ entry ∈ observed,
        product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
          boundaryBasis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry) =
      boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed := rfl
  rw [equal] at continuous
  exact (continuous.norm.pow 2).intervalIntegrable

private theorem inner_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (force path : ℝ → E) (first last : ℝ) (ordered : first ≤ last)
    (forceIntegrable : IntervalIntegrable force volume first last)
    (pathContinuous : ContinuousOn path (Icc first last)) :
    IntervalIntegrable (fun time => inner ℝ (path time) (force time)) volume first last := by
  obtain ⟨bound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn pathContinuous
  have forceOn := (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mp forceIntegrable
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mpr
  refine (forceOn.norm.const_mul bound).mono'
    (pathContinuous.aestronglyMeasurable measurableSet_Icc |>.inner forceOn.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with time inside
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    (mul_le_mul_of_nonneg_right (bounded time inside) (norm_nonneg _))

theorem forcingPower_integrable (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) (ordered : first ≤ last) :
    IntervalIntegrable (fun time =>
      2 * inner ℝ
        (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
        (forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time))
      volume first last := by
  have continuous := (vector_ac (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b
    test seed observed first last first0 last0).continuousOn
  rw [uIcc_of_le ordered] at continuous
  exact (inner_integrable
    (forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed)
    (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed)
    first last ordered
    (forcingVector_integrable (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b
      test seed observed first last first0 last0) continuous).const_mul 2

theorem work_separated_write (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) (ordered : first ≤ last) :
    work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last +
      (∫ time in first..last,
        ‖boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖^2) =
    work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first +
      (∫ time in first..last,
        2 * inner ℝ
          (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
          (forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)) := by
  have force := forcingPower_integrable (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b
    test seed observed first last first0 last0 ordered
  have boundary := boundaryCost_integrable (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b
    test seed observed first last first0 last0
  have paid := work_signed_write slot leaf position newest i j response outside l m p q r s u v selected a b
    test seed observed first last first0 last0
  rw [intervalIntegral.integral_sub force boundary] at paid
  linarith

theorem work_forcing_gate (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) (ordered : first ≤ last) :
    work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last ≤
      work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first +
      (∫ time in first..last,
        2 * inner ℝ
          (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
          (forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)) := by
  have balance := work_separated_write slot leaf position newest i j response outside l m p q r s u v selected a b
    test seed observed first last first0 last0 ordered
  have nonnegative : 0 ≤ (∫ time in first..last,
      ‖boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖^2) :=
    intervalIntegral.integral_nonneg ordered (fun _ _ => sq_nonneg _)
  linarith

theorem pairing_forcing_gate (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) (ordered : first ≤ last) :
    ‖original slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last -
      bare slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last‖^2 ≤
      NativeUnifiedCompleteSource.budget seed^2 *
        (work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first +
          ∫ time in first..last,
            2 * inner ℝ
              (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
              (forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)) := by
  have paid := pairing_bound slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last
  exact paid.trans (mul_le_mul_of_nonneg_left
    (work_forcing_gate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first last first0 last0 ordered)
    (sq_nonneg _))

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
