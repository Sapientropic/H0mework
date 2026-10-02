import H0mework.Versions.R2.Physics.SpinPair.Actual
import H0mework.Physics.SpinPair.ColorInvariant

/-! The occupied quantum coordinates are extracted from the accepted physical
matter field. Normalization is a preparation readout; the full actual and its
independent linear dual remain available at their original source. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Source

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair

noncomputable section

abbrev Index := DiracSpinorIndex × Fin 2

/-- All four Dirac components and both source-generated color directions. -/
def amplitude (point : BasePoint) (index : Index) : ℂ :=
  spinPairCoefficients (upperPhase point) (lowerPhase point) index.1 index.2

/-- The occupied norm is two; its scale is retained by `amplitude`. -/
def vector (point : BasePoint) (index : Index) : ℂ := amplitude point index / 2

theorem amplitude_from_actual (point : BasePoint) (index : Index) :
    sourceColorDoubletDual index.2 (actual.matter point index.1) = amplitude point index :=
  sourceColorDoubletDual_diracMatter _ _ _

theorem amplitude_reconstruction (point : BasePoint) :
    sourceColorDiracMatter (fun spin color => amplitude point (spin, color)) =
      actual.matter point := rfl

theorem amplitude_eq_twice_vector (point : BasePoint) (index : Index) :
    amplitude point index = 2 * vector point index := by
  unfold vector
  ring

theorem phase_star (rate : ℝ) (point : BasePoint) :
    star (phase rate point) = phase (-rate) point := by
  change starRingEnd ℂ (Complex.exp _) = _
  rw [← Complex.exp_conj]
  simp [phase, map_mul]

theorem phase_star_mul (rate : ℝ) (point : BasePoint) :
    star (phase rate point) * phase rate point = 1 := by
  rw [phase_star, mul_comm]
  exact phase_opposite rate point

theorem phase_normSq (rate : ℝ) (point : BasePoint) :
    Complex.normSq (phase rate point) = 1 := by
  have value := congrArg Complex.re (phase_star_mul rate point)
  simpa [Complex.normSq_apply, Complex.mul_re] using value

theorem vector_inner_self (point : BasePoint) :
    (∑ index : Index, star (vector point index) * vector point index) = 1 := by
  simp only [Fintype.sum_prod_type]
  simp [amplitude, vector, spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two,
    star_div₀]
  have upper := phase_star_mul frequency point
  have lower := phase_star_mul (-frequency) point
  change (starRingEnd ℂ) (phase frequency point) * phase frequency point = 1 at upper
  change (starRingEnd ℂ) (phase (-frequency) point) * phase (-frequency) point = 1 at lower
  dsimp only [upperPhase, lowerPhase] at *
  linear_combination upper / 2 + lower / 2

theorem vector_normSq (point : BasePoint) :
    (∑ index : Index, Complex.normSq (vector point index)) = 1 := by
  have value := congrArg Complex.re (vector_inner_self point)
  simpa [map_sum, Complex.normSq_apply, Complex.mul_re] using value

theorem vector_nonzero (point : BasePoint) : vector point ≠ 0 := by
  intro zero
  have norm := vector_normSq point
  rw [zero] at norm
  simp at norm

theorem vector_zero (index : Index) :
    vector 0 index = spinPairCoefficients 1 1 index.1 index.2 / 2 := by
  simp [vector, amplitude, upperPhase, lowerPhase, phase_zero]

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Source
