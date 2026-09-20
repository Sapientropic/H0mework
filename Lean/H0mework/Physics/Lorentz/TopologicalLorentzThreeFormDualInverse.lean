import H0mework.Physics.Lorentz.TopologicalLorentzThreeFormDuality

/-!
# Explicit inverse of the topological Lorentz three-form dual

Every continuous real linear functional on the finite lowered Lorentz
bivector one-form carrier has a unique contravariant three-form representative
under W13.  The inverse below is fixed by the existing coordinate basis,
missing-triple map, and orientation signs; it introduces no normalization or
branch choice.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineTopologicalLorentzThreeFormDualInverse

open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality

noncomputable section

set_option autoImplicit false

/-- Reconstruct the unique three-form coordinates represented by a
continuous one-form dual. -/
def lorentzOneFormContinuousDualThreeForm
    (dual : LorentzBivectorOneForm →L[ℝ] ℝ) :
    PhysicalBivectorThreeForm :=
  fun internalPair triple =>
    let direction : LorentzianIndex := missingTripleOfOneForm triple
    oneWedgeThreeSign direction *
      dual (loweredLorentzBivectorOneFormCoordinate direction internalPair)

/-- Finite coordinate expansion of a lowered Lorentz bivector one-form. -/
theorem lorentzBivectorOneForm_eq_coordinateSum
    (oneForm : LorentzBivectorOneForm) :
    oneForm =
      ∑ direction : LorentzianIndex,
        ∑ internalPair : Fin 6,
          oneForm direction internalPair •
            loweredLorentzBivectorOneFormCoordinate direction internalPair := by
  funext direction internalPair
  classical
  fin_cases direction <;> fin_cases internalPair <;>
    simp [loweredLorentzBivectorOneFormCoordinate,
      Fin.sum_univ_four, Fin.sum_univ_six]

@[simp] theorem lorentzOneFormContinuousDualThreeForm_coordinate
    (dual : LorentzBivectorOneForm →L[ℝ] ℝ)
    (internalPair : Fin 6) (triple : Fin 4) :
    lorentzOneFormContinuousDualThreeForm dual internalPair triple =
      oneWedgeThreeSign (missingTripleOfOneForm triple) *
        dual (loweredLorentzBivectorOneFormCoordinate
          (missingTripleOfOneForm triple) internalPair) :=
  rfl

/-- Re-encoding the reconstructed three-form recovers the original dual on
every one-form, not only on coordinate probes. -/
@[simp] theorem lorentzThreeFormWedgeContinuousDual_reconstruct
    (dual : LorentzBivectorOneForm →L[ℝ] ℝ) :
    lorentzThreeFormWedgeContinuousDual
        (lorentzOneFormContinuousDualThreeForm dual) = dual := by
  apply ContinuousLinearMap.ext
  intro oneForm
  rw [lorentzBivectorOneForm_eq_coordinateSum oneForm]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro direction _
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [lorentzThreeFormWedgeContinuousDual_coordinate_apply]
  rw [lorentzOneFormContinuousDualThreeForm_coordinate,
    missingTripleOfOneForm_involutive]
  have signSquare := oneWedgeThreeSign_square direction
  ring_nf at signSquare ⊢
  rw [signSquare, one_mul]

/-- Conversely, coordinate reconstruction does not change a three-form. -/
@[simp] theorem lorentzOneFormContinuousDualThreeForm_wedgeDual
    (threeForm : PhysicalBivectorThreeForm) :
    lorentzOneFormContinuousDualThreeForm
        (lorentzThreeFormWedgeContinuousDual threeForm) = threeForm := by
  funext internalPair triple
  rw [lorentzOneFormContinuousDualThreeForm_coordinate,
    lorentzThreeFormWedgeContinuousDual_coordinate_apply,
    missingTripleOfOneForm_involutive]
  rw [← mul_assoc, oneWedgeThreeSign_square, one_mul]

/-- The inverse representation has a faithful zero fiber. -/
@[simp] theorem lorentzOneFormContinuousDualThreeForm_eq_zero_iff
    (dual : LorentzBivectorOneForm →L[ℝ] ℝ) :
    lorentzOneFormContinuousDualThreeForm dual = 0 ↔ dual = 0 := by
  constructor
  · intro reconstructedZero
    have encodedZero :
        lorentzThreeFormWedgeContinuousDual
            (lorentzOneFormContinuousDualThreeForm dual) = 0 :=
      (lorentzThreeFormWedgeContinuousDual_eq_zero_iff
        (lorentzOneFormContinuousDualThreeForm dual)).2 reconstructedZero
    rw [lorentzThreeFormWedgeContinuousDual_reconstruct] at encodedZero
    exact encodedZero
  · rintro rfl
    funext internalPair triple
    simp [lorentzOneFormContinuousDualThreeForm]

/-- Uniqueness: no second three-form can represent the same one-form dual. -/
theorem lorentzThreeFormRepresentative_existsUnique
    (dual : LorentzBivectorOneForm →L[ℝ] ℝ) :
    ∃! threeForm : PhysicalBivectorThreeForm,
      lorentzThreeFormWedgeContinuousDual threeForm = dual := by
  refine ⟨lorentzOneFormContinuousDualThreeForm dual,
    lorentzThreeFormWedgeContinuousDual_reconstruct dual, ?_⟩
  intro candidate candidateRepresents
  rw [← candidateRepresents]
  exact (lorentzOneFormContinuousDualThreeForm_wedgeDual candidate).symm

end

end
  SaturationMonoid.PhysicsCore.StageNineTopologicalLorentzThreeFormDualInverse
