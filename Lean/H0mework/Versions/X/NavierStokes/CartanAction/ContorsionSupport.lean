import H0mework.Versions.X.NavierStokes.CartanAction.TorsionSupport

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanContorsionSupport

open PhysicsCore ProofFreeRicherAnholonomicSource StageNineLorentzConnectionVariation
open StageNineGlobalIntegratedAction StageNineCartanContorsionTorsionEquiv
open StageNineResidualLinearPlebanskiTorsionReduction
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeSourceCartan NativeCartanTorsionSupport

noncomputable section

theorem diagonal_twoForm (diagonal : Fin 4 → ℝ) (form : Fin 6 → ℝ) (pair : Fin 6) :
    coframeTwoFormLinear (Matrix.diagonal diagonal) form pair =
      diagonal (pairFirst pair) * diagonal (pairSecond pair) * form pair := by
  fin_cases pair <;> simp [coframeTwoFormLinear, coframeWedge, pairFirst, pairSecond, Fin.sum_univ_six]

def internalTorsion (velocity : PhysicalSpace) : PointwiseCartanTorsionTwoForm :=
  minkowskiRaiseCartanTorsion (pullbackCartanTorsionTwoForm
    (NativeCanonicalFluidCoframe.coframe velocity) (torsion velocity))

theorem internalTorsion_support (velocity : PhysicalSpace) (pair : Fin 6) (internal : Fin 4)
    (repeated : internal = pairFirst pair ∨ internal = pairSecond pair) :
    internalTorsion velocity pair internal = 0 := by
  change minkowskiInternalSign internal *
    coframeTwoFormLinear ((NativeCanonicalFluidCoframe.coframe velocity)⁻¹).transpose
      (fun spacetimePair => (torsion velocity).component spacetimePair internal) pair = 0
  rw [NativeCanonicalFluidCoframe.coframe_inv, Matrix.diagonal_transpose, diagonal_twoForm,
    torsion_support velocity pair internal repeated, mul_zero, mul_zero]

theorem ordered_internalTorsion_support (velocity : PhysicalSpace) (internal first second : Fin 4)
    (repeated : internal = first ∨ internal = second) :
    orderedCartanTorsionComponent (internalTorsion velocity) internal first second = 0 := by
  rcases repeated with same | same <;> subst internal <;>
    fin_cases first <;> fin_cases second <;>
    simp [orderedCartanTorsionComponent, orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
      Fin.sum_univ_six, internalTorsion_support]

/-- The original KIN-2 contorsion preserves the source spin support on the actual diagonal frame. -/
theorem contorsion_support (velocity : PhysicalSpace) (direction : Fin 4) (pair : Fin 6)
    (repeated : direction = pairFirst pair ∨ direction = pairSecond pair) :
    contorsion velocity direction pair = 0 := by
  change ((NativeCanonicalFluidCoframe.coframe velocity).transpose *ᵥ
    (fun internalDirection => internalFrameContorsionOfTorsion (internalTorsion velocity) internalDirection pair)
      ) direction = 0
  rw [NativeCanonicalFluidCoframe.coframe, Matrix.diagonal_transpose, Matrix.mulVec_diagonal]
  rcases repeated with first | second
  · rw [first]
    simp [internalFrameContorsionOfTorsion, ordered_internalTorsion_support, internalTorsion_support]
  · rw [second]
    simp [internalFrameContorsionOfTorsion, ordered_internalTorsion_support, internalTorsion_support]

end
end SaturationMonoid.NavierStokes.NativeCartanContorsionSupport
