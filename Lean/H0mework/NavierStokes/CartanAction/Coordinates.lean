import H0mework.NavierStokes.MaterialAction.PauliPairing

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanCoordinates

open PhysicsCore DiracCliffordRepresentation PointwiseDiracSpinConnectionLift ProofFreeRicherAnholonomicSource
open StageNineResidualLinearPlebanskiTorsionReduction StageNineCartanTorsionThreeFormCoordinates
open StageNineTopologicalGravityCurvatureVariancePairing StageNineLorentzConnectionVariation
open StageNineCartanTorsionThreeFormEquiv StageNineCartanContorsionTorsionEquiv
open StageNineTopologicalLorentzThreeFormDuality StageNineTopologicalLorentzThreeFormDualInverse
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeSourceCartan NativeCartanSpinSupport NativeCartanContorsionSupport
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativeCartanClifford NativePauliPairing

noncomputable section

def currentVector (velocity : PhysicalSpace) : Fin 4 → ℝ :=
  ![NativeCanonicalFluidCoframe.density velocity, velocity 0, velocity 1, velocity 2]

def tripleProfile (current : Fin 4 → ℝ) : LorentzBivectorOneForm :=
  !![0, 0, 0, -current 1, -current 2, -current 3;
     0, current 3, -current 2, -current 0, 0, 0;
     -current 3, 0, current 1, 0, -current 0, 0;
     current 2, -current 1, 0, 0, 0, -current 0]

theorem triple_profile (velocity : PhysicalSpace) (direction : Fin 4) (pair : Fin 6) :
    tripleCurrent velocity direction (lorentzBivectorFirst pair) (lorentzBivectorSecond pair) =
      tripleProfile (currentVector velocity) direction pair := by
  rw [triple_block]
  fin_cases direction <;> fin_cases pair <;>
    simp [blockPair, hermitianBlock, spinAction, blockAction, bivectorBlock, spinPrincipal,
      tripleProfile, currentVector, pauli, normalizedVelocity, NativeCanonicalFluidCoframe.density,
      EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im,
      map_ofNat] <;> ring

def profile (current : Fin 4 → ℝ) : LorentzBivectorOneForm :=
  !![0, 0, 0, -current 1, -current 2, -current 3;
     0, current 3, -current 2, current 0, 0, 0;
     -current 3, 0, current 1, 0, current 0, 0;
     current 2, -current 1, 0, 0, 0, current 0]

def candidate (velocity : PhysicalSpace) : LorentzBivectorOneForm :=
  pushforwardLorentzBivectorOneForm (NativeCanonicalFluidCoframe.coframe velocity)
    (fun direction pair => profile (currentVector velocity) direction pair / 4)

theorem candidate_component (velocity : PhysicalSpace) (direction : Fin 4) (pair : Fin 6) :
    candidate velocity direction pair = NativeCanonicalFluidCoframe.diagonal velocity direction *
      profile (currentVector velocity) direction pair / 4 := by
  simp [candidate, pushforwardLorentzBivectorOneForm, NativeCanonicalFluidCoframe.coframe,
    Matrix.mulVec_diagonal, mul_div_assoc]

private theorem response_coordinate (velocity : PhysicalSpace) (pair : Fin 6) (triple : Fin 4) :
    spinResponse velocity pair triple =
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        (NativeMaterialMomentumJet.coefficient velocity (missingTripleOfOneForm triple) / 2 *
          tripleProfile (currentVector velocity) (missingTripleOfOneForm triple) pair)) := by
  simpa only [missingTripleOfOneForm_involutive, spinCLM_coordinate, triple_profile] using
    spinResponse_coordinate velocity (missingTripleOfOneForm triple) pair

def torsionProfile (current : Fin 4 → ℝ) : PointwiseCartanTorsionTwoForm :=
  ⟨!![0, 0, current 3 / 2, -current 2 / 2;
      0, -current 3 / 2, 0, current 1 / 2;
      0, current 2 / 2, -current 1 / 2, 0;
      -current 1 / 2, -current 0 / 2, 0, 0;
      -current 2 / 2, 0, -current 0 / 2, 0;
      -current 3 / 2, 0, 0, -current 0 / 2]⟩

private theorem profile_torsion (current : Fin 4 → ℝ) :
    minkowskiRaiseCartanTorsion (internalFrameCartanTorsion
      (fun direction pair => profile current direction pair / 4)) = torsionProfile current := by
  ext pair internal
  fin_cases pair <;> fin_cases internal <;>
    simp [minkowskiRaiseCartanTorsion, internalFrameCartanTorsion, profile, torsionProfile,
      loweredLorentzBivectorMatrix, orientedLorentzBivectorBasisCoefficient,
      Fin.sum_univ_six, pairFirst, pairSecond, minkowskiInternalSign] <;> ring

theorem candidate_torsion (velocity : PhysicalSpace) :
    cartanTorsionOfContorsion (NativeCanonicalFluidCoframe.coframe velocity) (candidate velocity) =
      ⟨fun pair internal => NativeCanonicalFluidCoframe.diagonal velocity (pairFirst pair) *
        NativeCanonicalFluidCoframe.diagonal velocity (pairSecond pair) *
          torsionProfile (currentVector velocity) pair internal⟩ := by
  rw [cartanTorsionOfContorsion, candidate, pullback_pushforwardLorentzBivectorOneForm _
    (NativeCanonicalFluidCoframe.coframe_nondegenerate velocity), profile_torsion]
  ext pair internal
  simp [pushforwardCartanTorsionTwoForm, NativeCanonicalFluidCoframe.coframe, diagonal_twoForm]

private theorem diagonal_response (diagonal : Fin 4 → ℝ) (torsion : PointwiseCartanTorsionTwoForm) :
    cartanTorsionThreeForm (Matrix.diagonal diagonal) torsion =
      !![-diagonal 2 * torsion 0 3, diagonal 3 * torsion 0 2, diagonal 3 * torsion 1 2 + diagonal 2 * torsion 2 3, diagonal 3 * torsion 5 2 - diagonal 2 * torsion 4 3;
     -diagonal 1 * torsion 1 3, -diagonal 1 * torsion 2 3 - diagonal 3 * torsion 0 1, -diagonal 3 * torsion 1 1, diagonal 1 * torsion 3 3 - diagonal 3 * torsion 5 1;
     diagonal 2 * torsion 0 1 + diagonal 1 * torsion 1 2, diagonal 1 * torsion 2 2, -diagonal 2 * torsion 2 1, diagonal 2 * torsion 4 1 - diagonal 1 * torsion 3 2;
     diagonal 1 * torsion 1 0 + diagonal 0 * torsion 5 1, diagonal 1 * torsion 2 0 - diagonal 0 * torsion 4 1, diagonal 0 * torsion 3 1, -diagonal 1 * torsion 3 0;
     -diagonal 2 * torsion 0 0 + diagonal 0 * torsion 5 2, -diagonal 0 * torsion 4 2, diagonal 2 * torsion 2 0 + diagonal 0 * torsion 3 2, -diagonal 2 * torsion 4 0;
     diagonal 0 * torsion 5 3, -diagonal 3 * torsion 0 0 - diagonal 0 * torsion 4 3, -diagonal 3 * torsion 1 0 + diagonal 0 * torsion 3 3, -diagonal 3 * torsion 5 0] := by
  funext pair triple
  fin_cases pair <;> fin_cases triple <;>
    simp [cartanTorsionThreeForm, internalBivectorDualThreeForm, lorentzianCoframeHodge,
      cartanTorsionCoframeWedgeThreeForm, torsionCoframeWedgeThreeForm,
      rawPointwiseCartanTorsion, orderedCartanTorsionComponent,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, threeFormFirst, threeFormSecond, threeFormThird,
      Fin.sum_univ_six] <;> ring

theorem candidate_response (velocity : PhysicalSpace) :
    cartanTorsionThreeForm (NativeCanonicalFluidCoframe.coframe velocity)
      (cartanTorsionOfContorsion (NativeCanonicalFluidCoframe.coframe velocity) (candidate velocity)) =
        spinResponse velocity := by
  rw [candidate_torsion, NativeCanonicalFluidCoframe.coframe, diagonal_response]
  funext pair triple
  rw [response_coordinate]
  simp only [NativeMaterialMomentumJet.coefficient, NativeMaterialMomentumJet.volumeFactor,
    NativeCanonicalFluidCoframe.coframe_volume]
  fin_cases pair <;> fin_cases triple <;>
    simp [torsionProfile, pairFirst, pairSecond, NativeCanonicalFluidCoframe.diagonal,
      missingTripleOfOneForm, oneWedgeThreeSign, tripleProfile]
  all_goals field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne']

theorem contorsion_eq (velocity : PhysicalSpace) : contorsion velocity = candidate velocity := by
  have equal := cartanTorsionThreeForm_injective (NativeCanonicalFluidCoframe.coframe velocity)
    (NativeCanonicalFluidCoframe.coframe_nondegenerate velocity)
    ((candidate_response velocity).trans (torsion_response velocity).symm)
  rw [contorsion, ← equal, contorsionOfCartanTorsion_leftInverse _
    (NativeCanonicalFluidCoframe.coframe_nondegenerate velocity)]

end
end SaturationMonoid.NavierStokes.NativeCartanCoordinates
