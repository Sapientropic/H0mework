import H0mework.Versions.R2.Physics.Material.SiklosNullMatter

/-! Finite Dirac contraction of the null source contorsion normal form.
The action Cartan producer must identify its output with this table before
these kernel identities can be consumed as facts about a physical actual. -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace SaturationMonoid.PhysicsCore.Stage9C.Material

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open Stage9C.Dynamics.PlaneWave
open StageNineLorentzConnectionVariation
open StageNineGlobalIntegratedAction

noncomputable section

def sourceNullContorsion (q density : ℝ) : LorentzBivectorOneForm :=
  !![0, 0, 0, 0, 0, -(q*density/4);
     0, q*density/4, 0, q*density/4, 0, 0;
     -(density/4), 0, 0, 0, density/4, 0;
     0, 0, 0, 0, 0, q*density/4]

abbrev sourceNullContorsionTable : LorentzBivectorOneForm := sourceNullContorsion 1 1

def sourceNullContorsionDiracMatrix (q H density : ℝ) : DiracMatrix :=
  Complex.I • ∑ direction : LorentzianIndex,
    inverseCoframeDiracGamma
      { coframe := siklosCoframeScale q H, derivative := 0 } direction *
    diracSpinConnectionLift
      (lorentzSkewConnectionOfBivectorOneForm (sourceNullContorsion q density)) direction

private theorem spinLift_matrix (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) :
    let c := fun pair => (2 : ℂ)⁻¹ *
      (loweredLorentzConnectionCoefficient connection direction pair : ℂ)
    diracSpinConnectionLift connection direction =
      !![c 2 + Complex.I*c 5, c 0-Complex.I*c 1+Complex.I*c 3+c 4,0,0;
         c 0+Complex.I*c 1+Complex.I*c 3-c 4,-c 2-Complex.I*c 5,0,0;
         0,0,-c 2+Complex.I*c 5,-c 0+Complex.I*c 1+Complex.I*c 3+c 4;
         0,0,-c 0-Complex.I*c 1+Complex.I*c 3-c 4,c 2-Complex.I*c 5] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [diracSpinConnectionLift, lorentzBivectorFirst, lorentzBivectorSecond,
      diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_six] <;> ring

theorem sourceNullContorsionDiracMatrix_exact
    (q H density : ℝ) (hq : q ≠ 0) :
    sourceNullContorsionDiracMatrix q H density =
      !![0, 0, 0, 0;
         0, 0, 0, -(3*density/4 : ℂ);
         -(3*density/4 : ℂ), 0, 0, 0;
         0, 0, 0, 0] := by
  have complexNonzero : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  unfold sourceNullContorsionDiracMatrix inverseCoframeDiracGamma
  rw [siklosCoframeScale_inv q H hq]
  simp_rw [spinLift_matrix, loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  simp only [sourceNullContorsion, nullShear, adsCoframeScale, Fin.sum_univ_four,
    Matrix.mul_apply, Matrix.diagonal_apply]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree]
  all_goals field_simp [complexNonzero]; ring_nf
  all_goals simp [Complex.I_sq]

theorem sourceNullContorsion_matter_zero
    (q H density : ℝ) (hq : q ≠ 0) :
    diracMatrixMatterAction (sourceNullContorsionDiracMatrix q H density)
      diracSpinTwoMatterProbe = 0 := by
  rw [sourceNullContorsionDiracMatrix_exact q H density hq]
  funext spin
  fin_cases spin <;>
    simp [diracMatrixMatterAction, diracSpinTwoMatterProbe, Fin.sum_univ_four]

theorem sourceNullContorsion_dual_zero
    (q H density : ℝ) (hq : q ≠ 0) :
    diracSpinZeroMatterCoordinate.comp
      (diracMatrixMatterAction (sourceNullContorsionDiracMatrix q H density)) = 0 := by
  rw [sourceNullContorsionDiracMatrix_exact q H density hq]
  apply LinearMap.ext
  intro matter
  simp [diracMatrixMatterAction, diracSpinZeroMatterCoordinate, Fin.sum_univ_four]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material
