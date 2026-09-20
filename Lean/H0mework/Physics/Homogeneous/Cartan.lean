import H0mework.Physics.CartanReduction.AlgebraicCartan

/-! The homogeneous coframe and isotropic spatial Cartan connection. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineHolonomicField StageNineCoframeFirstJet
open StageNineLorentzConnectionVariation

noncomputable section

def homogeneousCoframe (lapse : ℝ) : LorentzianCoframe :=
  Matrix.diagonal ![lapse,1,1,1]

def homogeneousContorsion (spin : ℝ) : LorentzBivectorOneForm :=
  !![0,0,0,0,0,0;0,0,0,spin,0,0;0,0,0,0,spin,0;0,0,0,0,0,spin]

def homogeneousConnection (spin : ℝ) : PointwiseLorentzSpinConnection :=
  lorentzSkewConnectionOfBivectorOneForm (homogeneousContorsion spin)

theorem homogeneousCoframe_det (lapse : ℝ) :
    Matrix.det (homogeneousCoframe lapse) = lapse := by
  simp [homogeneousCoframe, Fin.prod_univ_four]

theorem homogeneousCoframe_nondegenerate (lapse : ℝ) (positive : 0 < lapse) :
    Matrix.det (homogeneousCoframe lapse) ≠ 0 := by
  rw [homogeneousCoframe_det]
  exact ne_of_gt positive

theorem homogeneousCoframe_inv (lapse : ℝ) (nonzero : lapse ≠ 0) :
    (homogeneousCoframe lapse)⁻¹ = homogeneousCoframe lapse⁻¹ := by
  apply Matrix.inv_eq_left_inv
  unfold homogeneousCoframe
  rw [Matrix.diagonal_mul_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;> simp [nonzero]

open PointwiseLorentzianCoframeJet in
theorem homogeneousCoframe_generatedLC (lapse : ℝ) (point : BasePoint) :
    (holonomicCoframeFirstJetAt (fun _ => homogeneousCoframe lapse) point).lorentzSpinConnection = 0 := by
  have firstJet : holonomicCoframeFirstJetAt (fun _ => homogeneousCoframe lapse) point =
      ({ coframe := homogeneousCoframe lapse, derivative := 0 } : PointwiseLorentzianCoframeJet) := by
    apply coframeJet_eq_of_fields_eq
    · rfl
    · funext μ a ν
      simp [holonomicCoframeFirstJetAt]
  rw [firstJet]
  funext μ a b
  simp [lorentzSpinConnection, lorentzSpinConnectionMatrix, coordinateConnectionMatrix,
    affineConnectionMatrix, coframeDerivativeMatrix, leviCivitaConnection,
    leviCivitaConnectionVector, loweredLeviCivitaVector, loweredLeviCivitaConnection,
    metricDerivative, Matrix.mul_apply, Matrix.mulVec, dotProduct]


end
end SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous
