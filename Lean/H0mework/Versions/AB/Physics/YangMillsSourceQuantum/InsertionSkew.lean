import H0mework.Versions.AB.Physics.YangMillsSourceQuantum.InsertionForcing
import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingResponse
import H0mework.Physics.Dirac.FullDiracAdjointLocalOperator
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The original temporal gauge insertion is skew for the full physical
mother pairing. Its lapse and temporal-connection terms remain unchanged. -/

set_option autoImplicit false
open scoped InnerProductSpace Kronecker Matrix
namespace SaturationMonoid.PhysicsCore.YangMills.Response.Skew
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracCliffordRepresentation DiracExteriorMatterAction StageNineExteriorMotherLieRepresentation
open StageNineFullDiracAdjointLocalOperator StageNineFullDiracAdjointMaterial
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation FullPairing
open StageNineCurrentCoframeMatterTemporalPrincipal Stage9C.Material.SpinPair Forcing
open Stage9C.Dynamics.Homogeneous StageNineP286GaugeConnectionVariationDensity SU7ExteriorBreakingYukawa
noncomputable section
local instance : DecidableEq Sector := Classical.decEq _

private def asOperator : Mother →ₐ[ℂ] (Hilbert →L[ℂ] Hilbert) where
  toFun := operator
  map_zero' := by ext v; simp [operator]
  map_one' := by ext v; simp [operator]
  map_add' A B := by ext v; simp [operator]
  map_mul' A B := by ext v; simp [operator]
  commutes' c := by ext v; simp [operator, Algebra.algebraMap_eq_smul_one]

private theorem spin_matrix (A : DiracMatrix) :
    asOperator (diracMatrixMatterAction A) =
      (Matrix.toEuclideanCLM (n := FullPairing.Index) (𝕜 := ℂ)) (A ⊗ₖ (1 : Matrix Sector Sector ℂ)) := by
  ext v i
  rcases i with ⟨spin, sector⟩
  have read := operator_coordinates (diracMatrixMatterAction A) (naturalCoordinates.symm v)
  rw [naturalCoordinates.apply_symm_apply] at read
  change operator (diracMatrixMatterAction A) v (spin, sector) =
    ((A ⊗ₖ (1 : Matrix Sector Sector ℂ)) *ᵥ (v : FullPairing.Index → ℂ)) (spin, sector)
  rw [read]
  conv_rhs => rw [← naturalCoordinates.apply_symm_apply v]
  simp [naturalCoordinates_apply, diracMatrixMatterAction,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : Hilbert => A spin j * z (j, sector))
    (naturalCoordinates.apply_symm_apply v)

private theorem spin_selfAdjoint (A : DiracMatrix) (hA : A.IsHermitian) :
    star (asOperator (diracMatrixMatterAction A)) = asOperator (diracMatrixMatterAction A) := by
  rw [spin_matrix, ← map_star]
  congr 1
  change (A ⊗ₖ (1 : Matrix Sector Sector ℂ)).conjTranspose = _
  rw [Matrix.conjTranspose_kronecker, hA.eq, Matrix.conjTranspose_one]

private theorem gauge_skew (M : SU7MotherLieMatrix) :
    star (asOperator (diracExteriorMotherLieAction M)) = -asOperator (diracExteriorMotherLieAction M) := by
  symm
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  obtain ⟨v, rfl⟩ := naturalCoordinates.surjective v
  obtain ⟨w, rfl⟩ := naturalCoordinates.surjective w
  change inner ℂ (-(operator (diracExteriorMotherLieAction M) (naturalCoordinates v))) (naturalCoordinates w) = _
  rw [inner_neg_left, operator_coordinates]
  change -inner ℂ (naturalCoordinates (diracExteriorMotherLieAction M v)) (naturalCoordinates w) =
    inner ℂ (naturalCoordinates v) (operator (diracExteriorMotherLieAction M) (naturalCoordinates w))
  rw [operator_coordinates, natural_inner, natural_inner]
  have zero := Finset.sum_eq_zero (fun i (_ : i ∈ (Finset.univ : Finset DiracSpinorIndex)) =>
    fullInternalPair_motherLie_skew M (v i) (w i))
  rw [Finset.sum_add_distrib] at zero
  change -(∑ i, fullInternalPair (exteriorSpinorMotherLieAction M (v i)) (w i)) =
    ∑ i, fullInternalPair (v i) (exteriorSpinorMotherLieAction M (w i))
  linear_combination -zero

private theorem product_skew (A : DiracMatrix) (hA : A.IsHermitian) (M : SU7MotherLieMatrix) :
    star (asOperator ((diracMatrixMatterAction A).comp (diracExteriorMotherLieAction M))) =
      -asOperator ((diracMatrixMatterAction A).comp (diracExteriorMotherLieAction M)) := by
  change star (asOperator (diracMatrixMatterAction A * diracExteriorMotherLieAction M)) = _
  rw [map_mul, star_mul, gauge_skew, spin_selfAdjoint A hA]
  have negProduct : -asOperator (diracExteriorMotherLieAction M) *
      asOperator (diracMatrixMatterAction A) =
      -(asOperator (diracExteriorMotherLieAction M) * asOperator (diracMatrixMatterAction A)) := by ext v; rfl
  rw [negProduct, ← map_mul]
  congr 1
  exact congrArg asOperator (diracMatrixMatterAction_commutes_internal A
    (exteriorSpinorMotherLieAction M)).symm

private theorem temporal_inverse :
    currentCoframeMatterTemporalPrincipalInverse (homogeneousCoframe lapse) =
      (lapse : ℂ) • (Complex.I • diracMatrixMatterAction diracGammaZero) := by
  have q : coframeTemporalPrincipalScalar (homogeneousCoframe lapse) = (lapse⁻¹)^2 := by
    rw [coframeTemporalPrincipalScalar, homogeneousCoframe_inv lapse lapse_pos.ne']
    simp [homogeneousCoframe, minkowskiInternalSign, Fin.sum_univ_four]
  apply LinearMap.ext
  intro v
  simp only [currentCoframeMatterTemporalPrincipalInverse, q,
    currentCoframeMatterTemporalPrincipal, LinearMap.smul_apply,
    homogeneousInverseGamma lapse lapse_pos.ne',
    diracMatrixMatterAction_smul_matrix, smul_smul]
  congr 1
  push_cast
  field_simp [lapse_pos.ne']

private theorem insertion_formula (C : StageNineHolonomicConfiguration)
    (η : BasePoint → StageNineP286GaugeConnectionVariation.P286GaugeOneForm) (p : BasePoint)
    (coframe : C.coframe p = homogeneousCoframe lapse) :
    insertion C η p =
      (lapse : ℂ) • ∑ j : Fin 3,
        (diracMatrixMatterAction (diracGammaZero * diracGamma j.succ)).comp
          (diracExteriorMotherLieAction (StageNineP286GaugeConnectionVariation.p286GaugeConnectionMotherVariation η p j.succ)) -
        diracExteriorMotherLieAction (StageNineP286GaugeConnectionVariation.p286GaugeConnectionMotherVariation η p 0) := by
  have spatial (j : Fin 3) : inverseCoframeDiracGamma
      { coframe := homogeneousCoframe lapse, derivative := 0 } j.succ = diracGamma j.succ := by
    rw [homogeneousInverseGamma lapse lapse_pos.ne']
    simp
  apply LinearMap.ext
  intro v
  simp only [insertion, spatialInsertion, coframe, temporal_inverse, spatial,
    LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    diracMatrixMatterAction_mul]
  simp only [smul_smul]
  rw [← Finset.smul_sum, smul_smul]
  have scalar : Complex.I * ((lapse : ℂ) * Complex.I) = -(lapse : ℂ) := by
    rw [mul_left_comm, Complex.I_mul_I, mul_neg_one]
  rw [scalar]
  module

theorem insertion_skew
    (η : BasePoint → StageNineP286GaugeConnectionVariation.P286GaugeOneForm) (p : BasePoint) :
    star (operator (insertion Stage10.Runtime.configuration η p)) =
      -operator (insertion Stage10.Runtime.configuration η p) := by
  let U := Stage10.Recovery.stageOneThroughTenClosure
  have same := U.final.recoversStageNine.trans U.final.stageNine.actualGenerated
  have coframe : Stage10.Runtime.configuration.coframe p = homogeneousCoframe lapse := by
    rw [same, actual_coframe]
  change star (asOperator (insertion Stage10.Runtime.configuration η p)) =
    -asOperator (insertion Stage10.Runtime.configuration η p)
  rw [insertion_formula _ η p coframe]
  have each (j : Fin 3) := product_skew
    (diracGammaZero * diracGamma j.succ) (diracGammaZero_mul_spatial_isHermitian j)
    (StageNineP286GaugeConnectionVariation.p286GaugeConnectionMotherVariation η p j.succ)
  simp only [map_sub asOperator, map_smul asOperator, map_sum asOperator]
  change ContinuousLinearMap.adjoint _ = _
  simp only [map_sub ContinuousLinearMap.adjoint, map_smulₛₗ ContinuousLinearMap.adjoint,
    map_sum ContinuousLinearMap.adjoint]
  simp only [← ContinuousLinearMap.star_eq_adjoint]
  simp_rw [each, gauge_skew]
  simp only [Complex.conj_ofReal, Finset.sum_neg_distrib, smul_neg]
  abel

end
end SaturationMonoid.PhysicsCore.YangMills.Response.Skew
