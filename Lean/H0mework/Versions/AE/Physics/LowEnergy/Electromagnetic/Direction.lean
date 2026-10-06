import H0mework.Versions.AB.Physics.MotherSource.HyperchargeResponse.Scalar

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.Direction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLimitScalarBalanceClosure Stage9C.Material.SpinPair
open DiracExteriorMatterAction Stage10
noncomputable section

/-- Color diagonal commuting with the actual source's color SU(2). -/
def colorNeutral : SU3BlockLieMatrix := by
  refine ⟨Matrix.diagonal ![Complex.I, Complex.I, -2*Complex.I], ?_, ?_⟩
  · ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.diagonal]
  · simp [Matrix.trace, Fin.sum_univ_three]
    ring

/-- The three commuting neutral directions, with the original native normalization. -/
def neutral (color weak hypercharge : ℝ) : P286LieBlockData :=
  (color • colorNeutral, weak • weakCartanGenerator, hypercharge • hyperchargeGenerator)

def fundamentalWeight (color weak hypercharge : ℝ) : SU7MotherIndex → ℝ
  | Sum.inl i => if i.val = 2 then -2*color else color
  | Sum.inr (Sum.inl i) => if i = 0 then weak else -weak
  | Sum.inr (Sum.inr (Sum.inl _)) => hypercharge
  | Sum.inr (Sum.inr (Sum.inr _)) => -hypercharge

def weight (color weak hypercharge : ℝ) {degree : ℕ} (index : ExteriorBasisIndex degree) : ℝ :=
  ∑ i ∈ index.1, fundamentalWeight color weak hypercharge i

theorem fundamental_action (color weak hypercharge : ℝ) (index : SU7MotherIndex) :
    fundamentalMotherLieAction (p286LieBlockEmbed (neutral color weak hypercharge))
      (su7FundamentalBasis index) =
    ((fundamentalWeight color weak hypercharge index : ℂ)*Complex.I) • su7FundamentalBasis index := by
  fin_cases index <;> ext row <;> fin_cases row <;>
    norm_num [fundamentalMotherLieAction, neutral, colorNeutral, p286LieBlockEmbed,
      rawP286LieBlock, weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
      weakCartanGenerator, weakCartanRaw, hyperchargeGenerator, su7FundamentalBasis,
      Matrix.mulVecLin, Matrix.mulVec, fundamentalWeight, Matrix.diagonal, Pi.single_apply] <;>
    first | simp | ring

/-- Every exterior charge is generated from the same fundamental action; no charge list is supplied. -/
theorem exterior_action (color weak hypercharge : ℝ) (degree : ℕ) (index : ExteriorBasisIndex degree) :
    exteriorMotherLieAction degree (p286LieBlockEmbed (neutral color weak hypercharge))
      (su7ExteriorBasis degree index) =
    ((weight color weak hypercharge index : ℂ)*Complex.I) • su7ExteriorBasis degree index := by
  classical
  rw [exteriorMotherLieAction_basis]
  have term (position : Fin degree) :
      (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree (p286LieBlockEmbed (neutral color weak hypercharge)) index position) =
      ((fundamentalWeight color weak hypercharge (exteriorPositionEquiv index position).1 : ℂ)*Complex.I) •
        su7ExteriorBasis degree index := by
    rw [exteriorBasisLieActionTerm_eq_update]
    have eigen := fundamental_action color weak hypercharge (exteriorPositionEquiv index position).1
    change fundamentalMotherLieAction (p286LieBlockEmbed (neutral color weak hypercharge))
      (exteriorBasisInput degree index position) = _ at eigen
    change fundamentalMotherLieAction (p286LieBlockEmbed (neutral color weak hypercharge))
      (exteriorBasisInput degree index position) =
      ((fundamentalWeight color weak hypercharge (exteriorPositionEquiv index position).1 : ℂ)*Complex.I) •
        exteriorBasisInput degree index position at eigen
    rw [eigen, (exteriorPower.ιMulti ℂ degree).map_update_smul,
      Function.update_eq_self, exteriorBasisInput_wedge_eq_basis]
  change (∑ position : Fin degree, (exteriorPower.ιMulti ℂ degree)
    (exteriorBasisLieActionInput degree (p286LieBlockEmbed (neutral color weak hypercharge)) index position)) = _
  simp_rw [term]
  rw [← Finset.sum_smul, ← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 3
  exact ((exteriorPositionEquiv index).sum_comp
    (fun i => fundamentalWeight color weak hypercharge i)).trans
      (Finset.sum_subtype index.1 (by simp) (fundamentalWeight color weak hypercharge)).symm

theorem vacuum_weights (color weak hypercharge : ℝ) (output input : Fin 2) :
    weight color weak hypercharge (finiteGenerationScalarIndex output input) =
      if output = 0 then (if input = 0 then -hypercharge else -weak)
      else if input = 0 then 2*color else 2*color-weak+hypercharge := by
  fin_cases output <;> fin_cases input <;>
    simp [weight, fundamentalWeight, finiteGenerationScalarIndex, finiteGenerationScalarSubset,
      colorZeroIndex, colorOneIndex, colorTwoIndex, weakOneIndex,
      hyperPlusIndex, hyperMinusIndex] <;> ring

theorem source_doublet_weight (color weak hypercharge : ℝ) (state : Fin 2) :
    weight color weak hypercharge (sourceColorDoubletIndex state) = color+hypercharge := by
  fin_cases state <;>
    simp [weight, fundamentalWeight, sourceColorDoubletIndex, hyperPlusIndex]

/-- The actual occupied source doublet couples to color + hypercharge, not to weak Cartan. -/
theorem source_doublet_action (color weak hypercharge : ℝ) (state : Fin 2) :
    exteriorSpinorMotherLieAction (p286LieBlockEmbed (neutral color weak hypercharge))
      (sourceColorDoubletMatter state) =
      (((color+hypercharge : ℝ) : ℂ)*Complex.I) • sourceColorDoubletMatter state := by
  simp [sourceColorDoubletMatter, exteriorSpinorMotherLieAction, exterior_action, source_doublet_weight]

def scalarCharge (direction : P286LieBlockData) : ScalarCoordinateCarrier :=
  scalarMotherLieAction (p286LieBlockEmbed direction)
    (sourceGeneratedVacuumCoordinates Stage10.Runtime.source)

/-- The full scalar response map retains all native directions and their mixed pairings. -/
def scalarGram (first second : P286LieBlockData) : ℝ :=
  scalarCoordinatePairingRe (scalarCharge first) (scalarCharge second)

theorem scalar_coordinates (color weak hypercharge : ℝ) (index : ScalarBasisIndex) :
    scalarCharge (neutral color weak hypercharge) index =
      if index = finiteGenerationScalarIndex 0 0 then (-hypercharge : ℂ)*Complex.I
      else if index = finiteGenerationScalarIndex 0 1 then (-weak : ℂ)*Complex.I
      else if index = finiteGenerationScalarIndex 1 0 then (2*color : ℂ)*Complex.I
      else if index = finiteGenerationScalarIndex 1 1 then ((2*color-weak+hypercharge : ℝ) : ℂ)*Complex.I
      else 0 := by
  have h001 : finiteGenerationScalarIndex 0 0 ≠ finiteGenerationScalarIndex 0 1 := by decide
  have h010 : finiteGenerationScalarIndex 0 0 ≠ finiteGenerationScalarIndex 1 0 := by decide
  have h011 : finiteGenerationScalarIndex 0 0 ≠ finiteGenerationScalarIndex 1 1 := by decide
  have h110 : finiteGenerationScalarIndex 0 1 ≠ finiteGenerationScalarIndex 1 0 := by decide
  have h111 : finiteGenerationScalarIndex 0 1 ≠ finiteGenerationScalarIndex 1 1 := by decide
  have h211 : finiteGenerationScalarIndex 1 0 ≠ finiteGenerationScalarIndex 1 1 := by decide
  unfold scalarCharge scalarMotherLieAction
  rw [Runtime.source_eq]
  simp only [sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply,
    positive_sourceGeneratedVacuumBase, finiteGenerationJointBreakingScalar, map_sum,
    finiteGenerationBreakingTensor, exterior_action, vacuum_weights, map_smul]
  by_cases first : index = finiteGenerationScalarIndex 0 0
  · subst index
    simp [scalarCoordinateEquiv, Fin.sum_univ_two, h001, h010, h011]
  · by_cases second : index = finiteGenerationScalarIndex 0 1
    · subst index
      simp [scalarCoordinateEquiv, Fin.sum_univ_two, h110, h111, h001.symm]
    · by_cases third : index = finiteGenerationScalarIndex 1 0
      · subst index
        simp [scalarCoordinateEquiv, Fin.sum_univ_two, h211, h010.symm, h110.symm]
      · by_cases fourth : index = finiteGenerationScalarIndex 1 1
        · subst index
          simp [scalarCoordinateEquiv, Fin.sum_univ_two, h011.symm, h111.symm, h211.symm]
        · simp [scalarCoordinateEquiv, Fin.sum_univ_two, first, second, third, fourth]

/-- The original four vacuum channels generate all color/weak/Y mixed terms. -/
theorem scalar_norm (color weak hypercharge : ℝ) :
    scalarCoordinateSquaredNorm (scalarCharge (neutral color weak hypercharge)) =
      hypercharge^2+weak^2+4*color^2+(2*color-weak+hypercharge)^2 := by
  have h001 : finiteGenerationScalarIndex 0 0 ≠ finiteGenerationScalarIndex 0 1 := by decide
  have h010 : finiteGenerationScalarIndex 0 0 ≠ finiteGenerationScalarIndex 1 0 := by decide
  have h011 : finiteGenerationScalarIndex 0 0 ≠ finiteGenerationScalarIndex 1 1 := by decide
  have h110 : finiteGenerationScalarIndex 0 1 ≠ finiteGenerationScalarIndex 1 0 := by decide
  have h111 : finiteGenerationScalarIndex 0 1 ≠ finiteGenerationScalarIndex 1 1 := by decide
  have h211 : finiteGenerationScalarIndex 1 0 ≠ finiteGenerationScalarIndex 1 1 := by decide
  have term (index : ScalarBasisIndex) :
      Complex.normSq (scalarCharge (neutral color weak hypercharge) index) =
        (if index = finiteGenerationScalarIndex 0 0 then hypercharge^2 else 0) +
        (if index = finiteGenerationScalarIndex 0 1 then weak^2 else 0) +
        (if index = finiteGenerationScalarIndex 1 0 then 4*color^2 else 0) +
        (if index = finiteGenerationScalarIndex 1 1 then (2*color-weak+hypercharge)^2 else 0) := by
    rw [scalar_coordinates]
    split_ifs <;> simp_all [Complex.normSq_apply] <;> ring
  simp only [scalarCoordinateSquaredNorm, term, Finset.sum_add_distrib]
  simp

theorem scalar_norm_zero_iff (color weak hypercharge : ℝ) :
    scalarCoordinateSquaredNorm (scalarCharge (neutral color weak hypercharge)) = 0 ↔
      color = 0 ∧ weak = 0 ∧ hypercharge = 0 := by
  rw [scalar_norm]
  constructor
  · intro zero
    have colorZero : color = 0 := by
      nlinarith [sq_nonneg weak, sq_nonneg hypercharge, sq_nonneg (2*color-weak+hypercharge), sq_nonneg color]
    have weakZero : weak = 0 := by
      nlinarith [sq_nonneg weak, sq_nonneg hypercharge, sq_nonneg (2*color-weak+hypercharge), sq_nonneg color]
    have hyperZero : hypercharge = 0 := by
      nlinarith [sq_nonneg weak, sq_nonneg hypercharge, sq_nonneg (2*color-weak+hypercharge), sq_nonneg color]
    exact ⟨colorZero, weakZero, hyperZero⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.Direction
