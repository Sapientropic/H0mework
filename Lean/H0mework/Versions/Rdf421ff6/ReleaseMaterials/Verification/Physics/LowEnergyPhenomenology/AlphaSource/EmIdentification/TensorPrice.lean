import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceTensorPriceEnvelope
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ExteriorChannelCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceTensorPriceEnvelopeOwn
open SaturationMonoid.PhysicsCore
open StageNineDynamicBreakingVacuum SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum DiracCliffordRepresentation
open ActualSourceFiniteYukawaPriceOwn
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
local instance : LinearOrder SU7MotherLieAlgebra.SU7MotherIndex :=
  LinearOrder.lift' SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal.smBlockIndexEquivFin7 SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal.smBlockIndexEquivFin7.injective
local instance : DecidableEq ScalarBasisIndex := Classical.decEq _
local instance : DecidableEq SU7MotherLieAlgebra.SU7MotherIndex := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

def complexPrice (z : ℂ) : ℝ := |z.re| + |z.im|
def spinGate (s t : DiracSpinorIndex) : ℝ :=
  if (s = 0 ∧ t = 2) ∨ (s = 1 ∧ t = 3) then 1 else 0

theorem spinEntry_source (s t : DiracSpinorIndex) : spinEntry s t = (spinGate s t : ℂ) := by
  fin_cases s <;> fin_cases t <;>
    norm_num [DiracSpinorIndex, spinEntry, spinGate, diracGammaZero, rightChiralityProjector,
      diracGammaFive, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.cons_val, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
    <;> simp only [Fin.ext_iff] <;> norm_num

theorem spinGate_sum : (∑ s, ∑ t, spinGate s t) = 2 := by
  norm_num [DiracSpinorIndex, spinGate, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
  simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.card_singleton, Nat.cast_one]
  norm_num

theorem complexPrice_nonnegative (z : ℂ) : 0 ≤ complexPrice z := by
  unfold complexPrice
  positivity

theorem complexPrice_real_mul (r : ℝ) (nonnegative : 0 ≤ r) (z : ℂ) :
    complexPrice ((r : ℂ) * z) = r * complexPrice z := by
  simp [complexPrice, Complex.mul_re, Complex.mul_im, abs_mul, abs_of_nonneg nonnegative,
    mul_add]

theorem complexPrice_neg (z : ℂ) : complexPrice (-z) = complexPrice z := by
  simp [complexPrice]

theorem complexPrice_basis_column (b : ExteriorBasisIndex 6) :
    (∑ six : ExteriorBasisIndex 6,
      complexPrice ((su7ExteriorBasis 6).repr (su7ExteriorBasis 6 b) six)) = 1 := by
  classical
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  have price (six : ExteriorBasisIndex 6) :
      complexPrice (if b = six then (1 : ℂ) else 0) = if b = six then (1 : ℝ) else 0 := by
    split_ifs <;> norm_num [complexPrice]
  simp_rw [price]
  simp

theorem original_internal_column_price (a : ScalarBasisIndex) (two : ExteriorBasisIndex 2) :
    (∑ six : ExteriorBasisIndex 6, complexPrice
      (internalEntry a (Sum.inl six) (Sum.inr (Sum.inl two)))) =
      if Disjoint two.val a.val then 1 else 0 := by
  classical
  change (∑ six : ExteriorBasisIndex 6, complexPrice
    ((su7ExteriorBasis 6).repr (exteriorYukawaMassMap (su7ExteriorBasis 4 a)
      (su7ExteriorBasis 2 two)) six)) = _
  by_cases h : Disjoint two.val a.val
  · rw [if_pos h, exteriorYukawaMassMap_basisPair_of_disjoint two a h]
    rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint h).sign with plus | minus
    · rw [plus]
      simpa only [one_smul] using complexPrice_basis_column (Set.powersetCard.disjUnion h)
    · rw [minus]
      simpa only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul, map_neg, Finsupp.neg_apply, complexPrice_neg] using
        complexPrice_basis_column (Set.powersetCard.disjUnion h)
  · rw [if_neg h, exteriorYukawaMassMap_basisPair_of_not_disjoint two a h]
    simp [complexPrice]

theorem original_internal_price (a : ScalarBasisIndex) :
    (∑ i : LowEnergy.Quantum.InternalIndex, ∑ j : LowEnergy.Quantum.InternalIndex,
      complexPrice (internalEntry a i j)) = 3 := by
  classical
  simp only [Fintype.sum_sum_type, internalEntry, complexPrice, Complex.zero_re,
    Complex.zero_im, abs_zero, zero_add, Finset.sum_const_zero, add_zero, zero_add]
  rw [Finset.sum_comm]
  change (∑ two : ExteriorBasisIndex 2, ∑ six : ExteriorBasisIndex 6,
    complexPrice (internalEntry a (Sum.inl six) (Sum.inr (Sum.inl two)))) = 3
  simp_rw [original_internal_column_price]
  have cardinal := original_disjoint_two_card a
  simpa only [originalDisjointTwo, Fintype.card_subtype, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, Finset.sum_boole] using
    (congrArg (fun n : ℕ => (n : ℝ)) cardinal)


theorem original_tensor_entry_price (a : ScalarBasisIndex) (i j : LowEnergy.Quantum.Index) :
    tensorEntryPrice a i j = lapse * spinGate i.1 j.1 * complexPrice (internalEntry a i.2 j.2) := by
  change complexPrice (sourceTensor a i j) = _
  rw [original_tensor_entry, spinEntry_source]
  unfold spinGate
  split_ifs
  · simpa only [Complex.ofReal_one, mul_one] using
      complexPrice_real_mul lapse Stage9C.Material.SpinPair.lapse_pos.le (internalEntry a i.2 j.2)
  · simp [complexPrice]

theorem original_scalar_tensor_price (a : ScalarBasisIndex) :
    (∑ i : LowEnergy.Quantum.Index, ∑ j : LowEnergy.Quantum.Index, tensorEntryPrice a i j) =
      6 * lapse := by
  simp_rw [original_tensor_entry_price]
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_sigma]
  calc
    (∑ s, ∑ u, ∑ t, ∑ v, lapse * spinGate s t * complexPrice (internalEntry a u v)) =
        ∑ s, ∑ t, lapse * spinGate s t *
          (∑ u, ∑ v, complexPrice (internalEntry a u v)) := by
      conv_lhs => arg 2; ext s; rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ s, ∑ t, lapse * spinGate s t * 3 := by rw [original_internal_price]
    _ = 6 * lapse := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, spinGate_sum]
      ring

theorem original_scalar_basis_card : Fintype.card ScalarBasisIndex = 35 := by
  rw [← Module.finrank_eq_card_basis (su7ExteriorBasis 4), su7ExteriorPower_finrank]
  norm_num [Nat.choose]

theorem original_sourceTensorPrice : sourceTensorPrice = 210 * lapse := by
  unfold sourceTensorPrice
  simp_rw [original_scalar_tensor_price]
  simp only [Finset.sum_const, Finset.card_univ, original_scalar_basis_card, nsmul_eq_mul]
  ring

theorem original_lapse_rational_enclosure : lapse ≤ 2 / 3 := by
  have hp := Stage9C.Material.SpinPair.lapse_pos
  have hs := Stage9C.Material.SpinPair.lapse_sq
  change lapse ^ 2 = 54 / 125 at hs
  nlinarith

theorem original_sourceTensorPrice_rational_enclosure : sourceTensorPrice ≤ 140 := by
  rw [original_sourceTensorPrice]
  nlinarith [original_lapse_rational_enclosure]

theorem original_fullY_B_rational_enclosure : GaussYukawaCoefficient.bound ≤ 1680 :=
  original_fullY_B_finite_price.trans (by nlinarith [original_sourceTensorPrice_rational_enclosure])

theorem actual_fullY_numerical_binary_error (epsilon : ℝ) (precision : 0 < epsilon) (bits : ℕ) :
    ‖ActualQuantitativePreparedFrameOwn.actualFullY epsilon precision -
      FullYSourceCutoffVolterra.cutoff (916 * bits)
        (ActualQuantitativePreparedFrameOwn.actualPrepared epsilon precision)‖ ≤
      1538880 * (1 / 2 : ℝ) ^ bits := by
  exact (actual_fullY_finite_coefficient_binary_error epsilon precision bits).trans
    (by
      have h := mul_le_mul_of_nonneg_right original_sourceTensorPrice_rational_enclosure
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) bits)
      nlinarith [h])

end LowEnergy.ActualSourceTensorPriceEnvelopeOwn
