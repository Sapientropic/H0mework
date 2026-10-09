import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteDiagonal.Literals.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.HeadSource

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped BigOperators
noncomputable section

def firstSixHeadEquiv : Fin 6 ≃ HeadDiagonal where
  toFun a := ⟨firstSixBasis a,by change a.val < 6; exact a.isLt⟩
  invFun h := ⟨h.val.val,h.property⟩
  left_inv a := Fin.ext rfl
  right_inv h := Subtype.ext (Fin.ext rfl)

def headDiagonalStagedQ : ℚ :=
  ∑ a : HeadDiagonal, sourceDiagonalGainIntQ a.val (head_diagonal_not_donor a)

theorem head_diagonal_staged_q_exact :
    headDiagonalStagedQ = (844046232124989572657219 : ℚ)/(scale : ℚ) := by
  unfold headDiagonalStagedQ
  rw [← (firstSixHeadEquiv.sum_comp
    (fun h : HeadDiagonal => sourceDiagonalGainIntQ h.val (head_diagonal_not_donor h)))]
  calc
    (∑ a : Fin 6, sourceDiagonalGainIntQ (firstSixHeadEquiv a).val
      (head_diagonal_not_donor (firstSixHeadEquiv a))) =
        ∑ a : Fin 6, (firstSixDiagonalGainNumeratorInt a : ℚ)/(scale : ℚ) := by
      apply Finset.sum_congr rfl
      intro a _
      change sourceDiagonalGainIntQ (firstSixBasis a) (first_six_different a) = _
      unfold sourceDiagonalGainIntQ
      rw [← first_six_diagonal_gain_original a]
    _ = ((∑ a : Fin 6, firstSixDiagonalGainNumeratorInt a : ℤ) : ℚ)/(scale : ℚ) := by
      rw [Int.cast_sum, Finset.sum_div]
    _ = _ := by rw [first_six_diagonal_integer_sum]; norm_num

theorem head_diagonal_staged_exact :
    headDiagonalStagedGain = (844046232124989572657219 : ℝ)/10^30 := by
  have castQ : headDiagonalStagedGain = (headDiagonalStagedQ : ℝ) := by
    unfold headDiagonalStagedGain headDiagonalStagedQ
    rw [Rat.cast_sum]
  rw [castQ,head_diagonal_staged_q_exact]
  norm_num [scale]

theorem head_diagonal_original_lower :
    (844046232124989572657219 : ℝ)/10^30 - 1/10^12 <
      headDiagonalOriginalGain := by
  have error := head_diagonal_gain_error_lt
  rw [head_diagonal_staged_exact] at error
  nlinarith [abs_lt.mp error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
