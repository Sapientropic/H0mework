import H0mework.Physics.LowEnergyScalar.QuaternionSymbol
import H0mework.Physics.SpinPair.Parameters

/-! Determinant in the real source-adapted basis. The exact receipt supplies
the 23-singlet / five-quaternion source intertwiner; this file proves the
momentum-polynomial identity for the resulting block matrix. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.ScalarSymbol
open Stage9C.Material.SpinPair
noncomputable section

def reducedSymbol (singlets blocks : ℕ) (frequencySquared amplitude : ℂ)
    (momentum : Fin 3 → ℂ) :
    Matrix (Fin singlets ⊕ (Fin 4 × Fin blocks)) (Fin singlets ⊕ (Fin 4 × Fin blocks)) ℂ :=
  Matrix.fromBlocks ((frequencySquared-(squareMomentum momentum-2)) • 1) 0 0
    (Matrix.blockDiagonal (fun _ : Fin blocks =>
      blockSymbol (frequencySquared-(squareMomentum momentum+3*amplitude^2/4-2)) amplitude momentum))

theorem reducedSymbol_determinant (singlets blocks : ℕ) (frequencySquared amplitude : ℂ)
    (momentum : Fin 3 → ℂ) :
    (reducedSymbol singlets blocks frequencySquared amplitude momentum).det =
      (frequencySquared-(squareMomentum momentum-2))^singlets*
        ((frequencySquared-(squareMomentum momentum+3*amplitude^2/4-2))^2-
          amplitude^2*squareMomentum momentum)^(2*blocks) := by
  rw [reducedSymbol, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one,
    Matrix.det_blockDiagonal]
  simp only [Fintype.card_fin, mul_one, blockSymbol_determinant, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem source_amplitude_squared : (gaugeScale : ℂ)^2 = 18/25 := by
  have source : gaugeScale^2 = 18/25 := by
    unfold gaugeScale
    rw [div_pow, mul_pow, spinScale_sq]
    norm_num
  rw [← Complex.ofReal_pow, source]
  norm_num

theorem source43_determinant (frequencySquared : ℂ) (momentum : Fin 3 → ℂ) :
    (reducedSymbol 23 5 frequencySquared gaugeScale momentum).det =
      (frequencySquared-(squareMomentum momentum-2))^23*
        ((frequencySquared-(squareMomentum momentum-73/50))^2-
          (18/25)*squareMomentum momentum)^10 := by
  rw [reducedSymbol_determinant, source_amplitude_squared]
  have center : squareMomentum momentum+3*(18/25:ℂ)/4-2 = squareMomentum momentum-73/50 := by ring
  rw [center]

theorem source43_singular_iff (frequencySquared : ℂ) (momentum : Fin 3 → ℂ) :
    (reducedSymbol 23 5 frequencySquared gaugeScale momentum).det = 0 ↔
      frequencySquared = squareMomentum momentum-2 ∨
      (frequencySquared-(squareMomentum momentum-73/50))^2 = (18/25)*squareMomentum momentum := by
  rw [source43_determinant]
  simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    sub_eq_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.ScalarSymbol
