import H0mework.Physics.SpinPair.Current
import H0mework.Physics.GaugeAction.P286GaugeAuxiliaryVariation

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineP286GaugeAuxiliaryVariation SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

def sourceColorRaw : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0,Complex.I/2,0;Complex.I/2,0,0;0,0,0],
    !![0,1/2,0;-1/2,0,0;0,0,0],
    !![Complex.I/2,0,0;0,-Complex.I/2,0;0,0,0]]

theorem sourceColorP286Generator_color (direction : Fin 3) :
    (sourceColorP286Generator direction).1.val = sourceColorRaw direction := by
  ext row column
  fin_cases direction <;> fin_cases row <;> fin_cases column <;>
    norm_num [sourceColorP286Generator, sourceColorRaw, p286LieBracket, suLieBracket,
      colorCartanGenerator, colorCartanRaw, colorMixingGenerator, colorMixingRaw,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem sourceColorP286Generator_weak_zero (direction : Fin 3) :
    (sourceColorP286Generator direction).2.1 = 0 := by
  fin_cases direction <;> simp [sourceColorP286Generator, p286LieBracket, suLieBracket]

theorem sourceColorP286Generator_hypercharge_zero (direction : Fin 3) :
    (sourceColorP286Generator direction).2.2 = 0 := by
  fin_cases direction <;> simp [sourceColorP286Generator, p286LieBracket]

theorem sourceColorP286Generator_bracket (first second : Fin 3) :
    p286LieBracket (sourceColorP286Generator first) (sourceColorP286Generator second) =
      (!![0, -sourceColorP286Generator 2, sourceColorP286Generator 1;
          sourceColorP286Generator 2, 0, -sourceColorP286Generator 0;
          -sourceColorP286Generator 1, sourceColorP286Generator 0, 0] :
        Matrix (Fin 3) (Fin 3) P286LieBlockData) first second := by
  fin_cases first <;> fin_cases second
  all_goals
    apply Prod.ext
    · apply Subtype.ext
      ext row column
      simp only [p286LieBracket, suLieBracket]
      simp_rw [sourceColorP286Generator_color]
      fin_cases row <;> fin_cases column <;>
        norm_num [sourceColorP286Generator_color, sourceColorRaw, Matrix.mul_apply, Fin.sum_univ_three]
      all_goals ring_nf
      all_goals simp [Complex.I_sq]
      all_goals ring
    · apply Prod.ext <;>
        simp [p286LieBracket, sourceColorP286Generator_weak_zero,
          sourceColorP286Generator_hypercharge_zero, suLieBracket]

theorem sourceColorP286Generator_pairing
    (direction : Fin 3) (data : P286LieBlockData) :
    p286LiePairing (sourceColorP286Generator direction) data =
      (![(-Complex.I/2 * (data.1.val 0 1 + data.1.val 1 0)).re,
          ((data.1.val 0 1 - data.1.val 1 0)/2).re,
          (-Complex.I/2 * (data.1.val 0 0 - data.1.val 1 1)).re] : Fin 3 → ℝ) direction := by
  unfold p286LiePairing specialUnitaryLiePairing hyperchargeLiePairing
  rw [sourceColorP286Generator_color, sourceColorP286Generator_weak_zero,
    sourceColorP286Generator_hypercharge_zero]
  fin_cases direction <;>
    simp [sourceColorRaw, Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Complex.mul_re] <;> ring

theorem sourceColorP286Generator_pairing_self (direction : Fin 3) :
    p286LiePairing (sourceColorP286Generator direction) (sourceColorP286Generator direction) = 1 / 2 := by
  rw [sourceColorP286Generator_pairing, sourceColorP286Generator_color]
  fin_cases direction <;> norm_num [sourceColorRaw]

theorem spinPairCurrentComplex_spatial_pairing
    (direction : Fin 3) (data : P286LieBlockData) (p q u v : ℂ) (density : ℝ)
    (product : p*v+q*u = (density : ℂ)) :
    (spinPairCurrentComplex direction.succ data p q u v).re =
      2 * density * p286LiePairing (sourceColorP286Generator direction) data := by
  rw [spinPairCurrentComplex_full, sourceColorP286Generator_pairing]
  fin_cases direction <;>
    simp only [product, Fin.succ_mk]
  all_goals
    simp [Complex.mul_re, Complex.mul_im]
    ring

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
