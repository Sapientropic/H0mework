import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Matrix

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped Matrix BigOperators

private theorem gram_product (r s u v : Int) :
    star (((r : ℂ) + Complex.I * (s : ℂ)) / (factorScale : ℂ)) *
      (((u : ℂ) + Complex.I * (v : ℂ)) / (factorScale : ℂ)) =
    (((r*u+s*v : Int) : ℂ) + Complex.I * ((r*v-s*u : Int) : ℂ)) /
      (factorScale : ℂ)^2 := by
  have scale_ne : (factorScale : ℂ) ≠ 0 := by norm_num [factorScale]
  simp [factorScale,Complex.conj_I]
  field_simp
  linear_combination -((s : ℂ) * (v : ℂ)) * Complex.I_sq

private theorem gram_product_at (i : Basis) (a b : OccupiedSlot) :
    star (factor i a) * factor i b =
      (((realNumerator i a * realNumerator i b + imagNumerator i a * imagNumerator i b : Int) : ℂ) +
        Complex.I * ((realNumerator i a * imagNumerator i b -
          imagNumerator i a * realNumerator i b : Int) : ℂ)) / (factorScale : ℂ)^2 := by
  exact gram_product _ _ _ _

private theorem gamma_product (r s u v : Int) :
    (((r : ℂ) + Complex.I * (s : ℂ)) / (factorScale : ℂ)) *
      star (((u : ℂ) + Complex.I * (v : ℂ)) / (factorScale : ℂ)) =
    (((r*u+s*v : Int) : ℂ) + Complex.I * ((s*u-r*v : Int) : ℂ)) /
      (factorScale : ℂ)^2 := by
  have scale_ne : (factorScale : ℂ) ≠ 0 := by norm_num [factorScale]
  simp [factorScale,Complex.conj_I]
  field_simp
  linear_combination -((s : ℂ) * (v : ℂ)) * Complex.I_sq

private theorem gamma_product_at (i j : Basis) (a : OccupiedSlot) :
    factor i a * star (factor j a) =
      (((realNumerator i a * realNumerator j a +
        imagNumerator i a * imagNumerator j a : Int) : ℂ) +
        Complex.I * ((imagNumerator i a * realNumerator j a -
          realNumerator i a * imagNumerator j a : Int) : ℂ)) /
        (factorScale : ℂ)^2 := by
  exact gamma_product _ _ _ _

theorem gram_entry (a b : OccupiedSlot) :
    (gram - 1) a b =
      ((gramRealError a b : ℂ) + Complex.I * (gramImagError a b : ℂ)) /
        (factorScale : ℂ)^2 := by
  let realSum : Int := ∑ i : Basis,
    (realNumerator i a * realNumerator i b + imagNumerator i a * imagNumerator i b)
  let imagSum : Int := ∑ i : Basis,
    (realNumerator i a * imagNumerator i b - imagNumerator i a * realNumerator i b)
  have products : gram a b =
      ((realSum : ℂ) + Complex.I * (imagSum : ℂ)) / (factorScale : ℂ)^2 := by
    change (∑ i : Basis, star (factor i a) * factor i b) = _
    simp_rw [gram_product_at]
    rw [← Finset.sum_div]
    simp [realSum,imagSum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [Matrix.sub_apply,products]
  simp [gramRealError,gramImagError,realSum,imagSum,Matrix.one_apply]
  have scale_ne : (factorScale : ℂ) ≠ 0 := by norm_num [factorScale]
  by_cases same : a = b
  · simp [same]
    field_simp [scale_ne]
    ring
  · simp [same]

theorem gamma_entry (i j : Basis) :
    (rawGamma - candidateGamma) i j =
      ((gammaRealError i j : ℂ) + Complex.I * (gammaImagError i j : ℂ)) /
        ((gammaScale : ℂ) * (factorScale : ℂ)^2) := by
  let realSum : Int := ∑ a : OccupiedSlot,
    (realNumerator i a * realNumerator j a + imagNumerator i a * imagNumerator j a)
  let imagSum : Int := ∑ a : OccupiedSlot,
    (imagNumerator i a * realNumerator j a - realNumerator i a * imagNumerator j a)
  have products : (factor * factor.conjTranspose) i j =
      ((realSum : ℂ) + Complex.I * (imagSum : ℂ)) / (factorScale : ℂ)^2 := by
    change (∑ a : OccupiedSlot, factor i a * star (factor j a)) = _
    simp_rw [gamma_product_at]
    rw [← Finset.sum_div]
    simp [realSum,imagSum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [Matrix.sub_apply,raw_gamma_entry]
  change _ - (2 : ℂ) * (factor * factor.conjTranspose) i j = _
  rw [products]
  simp [gammaRealError,gammaImagError,realSum,imagSum]
  have factor_ne : (factorScale : ℂ) ≠ 0 := by norm_num [factorScale]
  have gamma_ne : (gammaScale : ℂ) ≠ 0 := by norm_num [gammaScale]
  field_simp [factor_ne,gamma_ne]
  ring

end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
