import H0mework.Arithmetic.PrimeShadow.P322

/-!
# Proposition 323: half-sigma self-duality does not collapse addition and multiplication

P322 formalized the honest part of the Euler-product intuition: the prime
index is shared by the half-sigma atomic support and the analytic Euler
product, and the unconstrained product carrier is not enough.

This file records the next boundary.  The half-sigma point is self-dual under
the complement involution `r ↦ 1-r`, but self-duality is not a quotient that
identifies the serial `satOr` additive face with the nested-iteration
multiplicative face.

On the nondegenerate carrier, including `σ = 1/2`, those faces are faithful:
`satOr` reflects exponent addition and nested iteration reflects exponent
multiplication.  Therefore `2+3 ≠ 2*3` gives a concrete half-sigma witness that
addition and multiplication have not collapsed.  Consequently FTA still
transfers only to the multiplicative/nested face; any transfer to Goldbach is
exactly a Goldbach-strength additive bridge.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

/-! ## The true half-sigma self-duality -/

/-- THEOREM 1: `σ = 1/2` is fixed by the complement involution. -/
theorem halfSigma_complement_fixed :
    complement (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
  norm_num [complement]

/-! ## The false collapse: addition is not multiplication at half-sigma -/

/-- THEOREM 2: even at the self-dual point `σ=1/2`, serial noisy-OR addition
and nested-iteration multiplication do not identify.  The witness is the
exponent equation `2+3 ≠ 2*3`. -/
theorem halfSigma_add_mul_face_not_collapsed :
    satOrField
        (iteratedRate (1 / 2 : ℝ) 2)
        (iteratedRate (1 / 2 : ℝ) 3) ≠
      iteratedRate (iteratedRate (1 / 2 : ℝ) 2) 3 := by
  intro h
  have hnat :
      (2 : ℕ) + 3 = 2 * 3 :=
    (satOr_eq_nested_iteratedRate_iff_add_eq_mul_of_mem_Ioo
      (K := ℝ) halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2
      (a := 2) (b := 3) (c := 2) (d := 3)).mp h
  norm_num at hnat

/-- THEOREM 3: the image-level additive and multiplicative operations are
not the same operation at the half-sigma self-dual point. -/
theorem halfSigma_image_add_ne_mul :
    SigmaExponentImage.add
        (SigmaExponentImage.ofNat (1 / 2 : ℝ) 2)
        (SigmaExponentImage.ofNat (1 / 2 : ℝ) 3) ≠
      SigmaExponentImage.mul
        (SigmaExponentImage.ofNat (1 / 2 : ℝ) 2)
        (SigmaExponentImage.ofNat (1 / 2 : ℝ) 3) := by
  intro h
  have hnat :
      (2 : ℕ) + 3 = 2 * 3 :=
    (SigmaExponentImage.add_eq_ofNat_iff_add_eq_of_mem_Ioo
      (K := ℝ) halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2
      (n := 2) (m := 3) (k := 2 * 3)).mp ?_
  · norm_num at hnat
  · calc
      SigmaExponentImage.add
          (SigmaExponentImage.ofNat (1 / 2 : ℝ) 2)
          (SigmaExponentImage.ofNat (1 / 2 : ℝ) 3) =
          SigmaExponentImage.mul
            (SigmaExponentImage.ofNat (1 / 2 : ℝ) 2)
            (SigmaExponentImage.ofNat (1 / 2 : ℝ) 3) := h
      _ = SigmaExponentImage.ofNat (1 / 2 : ℝ) (2 * 3) :=
        SigmaExponentImage.mul_ofNat_of_mem_Ioo
          halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 2 3

/-! ## FTA remains a multiplicative bridge, not automatic Goldbach -/

/-- THEOREM 4: at `σ=1/2`, a proposed transfer from FTA to sigma-Goldbach is
still exactly a proposed transfer from FTA to ordinary Goldbach.  The
self-dual point gives no free additive-prime decomposition. -/
theorem halfSigma_fta_to_sigmaGoldbach_iff_fta_to_goldbach :
    (PrimeMultiplicativeFactorizationStatement →
        SigmaEvenGoldbachStatement (1 / 2 : ℝ)) ↔
      (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachStatement) :=
  fta_to_sigmaGoldbach_iff_fta_to_goldbach_of_mem_Ioo
    halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2

/-- THEOREM 5: even with an FTA-shaped certificate in hand, proving the
half-sigma carrier Goldbach transfer is equivalent to proving ordinary
Goldbach. -/
theorem halfSigma_fta_bridge_reduces_to_goldbach
    (hfta : PrimeMultiplicativeFactorizationStatement) :
    (PrimeMultiplicativeFactorizationStatement →
        SigmaEvenGoldbachStatement (1 / 2 : ℝ)) ↔
      EvenGoldbachStatement :=
  fta_bridge_reduces_to_goldbach_of_mem_Ioo
    halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 hfta

/-- A compact boundary certificate for the half-sigma self-dual point. -/
structure HalfSigmaSelfDualArithmeticBoundaryCertificate where
  self_dual :
    complement (1 / 2 : ℝ) = (1 / 2 : ℝ)
  add_mul_face_not_collapsed :
    satOrField
        (iteratedRate (1 / 2 : ℝ) 2)
        (iteratedRate (1 / 2 : ℝ) 3) ≠
      iteratedRate (iteratedRate (1 / 2 : ℝ) 2) 3
  image_add_ne_mul :
    SigmaExponentImage.add
        (SigmaExponentImage.ofNat (1 / 2 : ℝ) 2)
        (SigmaExponentImage.ofNat (1 / 2 : ℝ) 3) ≠
      SigmaExponentImage.mul
        (SigmaExponentImage.ofNat (1 / 2 : ℝ) 2)
        (SigmaExponentImage.ofNat (1 / 2 : ℝ) 3)
  fta_to_goldbach_boundary :
    (PrimeMultiplicativeFactorizationStatement →
        SigmaEvenGoldbachStatement (1 / 2 : ℝ)) ↔
      (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachStatement)
  euler_product_coupling_seed :
    EulerProductCouplingSeedCertificate

/-- THEOREM 6: the canonical half-sigma boundary certificate. -/
def halfSigmaSelfDualArithmeticBoundaryCertificate :
    HalfSigmaSelfDualArithmeticBoundaryCertificate where
  self_dual := halfSigma_complement_fixed
  add_mul_face_not_collapsed := halfSigma_add_mul_face_not_collapsed
  image_add_ne_mul := halfSigma_image_add_ne_mul
  fta_to_goldbach_boundary :=
    halfSigma_fta_to_sigmaGoldbach_iff_fta_to_goldbach
  euler_product_coupling_seed :=
    eulerProductCouplingSeedCertificate

end AffineRelaxation
end SaturationMonoid
