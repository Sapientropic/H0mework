import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Positive

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def quartet (i k j l : Basis) (z : Point × Point) : ℝ :=
  normalizedOrbital i z.1 * normalizedOrbital k z.1 *
    (normalizedOrbital j z.2 * normalizedOrbital l z.2) * kernel (z.2-z.1)

def hartreeIntegrand (z : Point × Point) : ℂ :=
  ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
    (2 * projector24 i k * projector24 j l) * (quartet i k j l z : ℂ)

def exchangeIntegrand (z : Point × Point) : ℂ :=
  ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
    (projector24 i l * projector24 j k) * (quartet i k j l z : ℂ)

private theorem factor_direct (A B : Basis → Basis → ℂ) :
    (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis, A i k * B j l) =
      (∑ i : Basis, ∑ k : Basis, A i k) *
        (∑ j : Basis, ∑ l : Basis, B j l) := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]

private theorem factor_exchange (A B : Basis → Basis → ℂ) :
    (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis, A i l * B j k) =
      (∑ i : Basis, ∑ l : Basis, A i l) *
        (∑ j : Basis, ∑ k : Basis, B j k) := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

theorem hartree_integrand_kernel (z : Point × Point) :
    hartreeIntegrand z = 2 * oneBodyKernel z.1 z.1 * oneBodyKernel z.2 z.2 *
      (kernel (z.2-z.1) : ℂ) := by
  let D (i k : Basis) : ℂ := projector24 i k *
    (normalizedOrbital i z.1 : ℂ) * (normalizedOrbital k z.1 : ℂ)
  let D' (j l : Basis) : ℂ := projector24 j l *
    (normalizedOrbital j z.2 : ℂ) * (normalizedOrbital l z.2 : ℂ)
  let κ : ℂ := (kernel (z.2-z.1) : ℂ)
  calc
    hartreeIntegrand z =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        2 * (D i k * D' j l) * κ := by
          unfold hartreeIntegrand
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          dsimp [D,D',κ,quartet]
          push_cast
          ring
    _ = 2 * (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
          D i k * D' j l) * κ := by
          simp only [Finset.mul_sum,Finset.sum_mul]
    _ = 2 * ((∑ i : Basis, ∑ k : Basis, D i k) *
        (∑ j : Basis, ∑ l : Basis, D' j l)) * κ := by rw [factor_direct]
    _ = _ := by dsimp [D,D',κ,oneBodyKernel]; ring

theorem exchange_integrand_kernel (z : Point × Point) :
    exchangeIntegrand z = oneBodyKernel z.1 z.2 * oneBodyKernel z.2 z.1 *
      (kernel (z.2-z.1) : ℂ) := by
  let X (i l : Basis) : ℂ := projector24 i l *
    (normalizedOrbital i z.1 : ℂ) * (normalizedOrbital l z.2 : ℂ)
  let Y (j k : Basis) : ℂ := projector24 j k *
    (normalizedOrbital j z.2 : ℂ) * (normalizedOrbital k z.1 : ℂ)
  let κ : ℂ := (kernel (z.2-z.1) : ℂ)
  calc
    exchangeIntegrand z =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        (X i l * Y j k) * κ := by
          unfold exchangeIntegrand
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          dsimp [X,Y,κ,quartet]
          push_cast
          ring
    _ = (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
          X i l * Y j k) * κ := by
          simp only [Finset.sum_mul]
    _ = ((∑ i : Basis, ∑ l : Basis, X i l) *
        (∑ j : Basis, ∑ k : Basis, Y j k)) * κ := by rw [factor_exchange]
    _ = _ := by dsimp [X,Y,κ,oneBodyKernel]

def realHartreeIntegrand (z : Point × Point) : ℝ :=
  2 * ‖occupiedVector z.1‖^2 * ‖occupiedVector z.2‖^2 * kernel (z.2-z.1)

def realExchangeIntegrand (z : Point × Point) : ℝ :=
  ‖inner ℂ (occupiedVector z.2) (occupiedVector z.1)‖^2 * kernel (z.2-z.1)

theorem hartree_integrand_real (z : Point × Point) :
    hartreeIntegrand z = (realHartreeIntegrand z : ℂ) := by
  rw [hartree_integrand_kernel,kernel_inner,kernel_inner]
  let v := occupiedVector z.1
  let w := occupiedVector z.2
  have hv : inner ℂ v v = (‖v‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K v
  have hw : inner ℂ w w = (‖w‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K w
  rw [hv,hw]
  change 2 * (‖v‖ : ℂ)^2 * (‖w‖ : ℂ)^2 * (kernel (z.2-z.1) : ℂ) =
    ((2 * ‖v‖^2 * ‖w‖^2 * kernel (z.2-z.1) : ℝ) : ℂ)
  push_cast
  ring

theorem exchange_integrand_real (z : Point × Point) :
    exchangeIntegrand z = (realExchangeIntegrand z : ℂ) := by
  rw [exchange_integrand_kernel,kernel_inner,kernel_inner]
  let v := occupiedVector z.1
  let w := occupiedVector z.2
  have hxy : inner ℂ v w = star (inner ℂ w v) := (inner_conj_symm v w).symm
  rw [hxy]
  have hs : inner ℂ w v * star (inner ℂ w v) =
      (‖inner ℂ w v‖^2 : ℂ) := by
    simpa using Complex.mul_conj' (inner ℂ w v)
  change inner ℂ w v * star (inner ℂ w v) * (kernel (z.2-z.1) : ℂ) =
    ((‖inner ℂ w v‖^2 * kernel (z.2-z.1) : ℝ) : ℂ)
  rw [hs]
  push_cast
  ring

theorem hartree_integrand_nonnegative (z : Point × Point) :
    0 ≤ realHartreeIntegrand z := by
  unfold realHartreeIntegrand
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (sq_nonneg _)) (kernel_nonnegative _)

theorem exchange_integrand_nonnegative (z : Point × Point) :
    0 ≤ realExchangeIntegrand z :=
  mul_nonneg (sq_nonneg _) (kernel_nonnegative _)

theorem exchange_integrand_bounded (z : Point × Point) :
    2 * realExchangeIntegrand z ≤ realHartreeIntegrand z := by
  let v := occupiedVector z.1
  let w := occupiedVector z.2
  have cauchy : ‖inner ℂ w v‖ ≤ ‖w‖ * ‖v‖ := norm_inner_le_norm w v
  have cauchySq : ‖inner ℂ w v‖^2 ≤ (‖w‖ * ‖v‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) cauchy 2
  have hdiff : 0 ≤ ‖v‖^2 * ‖w‖^2 - ‖inner ℂ w v‖^2 := by nlinarith
  have hm := mul_nonneg hdiff (kernel_nonnegative (z.2-z.1))
  dsimp [realHartreeIntegrand,realExchangeIntegrand]
  nlinarith


end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
