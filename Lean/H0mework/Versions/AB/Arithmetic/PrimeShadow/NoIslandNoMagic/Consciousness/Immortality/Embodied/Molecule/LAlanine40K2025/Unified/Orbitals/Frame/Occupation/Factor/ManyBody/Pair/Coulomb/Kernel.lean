import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Integral

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel
open scoped Matrix BigOperators InnerProductSpace
noncomputable section
attribute [local irreducible] normalizedFactor

def occupiedValue (a : OccupiedSlot) (x : Point) : ℂ :=
  ∑ i : Basis, normalizedFactor i a * (normalizedOrbital i x : ℂ)

def oneBodyKernel (x y : Point) : ℂ :=
  ∑ i : Basis, ∑ k : Basis,
    projector24 i k * (normalizedOrbital i x : ℂ) * (normalizedOrbital k y : ℂ)

theorem kernel_factor (x y : Point) :
    oneBodyKernel x y =
      ∑ a : OccupiedSlot, occupiedValue a x * star (occupiedValue a y) := by
  simp only [oneBodyKernel,occupiedValue,projector24,Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  let T (a : OccupiedSlot) (i k : Basis) : ℂ :=
    normalizedFactor i a * star (normalizedFactor k a) *
      (normalizedOrbital i x : ℂ) * (normalizedOrbital k y : ℂ)
  have starValue (a : OccupiedSlot) :
      star (∑ k : Basis, normalizedFactor k a * (normalizedOrbital k y : ℂ)) =
        ∑ k : Basis, star (normalizedFactor k a) * (normalizedOrbital k y : ℂ) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [star_mul,mul_comm]
  calc
    (∑ i : Basis, ∑ k : Basis,
      (∑ a : OccupiedSlot, normalizedFactor i a * star (normalizedFactor k a)) *
        (normalizedOrbital i x : ℂ) * (normalizedOrbital k y : ℂ)) =
      ∑ i : Basis, ∑ k : Basis, ∑ a : OccupiedSlot, T a i k := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        simp [T,Finset.sum_mul]
    _ = ∑ a : OccupiedSlot, ∑ i : Basis, ∑ k : Basis, T a i k := by
      calc
        _ = ∑ i : Basis, ∑ a : OccupiedSlot, ∑ k : Basis, T a i k := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ = ∑ a : OccupiedSlot,
        (∑ i : Basis, normalizedFactor i a * (normalizedOrbital i x : ℂ)) *
        star (∑ k : Basis, normalizedFactor k a * (normalizedOrbital k y : ℂ)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [starValue,Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring

private theorem four_sum_factor (A B : Basis → Basis → ℂ) :
    (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
      A i k * B j l) =
      (∑ i : Basis, ∑ k : Basis, A i k) *
        (∑ j : Basis, ∑ l : Basis, B j l) := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]

private theorem four_sum_cross (A B : Basis → Basis → ℂ) :
    (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
      A i l * B j k) =
      (∑ i : Basis, ∑ l : Basis, A i l) *
        (∑ j : Basis, ∑ k : Basis, B j k) := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

private theorem four_sum_const (c : ℂ) (F : Basis → Basis → Basis → Basis → ℂ) :
    (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis, c * F i j k l) =
      c * (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis, F i j k l) := by
  simp only [Finset.mul_sum]

theorem pair_density_kernel (z : Point × Point) :
    pairDensity z =
      (4 : ℂ) * oneBodyKernel z.1 z.1 * oneBodyKernel z.2 z.2 -
        (2 : ℂ) * oneBodyKernel z.1 z.2 * oneBodyKernel z.2 z.1 := by
  let D (i k : Basis) : ℂ := projector24 i k *
    (normalizedOrbital i z.1 : ℂ) * (normalizedOrbital k z.1 : ℂ)
  let D' (j l : Basis) : ℂ := projector24 j l *
    (normalizedOrbital j z.2 : ℂ) * (normalizedOrbital l z.2 : ℂ)
  let X (i l : Basis) : ℂ := projector24 i l *
    (normalizedOrbital i z.1 : ℂ) * (normalizedOrbital l z.2 : ℂ)
  let Y (j k : Basis) : ℂ := projector24 j k *
    (normalizedOrbital j z.2 : ℂ) * (normalizedOrbital k z.1 : ℂ)
  have expanded : pairDensity z =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        (4 * D i k * D' j l - 2 * X i l * Y j k) := by
    unfold pairDensity
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [spin_summed_two_body]
    push_cast
    dsimp [D,D',X,Y]
    ring
  have direct :
      (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        4 * D i k * D' j l) =
        4 * ((∑ i : Basis, ∑ k : Basis, D i k) *
          (∑ j : Basis, ∑ l : Basis, D' j l)) := by
    have step :
        (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
          4 * D i k * D' j l) =
        ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
          4 * (D i k * D' j l) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [step,four_sum_const,four_sum_factor]
  have exchange :
      (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        2 * X i l * Y j k) =
        2 * ((∑ i : Basis, ∑ l : Basis, X i l) *
          (∑ j : Basis, ∑ k : Basis, Y j k)) := by
    have step :
        (∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
          2 * X i l * Y j k) =
        ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
          2 * (X i l * Y j k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [step,four_sum_const,four_sum_cross]
  rw [expanded]
  simp_rw [Finset.sum_sub_distrib]
  rw [direct,exchange]
  change 4 * (oneBodyKernel z.1 z.1 * oneBodyKernel z.2 z.2) -
    2 * (oneBodyKernel z.1 z.2 * oneBodyKernel z.2 z.1) = _
  ring

def occupiedVector (x : Point) : EuclideanSpace ℂ OccupiedSlot :=
  WithLp.toLp 2 (fun a => occupiedValue a x)

theorem kernel_inner (x y : Point) :
    oneBodyKernel x y = inner ℂ (occupiedVector y) (occupiedVector x) := by
  rw [kernel_factor,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [occupiedVector,WithLp.ofLp_toLp,dotProduct,Pi.star_apply]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
