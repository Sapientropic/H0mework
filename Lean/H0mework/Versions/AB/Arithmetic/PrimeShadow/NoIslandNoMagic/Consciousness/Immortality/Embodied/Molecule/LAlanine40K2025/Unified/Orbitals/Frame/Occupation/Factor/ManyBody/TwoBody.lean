import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.TwoRow

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open scoped Matrix BigOperators
noncomputable section

def doublyReplacedState (k l : Fin 48) (x y : SpinBasis) : ⋀[ℂ]^48 OneBody :=
  exteriorPower.ιMulti ℂ 48
    (Function.update (Function.update orbitalFamily k (basisSpin x)) l (basisSpin y))

theorem dual_double_replaced (k l : Fin 48) (different : k ≠ l)
    (x y : SpinBasis) :
    slaterDual (doublyReplacedState k l x y) =
      dualFamily k (basisSpin x) * dualFamily l (basisSpin y) -
        dualFamily l (basisSpin x) * dualFamily k (basisSpin y) := by
  change exteriorPower.pairingDual ℂ OneBody 48
    (exteriorPower.ιMulti ℂ 48 dualFamily)
    (exteriorPower.ιMulti ℂ 48
      (Function.update (Function.update orbitalFamily k (basisSpin x)) l (basisSpin y))) = _
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  have rowMatrix :
      Matrix.of (fun i j : Fin 48 => dualFamily j
        ((Function.update (Function.update orbitalFamily k (basisSpin x)) l (basisSpin y)) i)) =
        (((1 : Matrix (Fin 48) (Fin 48) ℂ).updateRow k
          (fun j => dualFamily j (basisSpin x))).updateRow l
          (fun j => dualFamily j (basisSpin y))) := by
    ext i j
    by_cases ik : i = k
    · subst i
      simp [Matrix.updateRow_apply,different]
    · by_cases il : i = l
      · subst i
        simp [Matrix.updateRow_apply]
      · simp [Matrix.updateRow_apply,ik,il,
          Matrix.one_apply,dualFamily,orbitalFamily,orbital_dual_pair,
          spinIndex.injective.eq_iff,eq_comm]
  rw [rowMatrix,det_double_update_one k l different]

def twoBodyContraction (x₁ x₂ y₁ y₂ : SpinBasis) : ℂ :=
  ∑ k : Fin 48, ∑ l : Fin 48,
    if k = l then 0 else
      orbitalFamily k x₁ * orbitalFamily l x₂ *
        slaterDual (doublyReplacedState k l y₁ y₂)

private theorem wick_sum {ι : Type*} [Fintype ι]
    (A B U V : ι → ℂ) :
    (∑ k : ι, ∑ l : ι,
      A k * B l * (U k * V l - U l * V k)) =
      (∑ k : ι, A k * U k) * (∑ l : ι, B l * V l) -
        (∑ k : ι, A k * V k) * (∑ l : ι, B l * U l) := by
  calc
    _ = ∑ k : ι, ∑ l : ι,
          ((A k * U k) * (B l * V l) - (A k * V k) * (B l * U l)) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib]
      rw [Finset.sum_mul_sum,Finset.sum_mul_sum]

theorem two_body_wick (x₁ x₂ y₁ y₂ : SpinBasis) :
    twoBodyContraction x₁ x₂ y₁ y₂ =
      oneBodyContraction x₁ y₁ * oneBodyContraction x₂ y₂ -
        oneBodyContraction x₁ y₂ * oneBodyContraction x₂ y₁ := by
  have expansion : twoBodyContraction x₁ x₂ y₁ y₂ =
      ∑ k : Fin 48, ∑ l : Fin 48,
        orbitalFamily k x₁ * orbitalFamily l x₂ *
          (dualFamily k (basisSpin y₁) * dualFamily l (basisSpin y₂) -
            dualFamily l (basisSpin y₁) * dualFamily k (basisSpin y₂)) := by
    unfold twoBodyContraction
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases same : k = l
    · subst l
      simp
    · simp only [if_neg same,dual_double_replaced k l same]
  rw [expansion,wick_sum]
  simp only [oneBodyContraction,dual_replaced]

theorem two_body_source_projector (x₁ x₂ y₁ y₂ : SpinBasis) :
    twoBodyContraction x₁ x₂ y₁ y₂ =
      spinProjector x₁ y₁ * spinProjector x₂ y₂ -
        spinProjector x₁ y₂ * spinProjector x₂ y₁ := by
  rw [two_body_wick]
  simp only [one_body_contraction_exact]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
