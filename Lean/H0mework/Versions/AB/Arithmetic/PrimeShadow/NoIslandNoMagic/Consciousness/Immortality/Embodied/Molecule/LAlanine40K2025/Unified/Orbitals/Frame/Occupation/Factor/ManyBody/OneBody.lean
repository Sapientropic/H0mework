import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Exterior

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator BigOperators
noncomputable section

private theorem det_updateRow_one (k : Fin 48) (u : Fin 48 → ℂ) :
    ((1 : Matrix (Fin 48) (Fin 48) ℂ).updateRow k u).det = u k := by
  have rowExpansion : (∑ j : Fin 48, (u j) • (1 : Matrix (Fin 48) (Fin 48) ℂ) j) = u := by
    funext i
    simp [Matrix.one_apply]
  calc
    _ = ((1 : Matrix (Fin 48) (Fin 48) ℂ).updateRow k
        (∑ j : Fin 48, (u j) • (1 : Matrix (Fin 48) (Fin 48) ℂ) j)).det := by
          rw [rowExpansion]
    _ = u k := by rw [Matrix.det_updateRow_sum,Matrix.det_one,smul_eq_mul,mul_one]

def basisSpin (x : SpinBasis) : OneBody := Pi.single x 1

def replacedState (k : Fin 48) (x : SpinBasis) : ⋀[ℂ]^48 OneBody :=
  exteriorPower.ιMulti ℂ 48 (Function.update orbitalFamily k (basisSpin x))

theorem dual_replaced (k : Fin 48) (x : SpinBasis) :
    slaterDual (replacedState k x) = dualFamily k (basisSpin x) := by
  change exteriorPower.pairingDual ℂ OneBody 48
    (exteriorPower.ιMulti ℂ 48 dualFamily)
    (exteriorPower.ιMulti ℂ 48 (Function.update orbitalFamily k (basisSpin x))) = _
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  have rowMatrix :
      Matrix.of (fun i j : Fin 48 => dualFamily j
        ((Function.update orbitalFamily k (basisSpin x)) i)) =
        (1 : Matrix (Fin 48) (Fin 48) ℂ).updateRow k
          (fun j => dualFamily j (basisSpin x)) := by
    ext i j
    by_cases same : i = k
    · subst same
      simp [Matrix.updateRow_apply,dualFamily]
    · simp [Matrix.updateRow_apply,Function.update_of_ne,same,orbital_dual_pair,
        dualFamily,orbitalFamily,spinIndex.injective.eq_iff,Matrix.one_apply,eq_comm]
  rw [rowMatrix,det_updateRow_one]

def oneBodyContraction (x y : SpinBasis) : ℂ :=
  ∑ k : Fin 48, orbitalFamily k x * slaterDual (replacedState k y)

theorem one_body_contraction_exact (x y : SpinBasis) :
    oneBodyContraction x y = spinProjector x y := by
  simp only [oneBodyContraction,dual_replaced]
  have dualBasis (s : SpinSlot) : orbitalDual s (basisSpin y) =
      star (spinFactor y s) := by
    simp [orbitalDual,basisSpin,Matrix.conjTranspose_apply]
  simp_rw [orbitalFamily,dualFamily,orbital,dualBasis]
  simp_rw [Matrix.col_apply]
  rw [Equiv.sum_comp spinIndex (fun s : SpinSlot => spinFactor x s * star (spinFactor y s))]
  simp only [spinProjector,Matrix.mul_apply,Matrix.conjTranspose_apply]

def spinSummedContraction : Matrix Basis Basis ℂ :=
  fun i j => ∑ s : Bool, oneBodyContraction (i,s) (j,s)

theorem spin_summed_contraction : spinSummedContraction = spinSummed := by
  ext i j
  simp only [spinSummedContraction,spinSummed,one_body_contraction_exact]

theorem actual_U_one_body_error :
    ‖Occupation.gamma - spinSummedContraction‖ < (1 / 10^5 : ℝ) := by
  rw [spin_summed_contraction]
  exact actual_U_spin_density_error

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
