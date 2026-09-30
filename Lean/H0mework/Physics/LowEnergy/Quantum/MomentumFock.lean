import H0mework.Physics.LowEnergyFermion.Charge

/-! Algebraic consumer for a four-leg kernel with independent momentum labels.
The coefficient can depend on all four labels; no separable-current ansatz is
imposed. Source Green functions supply these coefficients componentwise for
both ordinary kernels and their distributional contact coefficients. -/
set_option autoImplicit false
namespace SourceMomentumFock
open SaturationMonoid.PhysicsCore
open SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def quartic (K : ι → ι → ι → ι → ℂ) : Module.End ℂ (Fock ι) :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    K i j k l • (creation i * creation k * annihilation l * annihilation j)

theorem quartic_factorized (A B : Matrix ι ι ℂ) :
    quartic (fun i j k l => A i j * B k l) = normalProduct A B := rfl

theorem quartic_add (K L : ι → ι → ι → ι → ℂ) :
    quartic (fun i j k l => K i j k l + L i j k l) = quartic K + quartic L := by
  simp only [quartic, add_smul, Finset.sum_add_distrib]

theorem quartic_smul (c : ℂ) (K : ι → ι → ι → ι → ℂ) :
    quartic (fun i j k l => c * K i j k l) = c • quartic K := by
  simp only [quartic, Finset.smul_sum, smul_smul]

theorem quartic_twoParticle (K : ι → ι → ι → ι → ℂ) (u v : ι → ℂ) :
    quartic K (twoParticle u v) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (K i j k l * (u j * v l - v j * u l)) •
          creation i (creation k vacuum) := by
  simp only [quartic, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    annihilation_twice, map_smul, smul_smul]

theorem quartic_charge (K : ι → ι → ι → ι → ℂ) (q : ι → ℂ)
    (selection : ∀ i j k l, K i j k l * (q i + q k - q j - q l) = 0) :
    occupationCharge q * quartic K = quartic K * occupationCharge q := by
  simp only [quartic, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [occupationCharge_four_word, smul_add, smul_smul, selection, zero_smul, add_zero]

theorem quartic_number (K : ι → ι → ι → ι → ℂ) :
    occupationCharge (fun _ : ι => 1) * quartic K =
      quartic K * occupationCharge (fun _ : ι => 1) := by
  apply quartic_charge
  intro i j k l
  norm_num

omit [LinearOrder ι] in
private theorem pairing_sum_right {κ : Type*} [Fintype κ]
    (ψ : Fock ι) (family : κ → Fock ι) :
    pairing ψ (∑ k, family k) = ∑ k, pairing ψ (family k) := by
  simp only [pairing, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem created_twoParticle (i k : ι) :
    creation i (creation k (vacuum : Fock ι)) =
      twoParticle (Pi.single i 1) (Pi.single k 1) := by
  simp [twoParticle, waveCreation]

theorem quartic_matrixElement (K : ι → ι → ι → ι → ℂ) (x y u v : ι → ℂ) :
    pairing (twoParticle x y) (quartic K (twoParticle u v)) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        K i j k l * (u j * v l - v j * u l) *
          (star (x i) * star (y k) - star (x k) * star (y i)) := by
  rw [quartic_twoParticle]
  simp only [pairing_sum_right, pairing_smul_right, created_twoParticle, pairing_twoParticle]
  simp [modePair, Pi.single_apply]

end
end SourceMomentumFock
