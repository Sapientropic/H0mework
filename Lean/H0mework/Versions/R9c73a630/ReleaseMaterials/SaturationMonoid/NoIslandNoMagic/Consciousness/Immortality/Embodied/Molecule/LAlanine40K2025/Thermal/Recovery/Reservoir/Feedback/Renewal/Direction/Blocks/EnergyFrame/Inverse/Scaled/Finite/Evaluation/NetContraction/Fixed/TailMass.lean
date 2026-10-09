import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped BigOperators

def tailIndices : Finset Basis := Finset.univ.filter (fun i => 6 ≤ i.val)
def tailSystemQ : ℚ := ∑ i ∈ tailIndices, (systemQ i i).1
def tailBathQ : ℚ := ∑ i ∈ tailIndices, (bathQ i i).1
def tailSystemZ : Scalar.QComplex := ∑ i ∈ tailIndices, systemQ i i
def tailBathZ : Scalar.QComplex := ∑ i ∈ tailIndices, bathQ i i
def tailPairZ : Scalar.QComplex := ∑ i ∈ tailIndices, ∑ j ∈ tailIndices, pairQ (i,j) (i,j)
def tailPairQ : ℚ := tailPairZ.1

theorem original_tail_system_bound : tailSystemQ < 76/100 := by decide +kernel
theorem original_tail_bath_bound : tailBathQ < 23/10^8 := by decide +kernel
theorem original_tail_system_lower : 74/100 < tailSystemQ := by decide +kernel
theorem original_tail_bath_lower : 22/10^8 < tailBathQ := by decide +kernel

private theorem square_pair_sum (U V : Matrix Basis Basis ℂ) (c s : ℂ) (F : Finset Basis) :
    (Finset.sum F (fun a => Finset.sum F (fun b =>
      c^2*U a a*V b b+s^2*V a a*U b b+
        Complex.I*c*s*(U a b*V b a-U b a*V a b)))) =
      (c^2+s^2)*(Finset.sum F (fun a => U a a))*(Finset.sum F (fun b => V b b)) := by
  have swap : (Finset.sum F (fun a => Finset.sum F (fun b => U a b*V b a)))=
      (Finset.sum F (fun a => Finset.sum F (fun b => U b a*V a b))) := by
    rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,← Finset.sum_mul]
  rw [swap]
  ring

private theorem pairQ_diagonal_expansion (a b : Basis) :
    Scalar.value (pairQ (a,b) (a,b)) =
      (couplingCosineQ : ℂ)^2*Scalar.value (systemQ a a)*Scalar.value (bathQ b b)+
      (couplingSineQ : ℂ)^2*Scalar.value (bathQ a a)*Scalar.value (systemQ b b)+
      Complex.I*(couplingCosineQ : ℂ)*(couplingSineQ : ℂ)*
        (Scalar.value (systemQ a b)*Scalar.value (bathQ b a)-
          Scalar.value (systemQ b a)*Scalar.value (bathQ a b)) := by
  simp only [pairQ,Scalar.value_add,Scalar.value_smul,Scalar.value_multiply,scalar_value_sub,
    Rat.cast_pow]
  simp only [Scalar.value]
  push_cast
  ring_nf

theorem tail_pair_complex : Scalar.value tailPairZ =
    ((couplingCosineQ : ℂ)^2+(couplingSineQ : ℂ)^2)*
      Scalar.value tailSystemZ*Scalar.value tailBathZ := by
  simp only [tailPairZ,tailSystemZ,tailBathZ,value_sum]
  simp_rw [pairQ_diagonal_expansion]
  exact square_pair_sum (qvalue systemQ) (qvalue bathQ)
    (couplingCosineQ : ℂ) (couplingSineQ : ℂ) tailIndices

theorem tail_pair_qcomplex : tailPairZ =
    Scalar.multiply (couplingCosineQ^2+couplingSineQ^2,0)
      (Scalar.multiply tailSystemZ tailBathZ) := by
  apply LoadPrimitive.scalar_value_injective
  rw [Scalar.value_multiply,Scalar.value_multiply]
  simpa [Scalar.value,mul_assoc] using tail_pair_complex

theorem tail_pair_rational : tailPairQ =
    (couplingCosineQ^2+couplingSineQ^2)*
      (tailSystemZ.1*tailBathZ.1-tailSystemZ.2*tailBathZ.2) := by
  have h := congrArg Prod.fst tail_pair_qcomplex
  simpa only [tailPairQ,Scalar.multiply,zero_mul,sub_zero] using h

theorem tail_system_real : tailSystemZ.1=tailSystemQ := by
  simp only [tailSystemZ,tailSystemQ,Prod.fst_sum]

theorem tail_bath_real : tailBathZ.1=tailBathQ := by
  simp only [tailBathZ,tailBathQ,Prod.fst_sum]

theorem tail_bath_imag_zero : tailBathZ.2=0 := by decide +kernel

theorem coupling_square_positive : 0 ≤ couplingCosineQ^2+couplingSineQ^2 := by positivity
theorem coupling_square_bound : couplingCosineQ^2+couplingSineQ^2 < 11/10 := by decide +kernel
theorem coupling_square_lower : 99/100 < couplingCosineQ^2+couplingSineQ^2 := by decide +kernel

theorem tail_pair_mass_exact : tailPairQ=
    (couplingCosineQ^2+couplingSineQ^2)*tailSystemQ*tailBathQ := by
  rw [tail_pair_rational,tail_system_real,tail_bath_real,tail_bath_imag_zero]
  ring

theorem original_tail_pair_nonnegative : 0 ≤ tailPairQ := by
  rw [tail_pair_mass_exact]
  exact mul_nonneg (mul_nonneg coupling_square_positive (by decide +kernel)) (by decide +kernel)

theorem original_tail_pair_nonzero : (1/10^7 : ℚ) < tailPairQ := by
  rw [tail_pair_mass_exact]
  have cpos : (0 : ℚ) < couplingCosineQ^2+couplingSineQ^2 :=
    lt_trans (by norm_num : (0 : ℚ) < 99/100) coupling_square_lower
  have spos : (0 : ℚ) < tailSystemQ :=
    lt_trans (by norm_num : (0 : ℚ) < 74/100) original_tail_system_lower
  have first : (99/100 : ℚ)*(74/100) <
      (couplingCosineQ^2+couplingSineQ^2)*tailSystemQ := by
    calc
      _ < (couplingCosineQ^2+couplingSineQ^2)*(74/100) :=
        mul_lt_mul_of_pos_right coupling_square_lower (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left original_tail_system_lower cpos
  have second : (99/100 : ℚ)*(74/100)*(22/10^8) <
      (couplingCosineQ^2+couplingSineQ^2)*tailSystemQ*tailBathQ := by
    calc
      _ < (couplingCosineQ^2+couplingSineQ^2)*tailSystemQ*(22/10^8) :=
        mul_lt_mul_of_pos_right first (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left original_tail_bath_lower (mul_pos cpos spos)
  exact lt_trans (by norm_num : (1/10^7 : ℚ) < (99/100)*(74/100)*(22/10^8)) second

theorem original_tail_pair_bound : tailPairQ < 2/10^7 := by
  rw [tail_pair_mass_exact]
  have bathPositive : 0 ≤ tailBathQ := by decide +kernel
  have systemPositive : 0 ≤ tailSystemQ := by decide +kernel
  have h := mul_le_mul_of_nonneg_right (le_of_lt original_tail_system_bound) bathPositive
  have j := mul_le_mul_of_nonneg_left (le_of_lt original_tail_bath_bound)
    (by norm_num : (0 : ℚ) ≤ 76/100)
  have f := mul_le_mul_of_nonneg_right (le_of_lt coupling_square_bound)
    (mul_nonneg systemPositive bathPositive)
  nlinarith [mul_nonneg coupling_square_positive (mul_nonneg systemPositive bathPositive)]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
