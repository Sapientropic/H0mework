import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.TailMass
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped BigOperators

def totalSystemZ : Scalar.QComplex := ∑ i : Basis, systemQ i i
def totalBathZ : Scalar.QComplex := ∑ i : Basis, bathQ i i
def totalPairZ : Scalar.QComplex := ∑ i : Basis, ∑ j : Basis, pairQ (i,j) (i,j)
def totalSystemQ : ℚ := totalSystemZ.1
def totalBathQ : ℚ := totalBathZ.1
def fullPairMassQ : ℚ := totalPairZ.1

private theorem square_pair_sum_all (U V : Matrix Basis Basis ℂ) (c s : ℂ) :
    (Finset.sum Finset.univ (fun a : Basis => Finset.sum Finset.univ (fun b : Basis =>
      c^2*U a a*V b b+s^2*V a a*U b b+
        Complex.I*c*s*(U a b*V b a-U b a*V a b)))) =
      (c^2+s^2)*(∑ a : Basis, U a a)*(∑ b : Basis, V b b) := by
  have swap : (∑ a : Basis, ∑ b : Basis, U a b*V b a)=
      (∑ a : Basis, ∑ b : Basis, U b a*V a b) := by
    rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,← Finset.sum_mul]
  rw [swap]
  ring

private theorem pairQ_diagonal_expansion_all (a b : Basis) :
    Scalar.value (pairQ (a,b) (a,b)) =
      (couplingCosineQ : ℂ)^2*Scalar.value (systemQ a a)*Scalar.value (bathQ b b)+
      (couplingSineQ : ℂ)^2*Scalar.value (bathQ a a)*Scalar.value (systemQ b b)+
      Complex.I*(couplingCosineQ : ℂ)*(couplingSineQ : ℂ)*
        (Scalar.value (systemQ a b)*Scalar.value (bathQ b a)-
          Scalar.value (systemQ b a)*Scalar.value (bathQ a b)) := by
  simp only [pairQ,Scalar.value_add,Scalar.value_smul,Scalar.value_multiply,
    scalar_value_sub,Rat.cast_pow]
  simp only [Scalar.value]
  push_cast
  ring_nf

theorem full_pair_complex : Scalar.value totalPairZ =
    ((couplingCosineQ : ℂ)^2+(couplingSineQ : ℂ)^2)*
      Scalar.value totalSystemZ*Scalar.value totalBathZ := by
  simp only [totalPairZ,totalSystemZ,totalBathZ,value_sum]
  simp_rw [pairQ_diagonal_expansion_all]
  exact square_pair_sum_all (qvalue systemQ) (qvalue bathQ)
    (couplingCosineQ : ℂ) (couplingSineQ : ℂ)

theorem full_pair_qcomplex : totalPairZ =
    Scalar.multiply (couplingCosineQ^2+couplingSineQ^2,0)
      (Scalar.multiply totalSystemZ totalBathZ) := by
  apply LoadPrimitive.scalar_value_injective
  rw [Scalar.value_multiply,Scalar.value_multiply]
  simpa [Scalar.value,mul_assoc] using full_pair_complex

theorem full_pair_mass_formula : fullPairMassQ =
    (couplingCosineQ^2+couplingSineQ^2)*
      (totalSystemZ.1*totalBathZ.1-totalSystemZ.2*totalBathZ.2) := by
  have h := congrArg Prod.fst full_pair_qcomplex
  simpa only [fullPairMassQ,Scalar.multiply,zero_mul,sub_zero] using h

theorem total_system_upper : totalSystemQ < (1000001/1000000 : ℚ) := by decide +kernel
theorem total_bath_upper : totalBathQ < (1000001/1000000 : ℚ) := by decide +kernel
theorem total_coupling_upper : couplingCosineQ^2+couplingSineQ^2 < (1000001/1000000 : ℚ) := by decide +kernel

theorem total_system_imag_bound : |totalSystemZ.2| < (1/10^10 : ℚ) := by decide +kernel
theorem total_bath_imag_bound : |totalBathZ.2| < (1/10^10 : ℚ) := by decide +kernel
theorem total_system_lower : (99/100 : ℚ) < totalSystemQ := by decide +kernel
theorem total_bath_lower : (99/100 : ℚ) < totalBathQ := by decide +kernel

private theorem abs_prod_upper (si bi e : ℚ) (he : 0 < e)
    (hsi : |si| < e) (hbi : |bi| < e) : |si*bi| < e*e := by
  rw [abs_mul]
  calc
    |si| * |bi| ≤ e * |bi| := mul_le_mul_of_nonneg_right (le_of_lt hsi) (abs_nonneg _)
    _ < e*e := mul_lt_mul_of_pos_left hbi he

private theorem product3_upper (c s b u : ℚ) (hu : 0 < u)
    (hs : 0 ≤ s) (hb : 0 ≤ b)
    (hcu : c < u) (hsu : s < u) (hbu : b < u) : c*s*b < u*u*u := by
  have h1 : c*s ≤ u*s := mul_le_mul_of_nonneg_right (le_of_lt hcu) hs
  have h2 : u*s ≤ u*u := mul_le_mul_of_nonneg_left (le_of_lt hsu) (le_of_lt hu)
  have h3 : u*u*b < u*u*u := mul_lt_mul_of_pos_left hbu (mul_pos hu hu)
  calc
    c*s*b ≤ u*s*b := mul_le_mul_of_nonneg_right h1 hb
    _ ≤ u*u*b := mul_le_mul_of_nonneg_right h2 hb
    _ < u*u*u := h3

private theorem corr_upper (c si bi u e : ℚ) (hu : 0 < u) (he : 0 < e)
    (hc : 0 ≤ c) (hcu : c < u) (hsi : |si| < e) (hbi : |bi| < e) :
    |c*(si*bi)| < u*(e*e) := by
  have habs : |si*bi| < e*e := by
    rw [abs_mul]
    calc
      |si| * |bi| ≤ e * |bi| := mul_le_mul_of_nonneg_right (le_of_lt hsi) (abs_nonneg _)
      _ < e*e := mul_lt_mul_of_pos_left hbi he
  rw [abs_mul,abs_of_nonneg hc]
  calc
    c * |si*bi| ≤ u * |si*bi| := mul_le_mul_of_nonneg_right (le_of_lt hcu) (abs_nonneg _)
    _ < u*(e*e) := mul_lt_mul_of_pos_left habs hu

private theorem final_bound (c s b si bi u e M : ℚ)
    (hp : c*s*b < u*u*u)
    (hcorr : |c*(si*bi)| < u*(e*e))
    (target : u*u*u+u*(e*e) < M) : c*(s*b-si*bi) < M := by
  have hneg : -(c*(si*bi)) ≤ |c*(si*bi)| := neg_le_abs _
  have hstep : c*s*b + -(c*(si*bi)) ≤ c*s*b + |c*(si*bi)| :=
    add_le_add_right hneg (c*s*b)
  calc
    c*(s*b-si*bi) = c*s*b + -(c*(si*bi)) := by simp only [sub_eq_add_neg,mul_add,mul_neg,mul_assoc]
    _ ≤ c*s*b+|c*(si*bi)| := hstep
    _ < u*u*u+|c*(si*bi)| := add_lt_add_left hp |c*(si*bi)|
    _ < u*u*u+u*(e*e) := add_lt_add_right hcorr (u*u*u)
    _ < M := target
private theorem product_source_mass_upper
    (c s b si bi u e M : ℚ)
    (hu : 0 < u) (he : 0 < e)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hb : 0 ≤ b)
    (hcu : c < u) (hsu : s < u) (hbu : b < u)
    (hsi : |si| < e) (hbi : |bi| < e)
    (target : u*u*u+u*(e*e) < M) :
    c*(s*b-si*bi) < M :=
  final_bound c s b si bi u e M
    (product3_upper c s b u hu hs hb hcu hsu hbu)
    (corr_upper c si bi u e hu he hc hcu hsi hbi) target

theorem full_pair_mass_upper : fullPairMassQ < (100001/100000 : ℚ) := by
  calc
    fullPairMassQ = (couplingCosineQ^2+couplingSineQ^2)*
      (totalSystemZ.1*totalBathZ.1-totalSystemZ.2*totalBathZ.2) := full_pair_mass_formula
    _ < _ := product_source_mass_upper
      (couplingCosineQ^2+couplingSineQ^2) totalSystemZ.1 totalBathZ.1
      totalSystemZ.2 totalBathZ.2
      (1000001/1000000) (1/10^10) (100001/100000)
      (by norm_num) (by norm_num) coupling_square_positive
      (le_trans (by norm_num : (0 : ℚ) ≤ 99/100)
        (le_of_lt (by simpa only [totalSystemQ] using total_system_lower)))
      (le_trans (by norm_num : (0 : ℚ) ≤ 99/100)
        (le_of_lt (by simpa only [totalBathQ] using total_bath_lower)))
      total_coupling_upper
      (by simpa only [totalSystemQ] using total_system_upper)
      (by simpa only [totalBathQ] using total_bath_upper)
      total_system_imag_bound total_bath_imag_bound (by norm_num)

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
