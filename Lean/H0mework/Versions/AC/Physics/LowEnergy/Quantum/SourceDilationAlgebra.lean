import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceKineticSquare

set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceDilationAlgebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem scalar_sum_commutes (X A B : R) (hA : Commute X A) (hB : Commute X B) (c : ℂ) :
    Commute X (c • (A+B)) := (hA.add_right hB).smul_right c

theorem scalar_commutes (X A : R) (hA : Commute X A) (c : ℂ) :
    Commute X (c • A) := hA.smul_right c

theorem homogeneous_smul (D A : R) (a c : ℂ) (h : D*A-A*D=a • A) :
    D*(c • A)-(c • A)*D=a • (c • A) := by
  rw [mul_smul_comm, smul_mul_assoc, ←smul_sub, h, smul_comm]

theorem homogeneous_add (D A B : R) (a : ℂ)
    (hA : D*A-A*D=a • A) (hB : D*B-B*D=a • B) :
    D*(A+B)-(A+B)*D=a • (A+B) := by
  calc
    _ = (D*A-A*D)+(D*B-B*D) := by noncomm_ring
    _ = _ := by rw [hA,hB,smul_add]

theorem homogeneous_mul (D A B : R) (a b : ℂ)
    (hA : D*A-A*D=a • A) (hB : D*B-B*D=b • B) :
    D*(A*B)-(A*B)*D=(a+b) • (A*B) := by
  calc
    _ = (D*A-A*D)*B+A*(D*B-B*D) := by noncomm_ring
    _ = _ := by rw [hA,hB,smul_mul_assoc,mul_smul_comm,add_smul]

theorem homogeneous_sum {ι : Type*} [Fintype ι] (D : R) (A : ι → R) (a : ℂ)
    (h : ∀ i, D*A i-A i*D=a • A i) :
    D*(∑ i, A i)-(∑ i, A i)*D=a • ∑ i, A i := by
  simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib,h,Finset.smul_sum]

theorem affine_dilation (E N A : R) (k : ℂ)
    (hE : E*A-A*E=k • A) (hN : Commute N A) :
    ((-Complex.I) • ((2/3 : ℂ) • E+N+(4 : ℂ) • 1))*A-
      A*((-Complex.I) • ((2/3 : ℂ) • E+N+(4 : ℂ) • 1)) =
        ((-2*Complex.I/3)*k) • A := by
  calc
    _ = (-2*Complex.I/3) • (E*A-A*E)+(-Complex.I) • (N*A-A*N) := by
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one]
      module
    _ = _ := by rw [hE,hN.eq,sub_self,smul_zero,add_zero,smul_smul]

end LowEnergy.SourceDilationAlgebra
