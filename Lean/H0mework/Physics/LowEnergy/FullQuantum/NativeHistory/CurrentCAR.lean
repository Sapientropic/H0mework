import H0mework.Physics.LowEnergyFockDynamics.Algebra

/-! Original canonical field frames lift every real differential vertex to
the full CAR algebra. The independent momentum is a literal creator row;
no Hilbert-adjoint identification is inserted. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.NativeHistory.CurrentCAR
open QuantizationCheck.Fermion
open Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def momentumField (B : Matrix ι ι ℂ) (i : ι) : Module.End ℂ (Fock ι) :=
  ∑ j, B i j • creation j

def vertex (A B D : Matrix ι ι ℂ) : Matrix ι ι ℂ := B.transpose*D*A

omit [Fintype ι] in
private theorem creation_anticommutator (i j : ι) :
    creation i*creation j+creation j*creation i=(0 : Module.End ℂ (Fock ι)) := by
  apply LinearMap.ext
  intro ψ
  funext word
  exact congrFun (create_create_car i j ψ) word

omit [Fintype ι] in
private theorem creation_word_commutator (i j k : ι) :
    (creation j*annihilation k)*creation i-creation i*(creation j*annihilation k)=
      if k=i then creation j else 0 := by
  calc
    _ = creation j*(annihilation k*creation i+creation i*annihilation k)-
        (creation j*creation i+creation i*creation j)*annihilation k := by noncomm_ring
    _ = _ := by rw [operator_car,creation_anticommutator]; split <;> simp_all

omit [Fintype ι] [LinearOrder ι] in
private theorem weighted_sub (c : ℂ) (A B : Module.End ℂ (Fock ι)) :
    c • A-c • B=c • (A-B) := (smul_sub c A B).symm

theorem creation_quantize (H : Matrix ι ι ℂ) (i : ι) :
    quantize H*creation i-creation i*quantize H=∑ j, H j i • creation j := by
  simp only [quantize,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,weighted_sub,creation_word_commutator]
  simp [smul_ite]

theorem momentum_quantize (B H : Matrix ι ι ℂ) (i : ι) :
    quantize H*momentumField B i-momentumField B i*quantize H=
      momentumField (B*H.transpose) i := by
  simp only [momentumField,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
  rw [← Finset.sum_sub_distrib]
  simp_rw [weighted_sub,creation_quantize,Finset.smul_sum,smul_smul]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_smul]
  rw [Finset.sum_comm]

theorem primal_vertex_matrix (A B D : Matrix ι ι ℂ)
    (canonical : A*B.transpose=Complex.I • (1 : Matrix ι ι ℂ)) :
    (-Complex.I) • (A*vertex A B D)=D*A := by
  unfold vertex
  rw [← Matrix.mul_assoc A,← Matrix.mul_assoc A,canonical]
  simp only [smul_mul_assoc,Matrix.one_mul,smul_smul]
  simp [Complex.I_mul_I]

theorem momentum_vertex_matrix (A B D : Matrix ι ι ℂ)
    (canonical : B*A.transpose=Complex.I • (1 : Matrix ι ι ℂ)) :
    Complex.I • (B*(vertex A B D).transpose)= -D.transpose*B := by
  unfold vertex
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,
    ← Matrix.mul_assoc B,canonical]
  simp only [smul_mul_assoc,Matrix.one_mul,smul_smul]
  simp [Complex.I_mul_I]

private theorem annihilation_smul (c : ℂ) (A : Matrix ι ι ℂ) (i : ι) :
    c • annihilationField A i=annihilationField (c • A) i := by
  simp [annihilationField,Finset.smul_sum,smul_smul]

private theorem momentum_smul (c : ℂ) (A : Matrix ι ι ℂ) (i : ι) :
    c • momentumField A i=momentumField (c • A) i := by
  simp [momentumField,Finset.smul_sum,smul_smul]

theorem primal_vertex_commutator (A B D : Matrix ι ι ℂ)
    (canonical : A*B.transpose=Complex.I • (1 : Matrix ι ι ℂ)) (i : ι) :
    Complex.I • (quantize (vertex A B D)*annihilationField A i-
      annihilationField A i*quantize (vertex A B D))=annihilationField (D*A) i := by
  have reversed := neg_sub (annihilationField A i*quantize (vertex A B D))
    (quantize (vertex A B D)*annihilationField A i)
  rw [← reversed,field_quantize,smul_neg,← neg_smul,annihilation_smul,
    primal_vertex_matrix A B D canonical]

theorem momentum_vertex_commutator (A B D : Matrix ι ι ℂ)
    (canonical : B*A.transpose=Complex.I • (1 : Matrix ι ι ℂ)) (i : ι) :
    Complex.I • (quantize (vertex A B D)*momentumField B i-
      momentumField B i*quantize (vertex A B D))=momentumField (-D.transpose*B) i := by
  rw [momentum_quantize,momentum_smul,momentum_vertex_matrix A B D canonical]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.NativeHistory.CurrentCAR
