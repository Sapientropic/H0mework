import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.StateGreen.Preparation

/-! The connected current kernel is the full four-CAR-word expectation in
the original one-particle state, with its actual occupation retained. -/
set_option autoImplicit false
open scoped Matrix BigOperators
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
open QuantizationCheck.Fermion Fermion StateGreen
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

private theorem annihilate_twice_oneParticle (i j : ι) (w : ι → ℂ) :
    annihilation i (annihilation j (oneParticle w))=0 := by
  simp only [annihilation_apply,annihilate_oneParticle]
  change annihilation i (w j • vacuum)=0
  simp

theorem normalProduct_oneParticle (A B : Matrix ι ι ℂ) (w : ι → ℂ) :
    normalProduct A B (oneParticle w)=0 := by
  simp only [normalProduct,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    annihilate_twice_oneParticle,map_zero,smul_zero,Finset.sum_const_zero]

theorem read_quantize (w : ι → ℂ) (A : Matrix ι ι ℂ) :
    read w (quantize A)=modePair w (A*ᵥw) := by
  change pairing (oneParticle w) (quantize A (oneParticle w))=_
  rw [quantize_apply]
  exact pairing_secondQuantize_oneParticle (fun i j => A i j) w w

theorem read_four_word (w : ι → ℂ) (A B : Matrix ι ι ℂ) :
    read w (quantize A*quantize B)=modePair w ((A*B)*ᵥw) := by
  rw [quantize_normal_order,map_add,read_quantize]
  have normal : read w (normalProduct A B)=0 := by
    change pairing (oneParticle w) (normalProduct A B (oneParticle w))=0
    rw [normalProduct_oneParticle]
    simp [pairing]
  rw [normal,add_zero]

omit [LinearOrder ι] in
theorem trace_occupation (w : ι → ℂ) (A : Matrix ι ι ℂ) :
    Matrix.trace (PreparedWeight.occupation w*A)=modePair w (A*ᵥw) := by
  rw [Matrix.trace_mul_comm,PreparedWeight.occupation,Matrix.mul_vecMulVec]
  simp only [Matrix.trace,Matrix.diag,Matrix.vecMulVec_apply,Pi.star_apply,modePair]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

omit [LinearOrder ι] in
theorem occupation_sandwich (w : ι → ℂ) (A : Matrix ι ι ℂ) :
    PreparedWeight.occupation w*A*PreparedWeight.occupation w=
      modePair w (A*ᵥw) • PreparedWeight.occupation w := by
  rw [PreparedWeight.occupation,Matrix.vecMulVec_mul,Matrix.vecMulVec_mul_vecMulVec]
  have contraction : (star w ᵥ* A) ⬝ᵥ w=modePair w (A*ᵥw) := by
    rw [← Matrix.dotProduct_mulVec]
    rfl
  rw [contraction]
  ext i j
  simp only [Matrix.vecMulVec_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  ring

omit [LinearOrder ι] in
theorem disconnected_trace (w : ι → ℂ) (A B : Matrix ι ι ℂ) :
    Matrix.trace (PreparedWeight.occupation w*A*PreparedWeight.occupation w*B)=
      modePair w (A*ᵥw)*modePair w (B*ᵥw) := by
  rw [occupation_sandwich,Matrix.smul_mul,Matrix.trace_smul,trace_occupation]
  rfl

def connected (w : ι → ℂ) (A B : Matrix ι ι ℂ) : ℂ :=
  read w (quantize A*quantize B)-read w (quantize A)*read w (quantize B)

theorem connected_generated (w : ι → ℂ) (A B : Matrix ι ι ℂ) :
    connected w A B=Matrix.trace (PreparedWeight.occupation w*A*(1-PreparedWeight.occupation w)*B) := by
  rw [connected,read_four_word,read_quantize,read_quantize]
  rw [Matrix.mul_sub,Matrix.mul_one,Matrix.sub_mul,Matrix.trace_sub,disconnected_trace,
    Matrix.mul_assoc,trace_occupation]

def connectedWord (w : ι → ℂ) (A B : Matrix ι ι ℂ) : Module.End ℂ (Fock ι) :=
  quantize A*quantize B-read w (quantize B) • quantize A

theorem connectedWord_read (w : ι → ℂ) (A B : Matrix ι ι ℂ) :
    read w (connectedWord w A B)=connected w A B := by
  rw [connectedWord,map_sub,map_smul]
  simp only [connected,smul_eq_mul,mul_comm]

def kuboWord (R B : Matrix ι ι ℂ) : Module.End ℂ (Fock ι) :=
  Complex.I • (quantize R*quantize B-quantize B*quantize R)

theorem kubo_generated (w : ι → ℂ) (R B : Matrix ι ι ℂ) :
    read w (kuboWord R B)=Complex.I*(connected w R B-connected w B R) := by
  rw [kuboWord,map_smul,map_sub]
  simp only [connected,smul_eq_mul]
  ring

theorem kubo_trace (w : ι → ℂ) (R B : Matrix ι ι ℂ) :
    read w (kuboWord R B)=Complex.I*Matrix.trace (PreparedWeight.occupation w*(R*B-B*R)) := by
  rw [kuboWord,map_smul,map_sub,read_four_word,read_four_word]
  rw [Matrix.mul_sub,Matrix.trace_sub,trace_occupation,trace_occupation]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
