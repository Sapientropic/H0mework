import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.StateResponse.TransferNative

/-! Independent primal and dual legs share one incoming source state. The temporal
momentum weight acts at its boundary before either complete transfer word is read. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrent
open QuantizationCheck.Fermion Fermion StateGreen StateResponse
noncomputable section
variable {ι : Type*} [Fintype ι]
attribute [local instance] transferIndexOrder

private theorem quantize_particle (A : Matrix (Fin 3×ι) (Fin 3×ι) ℂ) (v : Fin 3×ι → ℂ) :
    quantize A (oneParticle v)=oneParticle (A*ᵥv) := by
  rw [quantize_apply]
  exact secondQuantize_oneParticle (fun i j => A i j) v

def transferLeg (label : Fin 3) (K A G V : Matrix ι ι ℂ) : Module.End ℂ (Fock (Fin 3×ι)) :=
  quantize (channel 0 0 K)*quantize (channel 0 label A)*
    quantize (channel label label G)*quantize (channel label 0 V)

theorem transferLeg_read (label : Fin 3) (K A G V : Matrix ι ι ℂ) (w : ι → ℂ) :
    read (modeVector 0 w) (transferLeg label K A G V)=modePair w ((K*A*G*V)*ᵥw) := by
  change pairing (oneParticle (modeVector 0 w)) ((transferLeg label K A G V) (oneParticle (modeVector 0 w)))=_
  simp only [transferLeg,Module.End.mul_apply,quantize_particle,channel_vector,if_true]
  rw [pairing_oneParticle]
  change modePair (modeVector 0 w) (modeVector 0 (K*ᵥ(A*ᵥ(G*ᵥ(V*ᵥw)))))=_
  rw [modeVector_pair,if_pos rfl]
  simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]

def contactWord (K J : Matrix ι ι ℂ) : Module.End ℂ (Fock (Fin 3×ι)) :=
  quantize (channel 0 0 K)*quantize (channel 0 0 J)

theorem contactWord_read (K J : Matrix ι ι ℂ) (w : ι → ℂ) :
    read (modeVector 0 w) (contactWord K J)=modePair w ((K*J)*ᵥw) := by
  rw [contactWord,read_four_word,← Matrix.mulVec_mulVec,channel_vector]
  simp only [if_true,channel_vector,modeVector_pair,Matrix.mulVec_mulVec]

def fullResponseWord (scale : ℂ) (K CI Bplus Czero Cminus Bzero Gplus Gminus J : Matrix ι ι ℂ) :
    Module.End ℂ (Fock (Fin 3×ι)) :=
  -scale • (transferLeg 1 K (CI*Bplus) Gplus Czero+
    transferLeg 2 K (CI*Cminus) Gminus Bzero)+contactWord K (CI*J)

theorem fullResponseWord_read (scale : ℂ) (K CI Bplus Czero Cminus Bzero Gplus Gminus J : Matrix ι ι ℂ)
    (w : ι → ℂ) :
    read (modeVector 0 w) (fullResponseWord scale K CI Bplus Czero Cminus Bzero Gplus Gminus J)=
      modePair w ((K*CI*(-scale • (Bplus*Gplus*Czero+Cminus*Gminus*Bzero)+J))*ᵥw) := by
  rw [fullResponseWord,map_add,map_smul,map_add,transferLeg_read,transferLeg_read,contactWord_read]
  simp only [Matrix.mul_add,Matrix.mul_smul,Matrix.add_mulVec,Matrix.smul_mulVec,
    modePair_add_right,modePair_smul_right,Matrix.mul_assoc]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrent
