import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.StateResponse.Connected

/-! One prepared incoming momentum-zero sector and two intermediate sectors
retain both ordered transfer legs in the same full CAR carrier. -/
set_option autoImplicit false
open scoped Matrix BigOperators
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
open QuantizationCheck.Fermion Fermion StateGreen
noncomputable section
variable {ι : Type*} [Fintype ι]

def modeVector (mode : Fin 3) (w : ι → ℂ) : Fin 3×ι → ℂ :=
  fun index => if index.1=mode then w index.2 else 0

def channel (target incoming : Fin 3) (A : Matrix ι ι ℂ) : Matrix (Fin 3×ι) (Fin 3×ι) ℂ :=
  fun i j => if i.1=target ∧ j.1=incoming then A i.2 j.2 else 0

theorem modeVector_pair (mode other : Fin 3) (u v : ι → ℂ) :
    modePair (modeVector mode u) (modeVector other v)=
      if mode=other then modePair u v else 0 := by
  fin_cases mode <;> fin_cases other <;>
    simp [modeVector,modePair,Fintype.sum_prod_type]

theorem channel_vector (target incoming mode : Fin 3) (A : Matrix ι ι ℂ) (w : ι → ℂ) :
    channel target incoming A*ᵥmodeVector mode w=
      if incoming=mode then modeVector target (A*ᵥw) else 0 := by
  ext index
  rcases index with ⟨label,index⟩
  fin_cases incoming <;> fin_cases mode <;>
    simp [channel,modeVector,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
      ite_and,ite_mul,Finset.sum_ite_irrel]

abbrev transferIndexOrder : LinearOrder (Fin 3×ι) :=
  LinearOrder.lift' (Fintype.equivFin (Fin 3×ι)) (Fintype.equivFin _).injective
attribute [local instance] transferIndexOrder

def transferForce (T : Matrix ι ι ℂ) : Matrix (Fin 3×ι) (Fin 3×ι) ℂ :=
  channel 1 0 T+channel 0 2 T

def transferReader (B Rplus Rminus : Matrix ι ι ℂ) : Matrix (Fin 3×ι) (Fin 3×ι) ℂ :=
  channel 0 1 (B*Rplus)+channel 2 0 (Rminus*B)

theorem transferForce_source (T : Matrix ι ι ℂ) (w : ι → ℂ) :
    transferForce T*ᵥmodeVector 0 w=modeVector 1 (T*ᵥw) := by
  simp [transferForce,Matrix.add_mulVec,channel_vector]

theorem transferReader_source (B Rplus Rminus : Matrix ι ι ℂ) (w : ι → ℂ) :
    transferReader B Rplus Rminus*ᵥmodeVector 0 w=modeVector 2 ((Rminus*B)*ᵥw) := by
  simp [transferReader,Matrix.add_mulVec,channel_vector]

theorem transfer_forward (w : ι → ℂ) (T B Rplus Rminus : Matrix ι ι ℂ) :
    connected (modeVector 0 w) (transferReader B Rplus Rminus) (transferForce T)=
      modePair w ((B*Rplus*T)*ᵥw) := by
  rw [connected,read_four_word,read_quantize,read_quantize]
  rw [← Matrix.mulVec_mulVec,transferForce_source,transferReader_source]
  simp only [transferReader,Matrix.add_mulVec,channel_vector]
  simp [modeVector_pair,Matrix.mulVec_mulVec]

theorem transfer_backward (w : ι → ℂ) (T B Rplus Rminus : Matrix ι ι ℂ) :
    connected (modeVector 0 w) (transferForce T) (transferReader B Rplus Rminus)=
      modePair w ((T*Rminus*B)*ᵥw) := by
  rw [connected,read_four_word,read_quantize,read_quantize]
  rw [← Matrix.mulVec_mulVec,transferReader_source,transferForce_source]
  simp only [transferForce,Matrix.add_mulVec,channel_vector]
  simp [modeVector_pair,Matrix.mulVec_mulVec,Matrix.mul_assoc]

theorem transfer_response (w : ι → ℂ) (T B Rplus Rminus : Matrix ι ι ℂ) :
    read (modeVector 0 w) (connectedWord (modeVector 0 w) (transferReader B Rplus Rminus) (transferForce T)-
      connectedWord (modeVector 0 w) (transferForce T) (transferReader B Rplus Rminus))=
      modePair w ((B*Rplus*T)*ᵥw)-modePair w ((T*Rminus*B)*ᵥw) := by
  rw [map_sub,connectedWord_read,connectedWord_read,transfer_forward,transfer_backward]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
