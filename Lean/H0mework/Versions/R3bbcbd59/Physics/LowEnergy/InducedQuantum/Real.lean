import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.InducedQuantum.Adjoint
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Boundary

/-! Real density means the Hermitian part of the complete CAR word. Its
adjoint is taken on the whole occupation space, before the original source read. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
open QuantizationCheck.Fermion Fermion FullQuantum.StateGreen
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def realWord (word : Module.End ℂ (Fock ι)) : Module.End ℂ (Fock ι) :=
  (1/2 : ℂ) • (word+dagger word)

theorem realWord_adjoint (word : Module.End ℂ (Fock ι)) : dagger (realWord word)=realWord word := by
  simp [realWord,dagger_smul,dagger_add,dagger_involutive,add_comm]

theorem realWord_pair (word : Module.End ℂ (Fock ι)) (u v : Fock ι) :
    pairing u (realWord word v)=(1/2 : ℂ)*(pairing u (word v)+pairing (word u) v) := by
  change modePair u ((1/2 : ℂ) • (word v+dagger word v))=_
  rw [modePair_smul_right,modePair_add_right]
  change (1/2 : ℂ)*(pairing u (word v)+pairing u (dagger word v))=_
  rw [dagger_pair_left]

theorem read_realWord (w : ι → ℂ) (word : Module.End ℂ (Fock ι)) :
    read w (realWord word)=((read w word).re : ℂ) := by
  rw [realWord,map_smul,map_add,read_dagger,Complex.re_eq_add_conj]
  simp only [smul_eq_mul,starRingEnd_apply]
  ring

def physicalWord (word : Module.End ℂ (Fock ι)) : Module.End ℂ (Fock ι) :=
  (-4 : ℂ) • realWord word

theorem physicalWord_adjoint (word : Module.End ℂ (Fock ι)) :
    dagger (physicalWord word)=physicalWord word := by
  simp [physicalWord,dagger_smul,realWord_adjoint]

theorem read_physicalWord (w : ι → ℂ) (word : Module.End ℂ (Fock ι)) :
    read w (physicalWord word)=((-4*read w word).re : ℂ) := by
  rw [physicalWord,map_smul,read_realWord]
  simp

theorem quantize_oneParticle (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    quantize A (oneParticle v)=oneParticle (A*ᵥv) := by
  rw [quantize_apply,source_matrix_oneParticle]

theorem product_oneParticle (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    (quantize A*quantize B) (oneParticle v)=oneParticle ((A*B)*ᵥv) := by
  rw [Module.End.mul_apply,quantize_oneParticle,quantize_oneParticle,Matrix.mulVec_mulVec]

theorem realProduct_oneParticle (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    realWord (quantize A*quantize B) (oneParticle v)=oneParticle (hermitianPart (A*B)*ᵥv) := by
  simp only [realWord,LinearMap.smul_apply,LinearMap.add_apply,dagger_mul,dagger_quantize,
    product_oneParticle,hermitianPart,Matrix.smul_mulVec,Matrix.add_mulVec,
    Matrix.conjTranspose_mul]
  change (1/2 : ℂ) • (oneParticleLinear ((A*B)*ᵥv)+
    oneParticleLinear ((B.conjTranspose*A.conjTranspose)*ᵥv))=
    oneParticleLinear ((1/2 : ℂ) • ((A*B)*ᵥv+(B.conjTranspose*A.conjTranspose)*ᵥv))
  rw [← map_add,← map_smul]


attribute [local instance] Fermion.fullIndexOrder
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open YangMills.FullPairing FullQuantum

theorem original_real_density (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : FullQuantum.Mother) :
    read (preparedVector point) (physicalWord (CoframeResponse.boundaryWord C point k t A))=
      (((((|(C.coframe point).det| : ℝ) : ℂ)*canonicalDual C point k t
        (actual.conjugateMatter point) (A (primal C point k t (actual.matter point)))).re) : ℂ) := by
  rw [read_physicalWord,CoframeResponse.original_dual_full_CAR]

theorem original_real_density_source (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : FullQuantum.Mother) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Stage9DEF.Compatibility.responseMatrix (pairedMother 1
        (sourceWordMother (physicalWord (CoframeResponse.boundaryWord C point k t A)))))=
      (((((|(C.coframe point).det| : ℝ) : ℂ)*canonicalDual C point k t
        (actual.conjugateMatter point) (A (primal C point k t (actual.matter point)))).re) : ℂ) := by
  rw [source_word_readback,original_real_density]

end
end SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
