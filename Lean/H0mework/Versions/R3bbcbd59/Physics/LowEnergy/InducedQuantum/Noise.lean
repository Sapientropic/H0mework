import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.InducedQuantum.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Ordered noise is the Gram of the centered complete-word outputs. The
retarded commutator is a difference of orders, not this positive Gram. -/
set_option autoImplicit false
open scoped Matrix ComplexOrder
namespace SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
open QuantizationCheck.Fermion Fermion FullQuantum.StateGreen
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def centered (w : ι → ℂ) (word : Module.End ℂ (Fock ι)) : Module.End ℂ (Fock ι) :=
  word-read w word • 1

def noise (w : ι → ℂ) (first second : Module.End ℂ (Fock ι)) : ℂ :=
  read w (dagger (centered w first)*centered w second)

def fluctuation (w : ι → ℂ) (word : Module.End ℂ (Fock ι)) : Fock ι :=
  centered w word (oneParticle w)

theorem centered_read (w : ι → ℂ) (unit : modePair w w=1) (word : Module.End ℂ (Fock ι)) :
    read w (centered w word)=0 := by
  rw [centered,map_sub,map_smul,read_one,unit]
  simp

theorem noise_gram (w : ι → ℂ) (first second : Module.End ℂ (Fock ι)) :
    noise w first second=pairing (fluctuation w first) (fluctuation w second) := by
  unfold noise FullQuantum.StateGreen.read
  simp only [LinearMap.coe_mk,AddHom.coe_mk,Module.End.mul_apply]
  exact dagger_pair_left _ _ _

omit [LinearOrder ι] in
theorem pairing_self_positive (u : Fock ι) : 0 ≤ (pairing u u).re := by
  simp only [pairing,Complex.re_sum]
  apply Finset.sum_nonneg
  intro s _
  simpa [Complex.normSq_apply,Complex.mul_re] using Complex.normSq_nonneg (u s)

omit [LinearOrder ι] in
theorem pairing_self_zero (u : Fock ι) : (pairing u u).re=0 ↔ u=0 := by
  have form : (pairing u u).re=∑ s,Complex.normSq (u s) := by
    simp [pairing,Complex.normSq_apply,Complex.mul_re]
  rw [form]
  constructor
  · intro zero
    have values := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s∈Finset.univ) =>
      Complex.normSq_nonneg (u s))).mp zero
    funext s
    exact Complex.normSq_eq_zero.mp (values s (Finset.mem_univ s))
  · intro zero
    simp [zero]

theorem noise_nonnegative (w : ι → ℂ) (word : Module.End ℂ (Fock ι)) :
    0 ≤ (noise w word word).re := by rw [noise_gram]; exact pairing_self_positive _

theorem noise_positive (w : ι → ℂ) (word : Module.End ℂ (Fock ι))
    (nonzero : fluctuation w word≠0) : 0 < (noise w word word).re := by
  rw [noise_gram]
  exact lt_of_le_of_ne (pairing_self_positive _) (Ne.symm (mt (pairing_self_zero _).mp nonzero))

def noiseMatrix {κ : Type*} (w : ι → ℂ) (words : κ → Module.End ℂ (Fock ι)) :
    Matrix κ κ ℂ := fun i j => noise w (words i) (words j)

def outputMatrix {κ : Type*} (w : ι → ℂ) (words : κ → Module.End ℂ (Fock ι)) :
    Matrix (Finset ι) κ ℂ := fun s i => fluctuation w (words i) s

theorem noiseMatrix_gram {κ : Type*} [Fintype κ] (w : ι → ℂ)
    (words : κ → Module.End ℂ (Fock ι)) :
    noiseMatrix w words=(outputMatrix w words).conjTranspose*outputMatrix w words := by
  ext i j
  exact noise_gram w (words i) (words j)

theorem noiseMatrix_positive {κ : Type*} [Fintype κ] (w : ι → ℂ)
    (words : κ → Module.End ℂ (Fock ι)) : (noiseMatrix w words).PosSemidef := by
  rw [noiseMatrix_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self (outputMatrix w words)

theorem fluctuation_oneParticle (w : ι → ℂ) (word : Module.End ℂ (Fock ι))
    (A : Matrix ι ι ℂ) (action : ∀ v,word (oneParticle v)=oneParticle (A*ᵥv)) :
    fluctuation w word=oneParticle (A*ᵥw-modePair w (A*ᵥw) • w) := by
  have mean : read w word=modePair w (A*ᵥw) := by
    change pairing (oneParticle w) (word (oneParticle w))=_
    rw [action,pairing_oneParticle]
    rfl
  simp only [fluctuation,centered,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,action,mean]
  change oneParticleLinear (A*ᵥw)-modePair w (A*ᵥw) • oneParticleLinear w=
    oneParticleLinear (A*ᵥw-modePair w (A*ᵥw) • w)
  rw [map_sub,map_smul]


attribute [local instance] Fermion.fullIndexOrder
open ProofFreeRicherAnholonomicSource YangMills.FullPairing

theorem noise_source (point : BasePoint) (first second : Module.End ℂ (Fock Quantum.Index)) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Stage9DEF.Compatibility.responseMatrix (pairedMother 1 (sourceWordMother
        (dagger (centered (preparedVector point) first)*centered (preparedVector point) second))))=
      noise (preparedVector point) first second := source_word_readback _ _

end
end SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
