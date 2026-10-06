import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.PreparedWeight.Algebra
import H0mework.Physics.LowEnergyFockDynamics.Response

/-! Compress only after the full Fock word has acted, retaining every occupation sector. -/
set_option autoImplicit false
open scoped Matrix BigOperators
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedWeight
open QuantizationCheck.Fermion
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def wholeCompression (word : Module.End ℂ (Fock ι)) : Matrix ι ι ℂ :=
  fun i j => word (oneParticle (Pi.single j 1)) {i}

theorem wholeCompression_apply (word : Module.End ℂ (Fock ι)) (initial : ι → ℂ) (i : ι) :
    (wholeCompression word*ᵥinitial) i=word (oneParticle initial) {i} := by
  have decomposition : initial=∑ j, initial j • Pi.single j 1 := by
    funext j
    simp [Pi.single_apply]
  have finite : oneParticle initial=
      ∑ j, initial j • oneParticle (Pi.single j 1) := by
    calc
      _ = Fermion.oneParticleLinear (∑ j, initial j • Pi.single j 1) := congrArg oneParticle decomposition
      _ = _ := by rw [map_sum]; simp only [map_smul]; rfl
  rw [finite,map_sum]
  simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change (∑ j, word (oneParticle (Pi.single j 1)) {i}*initial j)=
    ∑ j, initial j*word (oneParticle (Pi.single j 1)) {i}
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem wholeCompression_pair (word : Module.End ℂ (Fock ι)) (initial : ι → ℂ) :
    Fermion.modePair initial (wholeCompression word*ᵥinitial)=
      pairing (oneParticle initial) (word (oneParticle initial)) := by
  rw [pairing_oneParticle_left]
  simp only [Fermion.modePair,wholeCompression_apply]

theorem boundaryDeterminant_whole_word (word : Module.End ℂ (Fock ι)) (initial : ι → ℂ)
    (unit : Fermion.modePair initial initial=1) :
    boundaryDeterminant initial (wholeCompression word)=
      pairing (oneParticle initial) (word (oneParticle initial)) := by
  rw [boundaryDeterminant_pair initial _ unit,wholeCompression_pair]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedWeight
