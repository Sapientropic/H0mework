import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.StateGreen.Preparation
import H0mework.Physics.LowEnergyFermion.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The full occupation-space adjoint is generated before any one-particle
compression or source readout. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
open QuantizationCheck.Fermion Fermion FullQuantum.StateGreen
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def dagger (word : Module.End ℂ (Fock ι)) : Module.End ℂ (Fock ι) :=
  Matrix.toLin' (LinearMap.toMatrix' word).conjTranspose

theorem dagger_matrix (word : Module.End ℂ (Fock ι)) :
    LinearMap.toMatrix' (dagger word)=(LinearMap.toMatrix' word).conjTranspose :=
  LinearMap.toMatrix'_toLin' _

theorem dagger_pair (word : Module.End ℂ (Fock ι)) (u v : Fock ι) :
    pairing u (dagger word v)=star (pairing v (word u)) := by
  change modePair u ((LinearMap.toMatrix' word).conjTranspose*ᵥv)=star (modePair v (word u))
  rw [modePair_conjTranspose,LinearMap.toMatrix'_mulVec]

theorem dagger_involutive (word : Module.End ℂ (Fock ι)) : dagger (dagger word)=word := by
  simp [dagger]

theorem dagger_add (first second : Module.End ℂ (Fock ι)) : dagger (first+second)=dagger first+dagger second := by
  simp [dagger]

theorem dagger_smul (c : ℂ) (word : Module.End ℂ (Fock ι)) : dagger (c • word)=star c • dagger word := by
  simp [dagger]

theorem dagger_mul (first second : Module.End ℂ (Fock ι)) : dagger (first*second)=dagger second*dagger first := by
  simp only [dagger,LinearMap.toMatrix'_mul,Matrix.conjTranspose_mul,Matrix.toLin'_mul]
  rfl

theorem dagger_creation (i : ι) : dagger (creation i)=annihilation i := by
  apply LinearMap.toMatrix'.injective
  rw [dagger_matrix]
  ext s t
  simp only [Matrix.conjTranspose_apply,LinearMap.toMatrix'_apply,creation_apply,annihilation_apply,
    create,annihilate]
  by_cases occupied : i∈s
  · rw [if_pos occupied]
    by_cases other : i∈t
    · have different : t.erase i≠s := by
        intro same
        have absent := Finset.notMem_erase i t
        exact absent (same.symm ▸ occupied)
      simp [other,different]
    · simp [other]
  · rw [if_neg occupied]
    by_cases other : i∈t
    · by_cases same : t=insert i s
      · subst t
        simp [occupied,star_sign]
      · have different : t.erase i≠s := by
          intro equal
          exact same ((Finset.insert_erase other).symm.trans (congrArg (insert i) equal))
        simp [other,Ne.symm same,different]
    · have different : insert i s≠t := by
        intro same
        exact other (same ▸ Finset.mem_insert_self i s)
      simp [other,different]

theorem dagger_annihilation (i : ι) : dagger (annihilation i)=creation i := by
  rw [← dagger_creation,dagger_involutive]

theorem dagger_sum {κ : Type*} (s : Finset κ) (words : κ → Module.End ℂ (Fock ι)) :
    dagger (∑ i∈s, words i)=∑ i∈s, dagger (words i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dagger]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,dagger_add,ih]

theorem dagger_quantize (A : Matrix ι ι ℂ) : dagger (quantize A)=quantize A.conjTranspose := by
  simp only [quantize,dagger_sum,dagger_smul,dagger_mul,dagger_creation,dagger_annihilation,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem dagger_pair_left (word : Module.End ℂ (Fock ι)) (u v : Fock ι) :
    pairing u (dagger word v)=pairing (word u) v := by
  change modePair u ((LinearMap.toMatrix' word).conjTranspose*ᵥv)=modePair (word u) v
  rw [← modePair_adjoint_left,LinearMap.toMatrix'_mulVec]

theorem dagger_one : dagger (1 : Module.End ℂ (Fock ι))=1 := by
  simp [dagger]
  rfl

theorem read_dagger (w : ι → ℂ) (word : Module.End ℂ (Fock ι)) :
    read w (dagger word)=star (read w word) := dagger_pair word _ _

end
end SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
