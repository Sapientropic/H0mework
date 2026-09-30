import H0mework.Physics.LowEnergy.FullQuantum.StateResponse.Connected
import H0mework.Physics.LowEnergy.FullQuantum.StateGreen.Flow

/-! The original inverse creator and annihilator generate the full bilinear
word before it is read as a transported one-particle matrix. -/
set_option autoImplicit false
open scoped Matrix BigOperators
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
open QuantizationCheck.Fermion Fermion StateGreen
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
private theorem sum_four_swap {E : Type*} [AddCommMonoid E] (f : ι → ι → ι → ι → E) :
    (∑ i, ∑ j, ∑ b, ∑ a, f i j b a) = ∑ a, ∑ b, ∑ i, ∑ j, f i j b a := by
  have swapped : (∑ ij : ι×ι, ∑ ba : ι×ι, f ij.1 ij.2 ba.1 ba.2)=
      ∑ ba : ι×ι, ∑ ij : ι×ι, f ij.1 ij.2 ba.1 ba.2 := Finset.sum_comm
  calc
    _ = ∑ b, ∑ a, ∑ i, ∑ j, f i j b a := by
      simpa only [Fintype.sum_prod_type] using swapped
    _ = _ := Finset.sum_comm

def transportedWord (Z W A : Matrix ι ι ℂ) : Module.End ℂ (Fock ι) :=
  ∑ i, ∑ j, A i j • (creationField Z.conjTranspose i*annihilationField W j)

theorem transportedWord_generated (Z W A : Matrix ι ι ℂ) :
    transportedWord Z W A=quantize (Z*A*W) := by
  rw [Matrix.mul_assoc]
  simp only [transportedWord,creationField,annihilationField,Matrix.conjTranspose_apply,
    star_star,Finset.sum_mul,Finset.mul_sum,smul_mul_smul,Finset.smul_sum,smul_smul]
  rw [sum_four_swap]
  simp only [quantize,Matrix.mul_apply,Finset.mul_sum,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
attribute [local instance] Fermion.fullIndexOrder

def sourceObservable (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) (A : SourceMatrix) :
    Module.End ℂ (Fock Quantum.Index) :=
  ∑ i, ∑ j, A i j •
    (momentumCreator actual point momentum time i*FullQuantum.annihilator actual point momentum time j)

def heisenberg (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) (A : SourceMatrix) : SourceMatrix :=
  U point momentum (-time)*A*U point momentum time

theorem sourceObservable_generated (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) (A : SourceMatrix) :
    sourceObservable point momentum time A=quantize (heisenberg point momentum time A) :=
  transportedWord_generated (U point momentum (-time)) (U point momentum time) A

def sourceConnected (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ) (A B : SourceMatrix) : ℂ :=
  read (preparedVector point) (sourceObservable point momentum t A*sourceObservable point momentum s B)-
    read (preparedVector point) (sourceObservable point momentum t A)*
      read (preparedVector point) (sourceObservable point momentum s B)

theorem sourceConnected_generated (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ) (A B : SourceMatrix) :
    sourceConnected point momentum t s A B=Matrix.trace (occupation point*
      heisenberg point momentum t A*(1-occupation point)*heisenberg point momentum s B) := by
  simp only [sourceConnected,sourceObservable_generated]
  exact connected_generated (preparedVector point) _ _

def sourceKuboWord (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ) (R B : SourceMatrix) :
    Module.End ℂ (Fock Quantum.Index) :=
  Complex.I • (sourceObservable point momentum s R*sourceObservable point momentum t B-
    sourceObservable point momentum t B*sourceObservable point momentum s R)

theorem sourceKubo_generated (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ) (R B : SourceMatrix) :
    read (preparedVector point) (sourceKuboWord point momentum t s R B)=
      Complex.I*(sourceConnected point momentum s t R B-sourceConnected point momentum t s B R) := by
  simp only [sourceKuboWord,sourceConnected,sourceObservable_generated]
  exact kubo_generated (preparedVector point) _ _

theorem sourceKubo_trace (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ) (R B : SourceMatrix) :
    read (preparedVector point) (sourceKuboWord point momentum t s R B)=
      Complex.I*Matrix.trace (occupation point*(heisenberg point momentum s R*heisenberg point momentum t B-
        heisenberg point momentum t B*heisenberg point momentum s R)) := by
  simp only [sourceKuboWord,sourceObservable_generated]
  exact kubo_trace (preparedVector point) _ _

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
