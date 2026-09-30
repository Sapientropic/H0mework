import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-! Coefficients generated in the original five emitted zero modes, ordered
as vector real rescaling, vector phase, axial real rescaling, axial phase,
and imaginary independent-dual rescaling. The source103/289 write is retained
in the corresponding exact receipt. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
noncomputable section

def first (u : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0,0,0,0,0; 0,0,0,0,0; 0,0,0,0,-8*u; 0,0,0,0,0; 0,0,8*u,0,0]

def realKernel (u q : ℂ) : ℂ := 80*q^2/9+16*u^2/3
def vectorKernel (u q : ℂ) : ℂ := 160*q^2/67+32*u^2/11
def axialKernel (u q : ℂ) : ℂ := 2500*q^2/81-40*u^2
def realMix (u q : ℂ) : ℂ := 80*Complex.I*q*u/9+16*u^2/3
def vectorMix (u q : ℂ) : ℂ := -80*q^2/67-32*u^2/11
def axialMix (u q : ℂ) : ℂ := -20*Complex.I*q*u/3
def pairDiagonal₁ (u q : ℂ) : ℂ := -40*q^2/3+80*Complex.I*q*u/3+88*u^2/9
def pairDiagonal₂ (u q : ℂ) : ℂ := -550*q^2/201-2438*u^2/561

def second (u q : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![realKernel u q,0,realMix u q,0,0;
     0,vectorKernel u q,0,0,vectorMix u q;
     realMix u q,0,pairDiagonal₁ u q,0,0;
     0,0,0,axialKernel u q,axialMix u q;
     0,vectorMix u q,0,axialMix u q,pairDiagonal₂ u q]

def pencil (u q : ℂ) : Matrix (Fin 5) (Fin 5) ℂ := first u+second u q

def pair (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0,-8*u;8*u,0]
def pairSecond (u q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![pairDiagonal₁ u q,0;0,pairDiagonal₂ u q]
def core (u q : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![realKernel u q,0,0;0,vectorKernel u q,0;0,0,axialKernel u q]
def mixing (u q : ℂ) : Matrix (Fin 2) (Fin 3) ℂ :=
  !![realMix u q,0,0;0,vectorMix u q,axialMix u q]
def blockPencil (u q : ℂ) : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) ℂ :=
  Matrix.fromBlocks (pair u+pairSecond u q) (mixing u q) (mixing u q).transpose (core u q)

def sourceOrder : (Fin 2 ⊕ Fin 3) ≃ Fin 5 := finSumFinEquiv.trans
  { toFun := fun i => ![2,4,0,1,3] i
    invFun := fun i => ![2,3,0,4,1] i
    left_inv := by intro i; fin_cases i <;> rfl
    right_inv := by intro i; fin_cases i <;> rfl }

theorem source_block (u q : ℂ) : (pencil u q).submatrix sourceOrder sourceOrder=blockPencil u q := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pencil,first,second,sourceOrder,blockPencil,pair,pairSecond,core,mixing,Matrix.submatrix,finSumFinEquiv]

theorem source_first_kernel (v : Fin 5 → ℂ) : first 1*ᵥv=0 ↔ v 2=0 ∧ v 4=0 := by
  constructor
  · intro zero
    have h2 := congrFun zero 2
    have h4 := congrFun zero 4
    simp [first] at h2 h4
    exact ⟨h4,h2⟩
  · rintro ⟨left,right⟩
    ext i
    fin_cases i <;> simp [first]
    · exact right
    · exact left

theorem core_determinant (u q : ℂ) : (core u q).det=
    (10240/537273 : ℂ)*(5*q^2+3*u^2)*(55*q^2+67*u^2)*(125*q^2-162*u^2) := by
  rw [Matrix.det_fin_three]
  simp [core,realKernel,vectorKernel,axialKernel]
  ring

theorem pair_determinant (u : ℂ) : (pair u).det=64*u^2 := by
  rw [Matrix.det_fin_two]
  simp [pair]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
