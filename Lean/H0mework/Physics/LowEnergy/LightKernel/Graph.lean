import H0mework.Physics.LowEnergy.BosonEffective.Schur

/-! A source-selected invertible complement produces the actual zero-mode graph;
the retained coordinate axes are not substituted for that graph. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
noncomputable section
variable {h l : Type*} [Fintype h] [Fintype l]

def zeroGraph (G : Matrix h h ℂ) (B : Matrix h l ℂ) (v : l → ℂ) : (h ⊕ l) → ℂ :=
  Sum.elim (-(G*ᵥ(B*ᵥv))) v

theorem zeroGraph_retained (G : Matrix h h ℂ) (B : Matrix h l ℂ) (v : l → ℂ) (i : l) :
    zeroGraph G B v (.inr i)=v i := rfl

theorem zeroGraph_injective (G : Matrix h h ℂ) (B : Matrix h l ℂ) :
    Function.Injective (zeroGraph G B) := by
  intro v w same
  funext i
  exact congrFun same (.inr i)

variable [DecidableEq h]

theorem zeroGraph_kernel (A G : Matrix h h ℂ) (B : Matrix h l ℂ)
    (C : Matrix l h ℂ) (D : Matrix l l ℂ) (right : A*G=1)
    (zeroSchur : D-C*G*B=0) (v : l → ℂ) :
    Matrix.fromBlocks A B C D*ᵥzeroGraph G B v=0 := by
  have upper := BosonEffective.eliminated_row A G B right v
  have lower := BosonEffective.retained_row D C B G v
  rw [BosonEffective.schur,zeroSchur,Matrix.zero_mulVec] at lower
  ext i
  cases i with
  | inl i => simpa [zeroGraph,Matrix.fromBlocks_mulVec,BosonEffective.matterWrite,add_comm] using congrFun upper i
  | inr i => simpa [zeroGraph,Matrix.fromBlocks_mulVec,BosonEffective.matterWrite,add_comm] using congrFun lower i

theorem kernel_is_zeroGraph (A G : Matrix h h ℂ) (B : Matrix h l ℂ)
    (C : Matrix l h ℂ) (D : Matrix l l ℂ) (left : G*A=1)
    (v : (h ⊕ l) → ℂ) (kernel : Matrix.fromBlocks A B C D*ᵥv=0) :
    v=zeroGraph G B (fun i => v (.inr i)) := by
  have upper : B*ᵥ(fun i => v (.inr i))+A*ᵥ(fun i => v (.inl i))=0 := by
    ext i
    have coordinate := congrFun kernel (.inl i)
    simpa [Matrix.fromBlocks_mulVec,Function.comp_def,add_comm] using coordinate
  have generated := BosonEffective.eliminated_unique A G B left _ _ upper
  ext i
  cases i with
  | inl i => exact congrFun generated i
  | inr i => rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
