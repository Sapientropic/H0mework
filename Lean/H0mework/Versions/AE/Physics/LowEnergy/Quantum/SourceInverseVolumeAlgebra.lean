import Mathlib

set_option autoImplicit false
noncomputable section
namespace LowEnergy.InverseVolumeWardAlgebra

variable {R : Type*} [Ring R] [Algebra ℂ R]

def localPolynomial (d : R →ₗ[ℂ] R) (A : R) : R :=
  d (d (d A)) + (3 : ℂ) • d (d A) - d A - (3 : ℂ) • A

def inverseLocalPolynomial (d : R →ₗ[ℂ] R) (A : R) : R :=
  d (d (d A)) + (12 : ℂ) • d (d A) + (44 : ℂ) • d A + (48 : ℂ) • A

def affinePolynomial (d : R →ₗ[ℂ] R) (A : R) : R :=
  d (d A) - (3 : ℂ) • d A + (2 : ℂ) • A

def mixedPolynomial (p g : R →ₗ[ℂ] R) (A : R) : R :=
  g (g (p A-g A)) - (5 : ℂ) • g (p A-g A) + (4 : ℂ) • (p A-g A)

def ward (p g c : R →ₗ[ℂ] R) (γ : ℂ) (A : R) : R :=
  mixedPolynomial p g A + γ • affinePolynomial p (localPolynomial c A)

def inverseWard (p g c : R →ₗ[ℂ] R) (γ : ℂ) (A : R) : R :=
  mixedPolynomial p g A + γ • affinePolynomial p (inverseLocalPolynomial c A)

theorem inverse_derivative (d : R →ₗ[ℂ] R)
    (hd : ∀ A B, d (A*B)=d A*B+A*d B) (U V : R) (a : ℂ)
    (huv : U*V=1) (hvu : V*U=1) (hU : d U=a • U) :
    d V=(-a) • V := by
  have h1 := hd 1 1
  simp only [one_mul,mul_one] at h1
  have hzero : d 1=0 := add_left_cancel (show d 1+d 1=d 1+0 by simpa using h1.symm)
  have h := congrArg (fun A : R => V*A) (hd U V)
  rw [huv,hzero,hU] at h
  simp only [mul_zero,mul_add,smul_mul_assoc,mul_smul_comm,←mul_assoc,hvu,one_mul] at h
  calc
    d V = (a • V+d V)-a • V := by abel
    _ = -a • V := by rw [←h,zero_sub,neg_smul]

theorem inverse_local_mul (d : R →ₗ[ℂ] R)
    (hd : ∀ A B, d (A*B)=d A*B+A*d B) (V A : R)
    (hV : d V=(-3 : ℂ) • V) :
    inverseLocalPolynomial d (V*A)=V*localPolynomial d A := by
  have h (B : R) : d (V*B)=V*d B-(3 : ℂ) • (V*B) := by
    rw [hd,hV,smul_mul_assoc]
    module
  simp only [inverseLocalPolynomial,localPolynomial,h,map_sub,map_smul,
    mul_add,mul_sub,mul_smul_comm]
  module

theorem inverse_ward_mul (p g c : R →ₗ[ℂ] R) (γ : ℂ)
    (hp : ∀ A B, p (A*B)=p A*B+A*p B)
    (hg : ∀ A B, g (A*B)=g A*B+A*g B)
    (hc : ∀ A B, c (A*B)=c A*B+A*c B) (V A : R)
    (hpV : p V=0) (hgV : g V=0) (hcV : c V=(-3 : ℂ) • V) :
    inverseWard p g c γ (V*A)=V*ward p g c γ A := by
  have hp' (B : R) : p (V*B)=V*p B := by rw [hp,hpV,zero_mul,zero_add]
  have hg' (B : R) : g (V*B)=V*g B := by rw [hg,hgV,zero_mul,zero_add]
  rw [inverseWard,inverse_local_mul c hc V A hcV]
  simp only [ward,mixedPolynomial,affinePolynomial,hp',hg',←mul_sub,
    ←mul_add,←mul_smul_comm]

omit [Algebra ℂ R] in
theorem inverse_commutator (H U V : R) (huv : U*V=1) (hvu : V*U=1) :
    H*V-V*H=-(V*(H*U-U*H)*V) := by
  calc
    _ = -(V*H*(U*V)-(V*U)*H*V) := by rw [huv,hvu]; simp
    _ = _ := by noncomm_ring

theorem inverse_current_weight (d : R →ₗ[ℂ] R)
    (hd : ∀ A B, d (A*B)=d A*B+A*d B) (H U V : R)
    (huv : U*V=1) (hvu : V*U=1)
    (hV : d V=(-3 : ℂ) • V) (hK : d (H*U-U*H)=0) :
    d (H*V-V*H)=(-6 : ℂ) • (H*V-V*H) := by
  rw [inverse_commutator H U V huv hvu]
  simp only [map_neg,hd,hV,hK,mul_zero,add_zero,
    smul_mul_assoc,mul_smul_comm]
  module

theorem inverse_current_invariant (d : R →ₗ[ℂ] R)
    (hd : ∀ A B, d (A*B)=d A*B+A*d B) (H U V : R)
    (huv : U*V=1) (hvu : V*U=1) (hV : d V=0) (hK : d (H*U-U*H)=0) :
    d (H*V-V*H)=0 := by
  rw [inverse_commutator H U V huv hvu]
  simp only [map_neg,hd,hV,hK,mul_zero,zero_mul,add_zero,neg_zero]

theorem inverse_ward_current (p g c : R →ₗ[ℂ] R) (γ : ℂ) (K : R)
    (hp : p K=0) (hg : g K=0) (hc : c K=(-6 : ℂ) • K) :
    inverseWard p g c γ K=0 := by
  have hlocal : inverseLocalPolynomial c K=0 := by
    simp only [inverseLocalPolynomial,hc,map_smul]
    module
  simp only [inverseWard,mixedPolynomial,hp,hg,hlocal,affinePolynomial,map_zero,
    smul_zero,sub_zero,add_zero]

private theorem inverse_ward_add (p g c : R →ₗ[ℂ] R) (γ : ℂ) (A B : R) :
    inverseWard p g c γ (A+B)=inverseWard p g c γ A+inverseWard p g c γ B := by
  simp only [inverseWard,mixedPolynomial,affinePolynomial,inverseLocalPolynomial,
    map_add,map_sub,map_smul,smul_add,smul_sub]
  module

private theorem inverse_ward_smul (p g c : R →ₗ[ℂ] R) (γ a : ℂ) (A : R) :
    inverseWard p g c γ (a • A)=a • inverseWard p g c γ A := by
  simp only [inverseWard,mixedPolynomial,affinePolynomial,inverseLocalPolynomial,
    map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul]
  module

/-- The inverse-volume symmetric action generates the inverse-weighted source Ward bulk.
The hypotheses are the original volume current and its three source weights, not a bulk witness. -/
theorem inverse_symmetric_ward (p g c : R →ₗ[ℂ] R) (γ : ℂ)
    (hp : ∀ A B, p (A*B)=p A*B+A*p B)
    (hg : ∀ A B, g (A*B)=g A*B+A*g B)
    (hc : ∀ A B, c (A*B)=c A*B+A*c B) (H U V : R)
    (huv : U*V=1) (hvu : V*U=1)
    (hpV : p V=0) (hgV : g V=0) (hcV : c V=(-3 : ℂ) • V)
    (hpK : p (H*U-U*H)=0) (hgK : g (H*U-U*H)=0) (hcK : c (H*U-U*H)=0) :
    inverseWard p g c γ ((1/2 : ℂ) • (H*V+V*H))=V*ward p g c γ H := by
  have hcurrent := inverse_ward_current p g c γ (H*V-V*H)
    (inverse_current_invariant p hp H U V huv hvu hpV hpK)
    (inverse_current_invariant g hg H U V huv hvu hgV hgK)
    (inverse_current_weight c hc H U V huv hvu hcV hcK)
  have hsplit : (1/2 : ℂ) • (H*V+V*H)=V*H+(1/2 : ℂ) • (H*V-V*H) := by module
  rw [hsplit,inverse_ward_add,inverse_ward_smul,hcurrent,smul_zero,add_zero]
  exact inverse_ward_mul p g c γ hp hg hc V H hpV hgV hcV

end LowEnergy.InverseVolumeWardAlgebra
