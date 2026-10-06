import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeAlgebra

set_option autoImplicit false
noncomputable section
namespace LowEnergy.InverseVolumeInsertionAlgebra
open InverseVolumeWardAlgebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem weight_one (p g c : R →ₗ[ℂ] R) (γ : ℂ) (Y : R)
    (hp : p Y=Y) (hg : g Y=0) (hc : c Y=0) :
    inverseWard p g c γ Y=(4 : ℂ) • Y := by
  have hlocal : inverseLocalPolynomial c Y=(48 : ℂ) • Y := by
    simp [inverseLocalPolynomial,hc]
  have hmixed : mixedPolynomial p g Y=(4 : ℂ) • Y := by
    simp [mixedPolynomial,hp,hg]
  rw [inverseWard,hlocal,hmixed]
  simp only [affinePolynomial,map_smul,hp]
  module

/-- The full inverse-volume Ward keeps a nonzero source insertion coefficient
and exactly the first two literal cutoff jets. -/
theorem source_cutoff_word (p g c : R →ₗ[ℂ] R) (γ : ℂ)
    (hp : ∀ A B,p (A*B)=p A*B+A*p B)
    (hg : ∀ A B,g (A*B)=g A*B+A*g B)
    (hc : ∀ A B,c (A*B)=c A*B+A*c B)
    (Y T : R) (hpY : p Y=Y) (hgY : g Y=0) (hcY : c Y=0)
    (hgT : g T=0) (hcT : c T=0) (hgPT : g (p T)=0) :
    inverseWard p g c γ (Y*T)=
      (4 : ℂ) • (Y*T)+(4-48*γ : ℂ) • (Y*p T)+
        (48*γ : ℂ) • (Y*p (p T)) := by
  have hp1 : p (Y*T)=Y*T+Y*p T := by rw [hp,hpY]
  have hp2 : p (p (Y*T))=Y*T+(2 : ℂ) • (Y*p T)+Y*p (p T) := by
    rw [hp1,map_add,hp,hp,hpY]
    module
  have hg0 : g (Y*T)=0 := by rw [hg,hgY,hgT,zero_mul,mul_zero,add_zero]
  have hg1 : g (p (Y*T))=0 := by
    rw [hp1,map_add,hg0,hg,hgY,hgPT,zero_mul,mul_zero,add_zero,add_zero]
  have hc0 : c (Y*T)=0 := by rw [hc,hcY,hcT,zero_mul,mul_zero,add_zero]
  have hlocal : inverseLocalPolynomial c (Y*T)=(48 : ℂ) • (Y*T) := by
    simp [inverseLocalPolynomial,hc0]
  have hmixed : mixedPolynomial p g (Y*T)=(4 : ℂ) • p (Y*T) := by
    simp [mixedPolynomial,hg0,hg1]
  rw [inverseWard,hlocal,hmixed]
  simp only [affinePolynomial,map_smul]
  rw [hp2,hp1]
  module

end LowEnergy.InverseVolumeInsertionAlgebra
