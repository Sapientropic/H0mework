import H0mework.Physics.LowEnergyFockDynamics.Algebra
import H0mework.Physics.LowEnergyFockDynamics.Response

/-! Wave-function CAR and one-occupation matrix elements in the original finite Fock carrier. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
open QuantizationCheck.Fermion Fermion
open scoped BigOperators Matrix
noncomputable section
variable {m : Type*} [Fintype m] [LinearOrder m]

def annihilator (u : m → ℂ) : Module.End ℂ (Fock m) := ∑ i, star (u i) • annihilation i

theorem wave_annihilation_car (u v : m → ℂ) :
    annihilator u * annihilator v+annihilator v * annihilator u=0 := by
  simp only [annihilator,Finset.sum_mul,Finset.mul_sum,smul_mul_smul]
  rw [Finset.sum_comm (f := fun i j => (star (v j)*star (u i)) • (annihilation j*annihilation i))]
  simp_rw [mul_comm (star (v _))]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib,← smul_add,operator_annihilation_car,smul_zero]
  simp

theorem wave_creation_car (u v : m → ℂ) :
    waveCreation u * waveCreation v+waveCreation v * waveCreation u=0 := by
  have native (i j : m) : creation i * creation j+creation j * creation i=0 := by
    apply LinearMap.ext
    intro ψ
    exact create_create_car i j ψ
  simp only [waveCreation,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_mul,Finset.mul_sum,smul_mul_smul]
  rw [Finset.sum_comm (f := fun i j => (v j*u i) • (creation j*creation i))]
  simp_rw [mul_comm (v _)]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib,← smul_add,native,smul_zero]
  simp

theorem wave_car (u v : m → ℂ) :
    annihilator u * waveCreation v+waveCreation v * annihilator u=
      modePair u v • (1 : Module.End ℂ (Fock m)) := by
  have generated := field_car (fun (_ : Unit) i => star (u i))
    (fun (_ : Unit) i => star (v i)) () ()
  change _=(∑ i, star (u i)*star (star (v i))) • (1 : Module.End ℂ (Fock m)) at generated
  simpa only [annihilationField,creationField,star_star,waveCreation,LinearMap.coe_mk,
    AddHom.coe_mk,annihilator,modePair] using generated

theorem annihilator_vacuum (u : m → ℂ) : annihilator u vacuum=0 := by
  simp [annihilator]

theorem annihilator_oneParticle (u v : m → ℂ) :
    annihilator u (oneParticle v)=modePair u v • vacuum := by
  ext occupied
  simp only [annihilator,LinearMap.sum_apply,LinearMap.smul_apply,annihilation_apply,
    annihilate_oneParticle,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,modePair,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)

theorem wave_empty (u : m → ℂ) (ψ : Fock m) : waveCreation u ψ ∅=0 := by
  simp [waveCreation,create]

theorem pairing_oneParticle_wave (w u : m → ℂ) (ψ : Fock m) :
    pairing (oneParticle w) (waveCreation u ψ)=modePair w u*ψ ∅ := by
  rw [pairing_oneParticle_left]
  simp only [waveCreation,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.sum_apply,
    LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,creation_apply,
    create_singleton,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  simp only [modePair,Finset.sum_mul,mul_assoc]

theorem creation_annihilation_oneParticle (u v w : m → ℂ) :
    (waveCreation u * annihilator v) (oneParticle w)=modePair v w • oneParticle u := by
  rw [Module.End.mul_apply,annihilator_oneParticle,map_smul,waveCreation_vacuum]

theorem occupation_twoPoint (u v w : m → ℂ) :
    pairing (oneParticle w) ((waveCreation u * annihilator v) (oneParticle w))=
      modePair v w*modePair w u := by
  rw [creation_annihilation_oneParticle,pairing_smul_right,pairing_oneParticle]
  rfl

theorem occupation_fourPoint (u v x y w : m → ℂ) :
    pairing (oneParticle w)
      ((waveCreation u * annihilator v * waveCreation x * annihilator y) (oneParticle w))=
      modePair v x*modePair y w*modePair w u := by
  have regroup : waveCreation u * annihilator v * waveCreation x * annihilator y=
      (waveCreation u * annihilator v)*(waveCreation x * annihilator y) := by
    simp only [mul_assoc]
  rw [regroup,Module.End.mul_apply,creation_annihilation_oneParticle,map_smul,
    creation_annihilation_oneParticle,pairing_smul_right,pairing_smul_right,pairing_oneParticle]
  change modePair y w*(modePair v x*modePair w u)=_
  ring

theorem occupation_normal_fourPoint (u v x y w : m → ℂ) :
    (waveCreation u * waveCreation v * annihilator x * annihilator y) (oneParticle w)=0 := by
  simp only [Module.End.mul_apply,annihilator_oneParticle,map_smul,annihilator_vacuum,
    smul_zero,map_zero]

theorem annihilator_wave (u v : m → ℂ) (ψ : Fock m) :
    annihilator u (waveCreation v ψ)=modePair u v • ψ-waveCreation v (annihilator u ψ) := by
  have identity := congrArg (fun op : Module.End ℂ (Fock m) => op ψ) (wave_car u v)
  simp only [LinearMap.add_apply,Module.End.mul_apply,LinearMap.smul_apply,Module.End.one_apply] at identity
  exact eq_sub_of_add_eq identity

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
