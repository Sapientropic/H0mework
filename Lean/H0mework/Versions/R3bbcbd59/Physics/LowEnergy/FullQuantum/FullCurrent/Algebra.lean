import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Source

/-! Both independent Euler equations generate the two ordered current legs.
Inverse-domain hypotheses are algebraic regularity, not response certificates. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrent
open DiracExteriorMatterAction
noncomputable section

def primalResponse (scale : ℂ) (G V : Mother) (psi : DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier :=
  -scale • G (V psi)

def dualResponse (scale : ℂ) (chi : Module.Dual ℂ DiracExteriorMatterCarrier) (V G : Mother) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  -scale • chi.comp (V.comp G)

theorem primalResponse_equation (scale : ℂ) (D G V : Mother) (psi : DiracExteriorMatterCarrier)
    (rightInverse : D*G=1) : D (primalResponse scale G V psi)=-scale • V psi := by
  have inverse := congrArg (fun A : Mother => A (V psi)) rightInverse
  simp only [Module.End.mul_apply,Module.End.one_apply] at inverse
  simp only [primalResponse,map_smul,inverse]

theorem dualResponse_equation (scale : ℂ) (D G V : Mother)
    (chi : Module.Dual ℂ DiracExteriorMatterCarrier) (v : DiracExteriorMatterCarrier)
    (leftInverse : G*D=1) : dualResponse scale chi V G (D v)=-scale*chi (V v) := by
  have inverse := congrArg (fun A : Mother => A v) leftInverse
  simp only [Module.End.mul_apply,Module.End.one_apply] at inverse
  simp only [dualResponse,LinearMap.smul_apply,LinearMap.comp_apply,inverse,smul_eq_mul]

def responseInsertion (scale : ℂ) (Bplus Czero Cminus Bzero Gplus Gminus J : Mother) : Mother :=
  -scale • (Bplus*Gplus*Czero+Cminus*Gminus*Bzero)+J

theorem independent_current_substitution (scale : ℂ)
    (chi : Module.Dual ℂ DiracExteriorMatterCarrier) (psi : DiracExteriorMatterCarrier)
    (Bplus Czero Cminus Bzero Gplus Gminus J : Mother) :
    chi (Bplus (primalResponse scale Gplus Czero psi))+
      dualResponse scale chi Cminus Gminus (Bzero psi)+chi (J psi)=
      chi (responseInsertion scale Bplus Czero Cminus Bzero Gplus Gminus J psi) := by
  simp only [primalResponse,dualResponse,responseInsertion,LinearMap.smul_apply,
    LinearMap.comp_apply,LinearMap.add_apply,Module.End.mul_apply,map_smul,map_add,smul_eq_mul]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrent
