import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Principal
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Retarded.Original

/-! A time-derivative vertex hitting the genuine source Dirac Green generates
its local principal contact. Positive damping supplies the inverse domain. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open DiracExteriorMatterAction StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def derivativeVertex (dPrincipal dLower : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  dLower-(Complex.I*z) • dPrincipal

def onShellVertex (dPrincipal dLower H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  dLower-Complex.I • (dPrincipal*H)

theorem derivativeVertex_split (dPrincipal dLower H : Matrix ι ι ℂ) (z : ℂ) :
    derivativeVertex dPrincipal dLower z=onShellVertex dPrincipal dLower H-
      Complex.I • (dPrincipal*(z • (1 : Matrix ι ι ℂ)-H)) := by
  simp only [derivativeVertex,onShellVertex,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,
    smul_sub,smul_smul]
  module

theorem derivativeVertex_contact (dPrincipal dLower H R principalInverse : Matrix ι ι ℂ)
    (z : ℂ) (inverse : (z • (1 : Matrix ι ι ℂ)-H)*R=1) :
    derivativeVertex dPrincipal dLower z*(Complex.I • (R*principalInverse))=
      onShellVertex dPrincipal dLower H*(Complex.I • (R*principalInverse))+
        dPrincipal*principalInverse := by
  rw [derivativeVertex_split]
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_smul]
  have collapse : (dPrincipal*(z • (1 : Matrix ι ι ℂ)-H))*(R*principalInverse)=
      dPrincipal*principalInverse := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc (z • (1 : Matrix ι ι ℂ)-H),inverse,Matrix.one_mul]
  rw [collapse]
  simp only [smul_sub,smul_smul,Complex.I_mul_I,neg_one_smul,sub_neg_eq_add]

local instance contactIndexDecidable : DecidableEq Quantum.Index := Classical.decEq _

theorem original_Dirac_contact (point : BasePoint) (k : Fin 3 → ℝ) (energy damping : ℝ)
    (positive : 0<damping) (dPrincipal dLower : Matrix Quantum.Index Quantum.Index ℂ) :
    let z := Retarded.spectralParameter energy damping
    let G := Quantum.operatorMatrix (Triangular.diracResolvent actual point k z)
    derivativeVertex dPrincipal dLower z*G=
      onShellVertex dPrincipal dLower (Quantum.operatorMatrix (hamiltonian actual point k))*G+
        dPrincipal*Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)) := by
  dsimp only
  have regular := Retarded.sourceFree_regular point k energy damping positive
  have two := (Triangular.fullResolvent_two_sided actual point k
    (Retarded.spectralParameter energy damping) regular).1
  have inverse : (Retarded.spectralParameter energy damping • (1 : Matrix Quantum.Index Quantum.Index ℂ)-
      Quantum.operatorMatrix (hamiltonian actual point k))*
      Quantum.operatorMatrix (Triangular.fullResolvent actual point k (Retarded.spectralParameter energy damping))=1 := by
    have mapped := congrArg Quantum.operatorMatrix two
    unfold Triangular.fullKernel at mapped
    rw [map_mul] at mapped
    have subtraction := Quantum.operatorMatrix.toLinearEquiv.map_sub
      (Retarded.spectralParameter energy damping • (1 : Mother)) (hamiltonian actual point k)
    change Quantum.operatorMatrix (Retarded.spectralParameter energy damping • (1 : Mother)-hamiltonian actual point k)=
      Quantum.operatorMatrix (Retarded.spectralParameter energy damping • (1 : Mother))-
        Quantum.operatorMatrix (hamiltonian actual point k) at subtraction
    rw [subtraction,map_smul,map_one] at mapped
    exact mapped
  have generated := derivativeVertex_contact dPrincipal dLower (Quantum.operatorMatrix (hamiltonian actual point k))
    (Quantum.operatorMatrix (Triangular.fullResolvent actual point k (Retarded.spectralParameter energy damping)))
    (Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)))
    (Retarded.spectralParameter energy damping) inverse
  simpa only [Triangular.diracResolvent,map_smul,map_mul] using generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
