import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.FullCurrent.Transfer
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.FullCurrent.Algebra
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Boundary

/-! The full response word is read with the original independent dual and its
C0-weighted initial momentum. No positive adjoint or replacement state enters. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrent
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open Stage9C.Dynamics.Homogeneous StageNineCurrentCoframeMatterTemporalPrincipal
open DiracExteriorMatterAction CoframeResponse StateGreen StateResponse
open QuantizationCheck.Fermion Fermion YangMills.FullPairing
noncomputable section
local instance sourceIndex : DecidableEq Quantum.Index := Classical.decEq _
attribute [local instance] transferIndexOrder

def originalBoundary (point : BasePoint) : SourceMatrix := Quantum.operatorMatrix (boundaryWeight actual point)
def originalPrincipalInverse (point : BasePoint) : SourceMatrix :=
  Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))

theorem original_pair_boundary (point : BasePoint) (A : Mother) :
    (lapse : ℂ)*actual.conjugateMatter point (A (actual.matter point))=
      (4*Complex.I)*modePair (preparedVector point)
        ((originalBoundary point*originalPrincipalInverse point*Quantum.operatorMatrix A)*ᵥpreparedVector point) := by
  let CI := currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)
  let K := boundaryWeight actual point
  have generated := boundaryWeight_original actual point (CI (A (actual.matter point)))
  simp only [normalizedMomentum,LinearMap.smul_apply,LinearMap.comp_apply,CI,
    currentCoframeMatterTemporalPrincipalInverse_right _ (actual_noncharacteristic point),smul_eq_mul] at generated
  rw [actual_coframe,homogeneousCoframe_det,abs_of_pos lapse_pos] at generated
  have normalized : actual.matter point=(2 : ℂ) • preparedMatter point := by
    simp [preparedMatter,smul_smul]
  have pair : Quantum.coordinatePair (actual.matter point) (K (CI (A (actual.matter point))))=
      4*modePair (preparedVector point)
        ((originalBoundary point*originalPrincipalInverse point*Quantum.operatorMatrix A)*ᵥpreparedVector point) := by
    rw [normalized,map_smul,map_smul,map_smul,Quantum.coordinatePair_smul]
    norm_num
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
    simp only [originalBoundary,originalPrincipalInverse,preparedVector,Quantum.matrix_action]
    rfl
  change (-Complex.I*(lapse : ℂ))*actual.conjugateMatter point (A (actual.matter point))=
    Quantum.coordinatePair (actual.matter point) (K (CI (A (actual.matter point)))) at generated
  rw [pair] at generated
  linear_combination (norm := (ring_nf; simp [Complex.I_sq])) Complex.I * generated

def nativeResponseWord (point : BasePoint) (Bplus Czero Cminus Bzero Gplus Gminus J : Mother) :
    Module.End ℂ (Fock (Fin 3×Quantum.Index)) :=
  fullResponseWord (lapse : ℂ)⁻¹ (originalBoundary point) (originalPrincipalInverse point)
    (Quantum.operatorMatrix Bplus) (Quantum.operatorMatrix Czero)
    (Quantum.operatorMatrix Cminus) (Quantum.operatorMatrix Bzero)
    (Quantum.operatorMatrix Gplus) (Quantum.operatorMatrix Gminus) (Quantum.operatorMatrix J)

theorem original_response_native (point : BasePoint) (Bplus Czero Cminus Bzero Gplus Gminus J : Mother) :
    (lapse : ℂ)*(actual.conjugateMatter point (Bplus (primalResponse (lapse : ℂ)⁻¹ Gplus Czero (actual.matter point)))+
      dualResponse (lapse : ℂ)⁻¹ (actual.conjugateMatter point) Cminus Gminus (Bzero (actual.matter point))+
      actual.conjugateMatter point (J (actual.matter point)))=
      (4*Complex.I)*transferNativeRead point (nativeResponseWord point Bplus Czero Cminus Bzero Gplus Gminus J) := by
  rw [independent_current_substitution,transferNativeRead_generated,nativeResponseWord,fullResponseWord_read]
  have generated := original_pair_boundary point (responseInsertion (lapse : ℂ)⁻¹ Bplus Czero Cminus Bzero Gplus Gminus J)
  simpa only [responseInsertion,map_add,map_smul,map_mul] using generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrent
