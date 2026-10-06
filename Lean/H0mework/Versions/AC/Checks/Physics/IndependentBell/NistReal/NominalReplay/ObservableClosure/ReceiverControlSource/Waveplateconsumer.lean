import H0mework.Versions.AC.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.ReceiverControlSource.Waveplatesource
import H0mework.Versions.AC.Checks.Physics.IndependentBell.NistReal.NominalReplay.GaussianWindow.NativeEffects.Detectorgamma

set_option autoImplicit false

namespace P23.ReceiverControl.Consumer

open Matrix P23.GaussianWindow.NativeEffects
open scoped BigOperators
noncomputable section

def born (rho effect : Jones) : ℝ := (rho*effect).trace.re

theorem actual_pose_born (p : Pose) (rho : Jones) :
    born rho (nativeEffect p)=born rho (rankOne (analyzer (effectiveAngle p))) ∧
    born (transported rho) (transported (nativeEffect p))=
      born (transported rho) (rankOne (codeAnalyzer (effectiveAngle p))) ∧
    born (transported rho) (transported (nativeEffect p))=born rho (nativeEffect p) := by
  refine ⟨by rw [native_effective_projector],?_,?_⟩
  · rw [transported,signed_effect]
  · unfold born
    rw [transport_born]

theorem finite_source_born {K : Type*} [Fintype K] (p : Pose) (phi : K → Polarization) :
    (∑ k, (star (phi k) ⬝ᵥ (nativeEffect p *ᵥ phi k)).re)=
      ∑ k, (star (phi k) ⬝ᵥ (rankOne (analyzer (effectiveAngle p)) *ᵥ phi k)).re := by
  rw [native_effective_projector]

def boolIndex (p : Bool) : Fin 2 := if p then 0 else 1
def booleanEffect (p : Pose) : Matrix Bool Bool ℂ := (nativeEffect p).submatrix boolIndex boolIndex

theorem actual_bool_projector (p : Pose) :
    booleanEffect p=vecMulVec (analyzerVector (effectiveAngle p)) (star (analyzerVector (effectiveAngle p))) := by
  rw [booleanEffect,native_effective_projector]
  ext i j
  cases i <;> cases j <;>
    simp [boolIndex,rankOne,analyzer,analyzerVector,vecMulVec]

theorem actual_one_photon_feed (d : DetectorPrim) (p : Pose) :
    1-transmissionRoot d*booleanEffect p*transmissionRoot d=onePhotonEffect d (effectiveAngle p) := by
  rw [actual_bool_projector,onePhoton_form]

theorem actual_all_sector_feed (d : DetectorPrim) (p : Pose) :
    ∀ n : ℕ,
      (occupation n)ᴴ*wordTensor
        (1-transmissionRoot d*booleanEffect p*transmissionRoot d) n*occupation n=
      gamma d (effectiveAngle p) n := by
  intro n
  rw [actual_one_photon_feed]
  rfl

theorem waveplate_source_effect_consumer (p : Pose) :
    nativeEffect p=rankOne (analyzer (effectiveAngle p)) ∧
    (∀ rho : Jones, born rho (nativeEffect p)=born rho (rankOne (analyzer (effectiveAngle p)))) ∧
    (∀ d : DetectorPrim, ∀ n : ℕ,
      (occupation n)ᴴ*wordTensor
        (1-transmissionRoot d*booleanEffect p*transmissionRoot d) n*occupation n=
      gamma d (effectiveAngle p) n) := by
  exact ⟨native_effective_projector p,fun rho => (actual_pose_born p rho).1,
    fun d => actual_all_sector_feed d p⟩

end
end P23.ReceiverControl.Consumer
