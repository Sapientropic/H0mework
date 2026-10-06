import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Parameter
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Contact

/-! The differentiable coframe Hamiltonian and the derivative-vertex contact
are read back to the complete original primal operator. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open DiracExteriorMatterAction StageNineCurrentCoframeMatterTemporalPrincipal StateGreen
noncomputable section
local instance sourceIndexDecidable : DecidableEq Quantum.Index := Classical.decEq _

theorem principal_inverse_original (e : LorentzianCoframe)
    (noncharacteristic : coframeTemporalPrincipalScalar e≠0) :
    Ring.inverse (principalMatrix e)=Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse e) := by
  have right : principalMatrix e*Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse e)=1 := by
    rw [principalMatrix,← Quantum.matrix_composition]
    have identity : (currentCoframeMatterTemporalPrincipal e).comp
        (currentCoframeMatterTemporalPrincipalInverse e)=1 := by
      apply LinearMap.ext
      intro v
      exact currentCoframeMatterTemporalPrincipalInverse_right e noncharacteristic v
    rw [identity,map_one]
  have left := Ring.inverse_mul_cancel (principalMatrix e) (principalMatrix_regular e noncharacteristic)
  calc
    _ = Ring.inverse (principalMatrix e)*(principalMatrix e*
        Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse e)) := by rw [right,mul_one]
    _ = _ := by rw [← mul_assoc,left,one_mul]

theorem hamiltonian_lower_original (C : StageNineHolonomicConfiguration) (point : BasePoint) (k : Fin 3 → ℝ)
    (noncharacteristic : coframeTemporalPrincipalScalar (C.coframe point)≠0) :
    hamiltonian C point k=(-Complex.I) •
      (currentCoframeMatterTemporalPrincipalInverse (C.coframe point)).comp (lowerSymbol C point k) := by
  apply LinearMap.ext
  intro v
  have original := full_temporal_equation C point k noncharacteristic v
  have expanded : currentCoframeMatterTemporalPrincipal (C.coframe point) (drift C point k v)+
      lowerSymbol C point k v=0 := by
    simp only [lowerSymbol,LinearMap.add_apply,LinearMap.comp_apply]
    rw [map_add] at original
    rw [add_assoc,add_comm
      (currentCoframeMatterTemporalPrincipal (C.coframe point) (connection C point 0 v))
      (knownSymbol C point k v)] at original
    exact original
  have divided := congrArg (currentCoframeMatterTemporalPrincipalInverse (C.coframe point)) expanded
  rw [map_add,map_zero,currentCoframeMatterTemporalPrincipalInverse_left _ noncharacteristic] at divided
  have velocity := eq_neg_of_add_eq_zero_left divided
  simp only [hamiltonian,LinearMap.smul_apply,LinearMap.comp_apply,velocity,smul_neg,neg_smul]

theorem coframeHamiltonian_original (point : BasePoint) (k : Fin 3 → ℝ) (e : LorentzianCoframe)
    (noncharacteristic : coframeTemporalPrincipalScalar e≠0) :
    coframeHamiltonian point k e=Quantum.operatorMatrix (hamiltonian (coframeConfiguration e) point k) := by
  have original := hamiltonian_lower_original (coframeConfiguration e) point k noncharacteristic
  conv_rhs => rw [original]
  simp only [coframeHamiltonian,timeSymbol,principal_inverse_original e noncharacteristic,
    lowerMatrix,map_smul,Quantum.matrix_composition]
  rfl

theorem coframeConfiguration_actual (point : BasePoint) :
    coframeConfiguration (actual.coframe point)=actual := by
  have same : (fun _ : BasePoint => actual.coframe point)=actual.coframe := by
    funext q
    rw [actual_coframe]
  unfold coframeConfiguration
  rw [same]

theorem coframeHamiltonian_actual (point : BasePoint) (k : Fin 3 → ℝ) :
    coframeHamiltonian point k (actual.coframe point)=Quantum.operatorMatrix (hamiltonian actual point k) := by
  rw [coframeHamiltonian_original _ _ _ (actual_noncharacteristic point),coframeConfiguration_actual]

theorem original_coframe_Dirac_contact (point : BasePoint) (k : Fin 3 → ℝ)
    (direction : LorentzianCoframe) (energy damping : ℝ) (positive : 0<damping) :
    let z := Retarded.spectralParameter energy damping
    let G := Quantum.operatorMatrix (Triangular.diracResolvent actual point k z)
    derivativeVertex (principalDirection point direction) (lowerDirection point k direction) z*G=
      onShellVertex (principalDirection point direction) (lowerDirection point k direction)
        (coframeHamiltonian point k (actual.coframe point))*G+
      principalDirection point direction*
        Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)) := by
  dsimp only
  rw [coframeHamiltonian_actual]
  exact original_Dirac_contact point k energy damping positive _ _

theorem original_hamiltonian_parameter (point : BasePoint) (k : Fin 3 → ℝ)
    (direction : LorentzianCoframe) :
    HasDerivAt (fun epsilon => Quantum.operatorMatrix
      (hamiltonian (coframeConfiguration (coframePath point direction epsilon)) point k))
      (hamiltonianDirection point k direction) 0 := by
  apply (coframeHamiltonian_parameter point k direction).congr_of_eventuallyEq
  filter_upwards [coframePath_eventually_noncharacteristic point direction] with epsilon regular
  exact (coframeHamiltonian_original point k (coframePath point direction epsilon) regular).symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
