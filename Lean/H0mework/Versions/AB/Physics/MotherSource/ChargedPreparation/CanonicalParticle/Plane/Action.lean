import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Plane.Dynamics

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility YangMills.FullPairing
open LowEnergy.FullQuantum StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeMotherAction LowEnergy.FiniteKernel
noncomputable section
attribute [local irreducible] Stage10.Runtime.source Stage10.Runtime.configuration

theorem covariant_time (momentum : Fin 3 → ℝ) (point : BasePoint) :
    holonomicMatterCovariantDerivative (fields momentum) point 0 =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative (fields momentum) point := by
  unfold holonomicMatterCovariantDerivative
  rw [original_action_time_velocity]
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
  simp [StageNineP286ActionCauchySplit.canonicalLorentzianTimeDirection,
    StageNineCurrentCoframeMatterTimeResponse.holonomicMatterConnectionAction]
  abel

theorem dirac_vector_zero (momentum : Fin 3 → ℝ) (point : BasePoint) :
    generatedContinuumDiracDualMatterVector Stage10.Runtime.source 0 point
      (toContinuumPointField (fields momentum) point) = 0 := by
  apply generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
  change HolonomicDiracDualCurrentCoframeMatterTimeActionLaw (fields momentum) point
    (holonomicMatterCovariantDerivative (fields momentum) point 0)
  rw [covariant_time]
  apply actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
  change StageNineCurrentCoframeMatterTemporalPrincipal.coframeTemporalPrincipalScalar
    (Stage10.Runtime.configuration.coframe point) ≠ 0
  rw [Stage10.Runtime.configuration_eq]
  exact actual_noncharacteristic point

theorem dirac_density_zero (momentum : Fin 3 → ℝ) (point : BasePoint) :
    generatedDensitizedContinuumDiracDualMatterDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (fields momentum) point) = 0 := by
  have zero := dirac_vector_zero momentum point
  rw [Stage10.Runtime.source_eq] at zero ⊢
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing, zero]
  simp

def reference : StageNineHolonomicConfiguration :=
  configuration Stage10.Runtime.configuration (modes 0) (fun _ : Unit => 0) (fun _ : Unit => 0)

theorem reference_smooth : reference.Smooth := by
  rcases actual_smooth with ⟨coframe,gravity,gravityAux,multiplier,gauge,gaugeAux,scalar,_,_⟩
  rw [reference, Stage10.Runtime.configuration_eq]
  refine ⟨coframe,gravity,gravityAux,multiplier,gauge,gaugeAux,scalar,?_,?_⟩
  · exact profile_smooth (modes 0) _
  · intro index
    exact dualProfile_smooth (modes 0) _ _

theorem reference_density_zero (point : BasePoint) :
    generatedDensitizedContinuumDiracDualMatterDensity Stage10.Runtime.source 0 point
      (toContinuumPointField reference point) = 0 := by
  rw [Stage10.Runtime.source_eq, generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing]
  simp [toContinuumPointField, reference, configuration, dualProfile]

theorem complete_density_equal (momentum : Fin 3 → ℝ) (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (fields momentum) point) =
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
      (toContinuumPointField reference point) := by
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary generatedDiracDualFormNativeMatterDensity
  rw [dirac_density_zero, reference_density_zero]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
