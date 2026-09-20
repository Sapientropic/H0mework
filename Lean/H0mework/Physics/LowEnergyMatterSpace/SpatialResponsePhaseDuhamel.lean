import H0mework.Physics.LowEnergyMatterSpace.SpatialResponsePhaseKubo

/-! The actual original-clock retarded integral is the phase readback of the generated spatial response. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.ResponsePhase
open _root_.SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open SU7MotherLieAlgebra DiracCliffordRepresentation
noncomputable section

def originalLocalForce (profile : ℝ → BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (u : MatterL2) (s : ℝ) : MatterL2 :=
  (-Complex.I) • localGaugeHamiltonian (profile s) data (originalSpatialUnitary s u)

theorem originalLocalForce_readback (profile : ℝ → BoundedProfile)
    (data : LorentzianIndex → P286LieBlockData) (u : MatterL2) (s : ℝ) :
    originalLocalForce profile data u s=
      phaseRead s (perturbationForce (fun r => localGaugeHamiltonian (profile r) data) u s) := by
  rw [originalLocalForce,originalSpatialUnitary_readback,← localGauge_phase]
  simp only [perturbationForce,map_smul]

def originalLocalFirstOrder (profile : ℝ → BoundedProfile)
    (data : LorentzianIndex → P286LieBlockData) (t : ℝ) (u : MatterL2) : MatterL2 :=
  ∫ s in (0 : ℝ)..t, originalSpatialUnitary (t-s) (originalLocalForce profile data u s)

theorem original_retarded_integrand (profile : ℝ → BoundedProfile)
    (data : LorentzianIndex → P286LieBlockData) (u : MatterL2) (t s : ℝ) :
    originalSpatialUnitary (t-s) (originalLocalForce profile data u s)=
      phaseRead t (spatialUnitary (t-s)
        (perturbationForce (fun r => localGaugeHamiltonian (profile r) data) u s)) := by
  rw [originalLocalForce_readback,originalSpatialUnitary_readback,← spatialUnitary_phase,
    ← phaseRead_add,sub_add_cancel]

theorem originalLocalFirstOrder_readback (profile : ℝ → BoundedProfile)
    (continuousProfile : Continuous profile) (data : LorentzianIndex → P286LieBlockData)
    (t : ℝ) (u : MatterL2) :
    originalLocalFirstOrder profile data t u=
      phaseRead t (firstOrder (fun r => localGaugeHamiltonian (profile r) data) t u) := by
  let force := perturbationForce (fun r => localGaugeHamiltonian (profile r) data) u
  have continuousForce : Continuous force := perturbationForce_continuous _
    (localGaugeHistory_continuous profile continuousProfile data) u
  have continuousIntegrand : Continuous (fun s => spatialUnitary (t-s) (force s)) := by
    have composed := spatialUnitary_joint.comp
      (((continuous_const : Continuous (fun _ : ℝ => t)).sub continuous_id).prodMk continuousForce)
    simpa only [Function.comp_def,Pi.sub_apply,id_eq] using composed
  have retarded := duhamel_retarded_integral force continuousForce t
  change firstOrder (fun r => localGaugeHamiltonian (profile r) data) t u=
    ∫ s in (0 : ℝ)..t, spatialUnitary (t-s) (force s) at retarded
  calc
    _ = ∫ s in (0 : ℝ)..t, phaseRead t (spatialUnitary (t-s) (force s)) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact original_retarded_integrand profile data u t s
    _ = phaseRead t (∫ s in (0 : ℝ)..t, spatialUnitary (t-s) (force s)) :=
      (phaseRead t).intervalIntegral_comp_comm (continuousIntegrand.intervalIntegrable (μ := volume) 0 t)
    _ = _ := by rw [← retarded]

def originalLocalVariation (profile : ℝ → BoundedProfile)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (currentData : LorentzianIndex → P286LieBlockData) (u : MatterL2) (t : ℝ) : ℂ :=
  inner ℂ (originalLocalFirstOrder profile forceData t u)
      (localCurrentOperator detector currentData (originalSpatialUnitary t u))+
    inner ℂ (originalSpatialUnitary t u)
      (localCurrentOperator detector currentData (originalLocalFirstOrder profile forceData t u))

theorem originalLocalVariation_readback (profile : ℝ → BoundedProfile)
    (continuousProfile : Continuous profile) (forceData : LorentzianIndex → P286LieBlockData)
    (detector : BoundedProfile) (currentData : LorentzianIndex → P286LieBlockData) (u : MatterL2) (t : ℝ) :
    originalLocalVariation profile forceData detector currentData u t=
      currentVariation (fun r => localGaugeHamiltonian (profile r) forceData)
        (localCurrentOperator detector currentData) u t := by
  rw [originalLocalVariation,originalLocalFirstOrder_readback profile continuousProfile,
    originalSpatialUnitary_readback,localCurrent_phase_pair,localCurrent_phase_pair]
  rfl

theorem originalLocalVariation_kubo (profile : ℝ → BoundedProfile)
    (continuousProfile : Continuous profile)
    (realProfile : ∀ s, ∀ᵐ x ∂volume, star (profile s x)=profile s x)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (currentData : LorentzianIndex → P286LieBlockData) (u : MatterL2) (t : ℝ) :
    originalLocalVariation profile forceData detector currentData u t=
      Complex.I*∫ s in (0 : ℝ)..t, originalKuboKernel
        (fun r => localGaugeHamiltonian (profile r) forceData) (localCurrentOperator detector currentData) u t s := by
  rw [originalLocalVariation_readback profile continuousProfile,
    currentVariation_kubo _ (localGaugeHistory_continuous profile continuousProfile forceData)
      (fun s => localGaugeHamiltonian_selfAdjoint (profile s) (realProfile s) forceData)]
  simp_rw [local_originalKuboKernel]

theorem prepared_originalFree_readback (u : MatterL2) (preparedAt t : ℝ) :
    originalSpatialUnitary t (phaseRead preparedAt u)=phaseRead (t+preparedAt) (spatialUnitary t u) := by
  rw [originalSpatialUnitary_readback,← spatialUnitary_phase,← phaseRead_add]

theorem originalPreparedVariation_kubo (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (profile : ℝ → BoundedProfile) (continuousProfile : Continuous profile)
    (realProfile : ∀ s, ∀ᵐ x ∂volume, star (profile s x)=profile s x)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (currentData : LorentzianIndex → P286LieBlockData) (t : ℝ) :
    originalLocalVariation profile forceData detector currentData
      (phaseRead preparedAt (normalizedPreparation preparation continuousPreparation preparedAt)) t=
      Complex.I*∫ s in (0 : ℝ)..t,
        kuboKernel (fun r => localGaugeHamiltonian (profile r) forceData)
          (localCurrentOperator detector currentData)
          (normalizedPreparation preparation continuousPreparation preparedAt) t s := by
  rw [originalLocalVariation_kubo profile continuousProfile realProfile]
  simp_rw [originalKernel_prepared_readback]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.ResponsePhase
