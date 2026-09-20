import H0mework.Physics.LowEnergyMatterSpace.PreparationState
import H0mework.Physics.LowEnergyMatterSpace.GaugeForce

/-! Native P286 force channels and L² controls generate the preparation history; no wavepacket is supplied. -/
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open SU7MotherLieAlgebra DiracCliffordRepresentation
noncomputable section
variable {ι : Type*} [Fintype ι]

abbrev ControlFiber := EuclideanSpace ℂ ι
abbrev ControlL2 := Lp (α := Position) (ControlFiber (ι := ι)) 2 volume

def channelLinear (channels : ι → MatterFiber →L[ℂ] MatterFiber) :
    ControlFiber (ι := ι) →ₗ[ℂ] MatterFiber →L[ℂ] MatterFiber where
  toFun values := ∑ i, values i • channels i
  map_add' u v := by
    ext w j
    simp [PiLp.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c u := by
    ext w j
    simp [PiLp.smul_apply,Finset.mul_sum,mul_assoc]

def channelCoefficient (channels : ι → MatterFiber →L[ℂ] MatterFiber) :
    MatterFiber →L[ℂ] ControlFiber (ι := ι) →L[ℂ] MatterFiber :=
  channelLinear channels |>.toContinuousLinearMap |>.flip

theorem channelCoefficient_apply (channels : ι → MatterFiber →L[ℂ] MatterFiber)
    (u : MatterFiber) (values : ControlFiber (ι := ι)) :
    channelCoefficient channels u values=∑ i, values i • channels i u := by
  simp [channelCoefficient,channelLinear]

def gaugeCoefficient (data : ι → LorentzianIndex → P286LieBlockData) :
    MatterFiber →L[ℂ] ControlFiber (ι := ι) →L[ℂ] MatterFiber :=
  channelCoefficient (fun i => gaugeForceOperator (data i))

def gaugePreparationMap (data : ι → LorentzianIndex → P286LieBlockData)
    (profile : ℝ → ControlL2 (ι := ι)) (continuousProfile : Continuous profile) (t : ℝ) :
    MatterFiber →L[ℂ] MatterL2 :=
  controlledPreparationMap (gaugeCoefficient data) profile continuousProfile t

theorem gauge_control_force_ae (data : ι → LorentzianIndex → P286LieBlockData)
    (profile : ℝ → ControlL2 (ι := ι)) (t : ℝ) (u : MatterFiber) :
    controlHistory (gaugeCoefficient data) profile t u=ᵐ[volume]
      fun x => ∑ i, profile t x i • gaugeForceOperator (data i) u := by
  have original := controlHistory_ae (gaugeCoefficient data) profile t u
  simpa only [gaugeCoefficient,channelCoefficient_apply] using original

theorem gaugePreparationMap_duhamel (data : ι → LorentzianIndex → P286LieBlockData)
    (profile : ℝ → ControlL2 (ι := ι)) (continuousProfile : Continuous profile) (t : ℝ) (u : MatterFiber) :
    gaugePreparationMap data profile continuousProfile t u=
      duhamel (fun s => sourceInjection (gaugeCoefficient data u) (profile s)) t := rfl

theorem gaugePreparationMap_interaction_derivative (data : ι → LorentzianIndex → P286LieBlockData)
    (profile : ℝ → ControlL2 (ι := ι)) (continuousProfile : Continuous profile) (t : ℝ) (u : MatterFiber) :
    HasDerivAt (fun s => spatialUnitary (-s) (gaugePreparationMap data profile continuousProfile s u))
      (spatialUnitary (-t) (sourceInjection (gaugeCoefficient data u) (profile t))) t :=
  injected_duhamel_derivative (gaugeCoefficient data u) profile continuousProfile t

theorem gaugePreparationMap_bound (data : ι → LorentzianIndex → P286LieBlockData)
    (profile : ℝ → ControlL2 (ι := ι)) (continuousProfile : Continuous profile) (t : ℝ) :
    ‖gaugePreparationMap data profile continuousProfile t‖≤
      preparationBound (controlHistory (gaugeCoefficient data) profile) t :=
  preparationMap_norm _ (controlHistory_continuous (gaugeCoefficient data) profile continuousProfile) t

def gaugePreparedFunctional (data : ι → LorentzianIndex → P286LieBlockData)
    (profile : ℝ → ControlL2 (ι := ι)) (continuousProfile : Continuous profile) (t : ℝ) :
    (MatterL2 →L[ℂ] MatterL2) →ₚ[ℂ] ℂ :=
  normalizedFunctional (controlHistory (gaugeCoefficient data) profile)
    (controlHistory_continuous (gaugeCoefficient data) profile continuousProfile) t

theorem gauge_history_prepares_nonempty (data : ι → LorentzianIndex → P286LieBlockData)
    (profile : ℝ → ControlL2 (ι := ι)) (continuousProfile : Continuous profile) (atTime : ℝ)
    (nonzero : sourceInjection (gaugeCoefficient data sourcePrepared) (profile atTime)≠0) :
    ∃ t, gaugePreparedFunctional data profile continuousProfile t 1=1 := by
  obtain ⟨t,unit,_⟩ := source_history_generates_normalized_state
    (controlHistory (gaugeCoefficient data) profile)
    (controlHistory_continuous (gaugeCoefficient data) profile continuousProfile) atTime nonzero
  exact ⟨t,unit⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
