import H0mework.Physics.LowEnergyMatterSpace.PerturbedPhase
import H0mework.Physics.LowEnergyMatterSpace.PerturbedVariationCurrent

/-! The actual local source producer pays the original-clock field and measured-current coupling derivatives. -/
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open ResponsePhase SU7MotherLieAlgebra DiracCliffordRepresentation Stage9DEF
noncomputable section

theorem original_local_coupling_derivative (profile : ℝ → BoundedProfile) (continuousProfile : Continuous profile)
    (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (data : LorentzianIndex → P286LieBlockData) (initial : MatterL2) (time : ℝ)
    (inside : time ∈ Ioo (-(localPerturbedDevelopment profile continuousProfile data).radius)
      (localPerturbedDevelopment profile continuousProfile data).radius) :
    HasDerivAt (fun epsilon => LocalPerturbed.originalCurve profile data
      (localPerturbedDevelopment profile continuousProfile data) epsilon 0 initial time)
      (originalLocalFirstOrder profile data time initial) 0 := by
  let development := localPerturbedDevelopment profile continuousProfile data
  have atZero : (0 : ℝ) ∈ Ioo (-development.radius) development.radius :=
    ⟨neg_lt_zero.mpr development.positive,development.positive⟩
  have derivative := true_family_interaction_derivative _
    (localGaugeHistory_continuous profile continuousProfile data)
    (fun t => localGaugeHamiltonian_selfAdjoint (profile t) (realProfile t) data)
    development.radius development.positive (fun epsilon t => development.curve epsilon 0 initial t) initial
    (fun epsilon coupling => development.starts epsilon 0 initial coupling atZero)
    (fun epsilon coupling => development.evolves epsilon 0 initial coupling atZero) time inside
  have transported := ((originalSpatialUnitary time).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 derivative
  simp only [LocalPerturbed.originalCurve,neg_zero,originalSpatial_zero]
  convert! transported using 1
  rw [originalLocalFirstOrder_readback profile continuousProfile]
  change phaseRead time (spatialUnitary time (interactionTangent _ initial time))=
    originalSpatialUnitary time (interactionTangent _ initial time)
  exact (originalSpatialUnitary_readback time _).symm

theorem original_local_current_derivative (profile : ℝ → BoundedProfile) (continuousProfile : Continuous profile)
    (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (currentData : LorentzianIndex → P286LieBlockData) (initial : MatterL2) (preparedAt time : ℝ)
    (inside : time ∈ Ioo (-(localPerturbedDevelopment profile continuousProfile forceData).radius)
      (localPerturbedDevelopment profile continuousProfile forceData).radius) :
    HasDerivAt (fun epsilon => measuredCurrent detector currentData
      (LocalPerturbed.originalCurve profile forceData (localPerturbedDevelopment profile continuousProfile forceData)
        epsilon 0 (phaseRead preparedAt initial) time))
      (Complex.I*∫ s in (0 : ℝ)..time,
        kuboKernel (fun r => localGaugeHamiltonian (profile r) forceData)
          (localCurrentOperator detector currentData) initial time s).re 0 := by
  let development := localPerturbedDevelopment profile continuousProfile forceData
  have derivative := development.current_coupling_kubo
    (localGaugeHistory_continuous profile continuousProfile forceData)
    (fun t => localGaugeHamiltonian_selfAdjoint (profile t) (realProfile t) forceData)
    (localCurrentOperator detector currentData) initial time inside
  have realDerivative := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 derivative
  apply realDerivative.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ)<0) (by norm_num : (0 : ℝ)<1)] with epsilon near
  rw [LocalPerturbed.original_current profile forceData development realProfile epsilon (abs_le.mpr near)
    time inside preparedAt initial detector realDetector currentData,
    measuredCurrent_pair detector realDetector]
  rfl

theorem original_prepared_current_source_derivative
    (preparation : ℝ → MatterFiber →L[ℂ] MatterL2) (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (profile : ℝ → BoundedProfile) (continuousProfile : Continuous profile)
    (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (currentData : LorentzianIndex → P286LieBlockData) (time : ℝ)
    (inside : time ∈ Ioo (-(localPerturbedDevelopment profile continuousProfile forceData).radius)
      (localPerturbedDevelopment profile continuousProfile forceData).radius) :
    HasDerivAt (fun epsilon => measuredCurrent detector currentData
      (LocalPerturbed.originalCurve profile forceData (localPerturbedDevelopment profile continuousProfile forceData)
        epsilon 0 (phaseRead preparedAt (normalizedPreparation preparation continuousPreparation preparedAt)) time))
      (State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
          (normalizedPreparationNative preparation continuousPreparation preparedAt
            (responseOperator (fun t => localGaugeHamiltonian (profile t) forceData)
              (localGaugeHistory_continuous profile continuousProfile forceData)
              (localCurrentOperator detector currentData) time))))).re 0 := by
  rw [local_native_kubo preparation continuousPreparation preparedAt profile continuousProfile realProfile]
  exact original_local_current_derivative profile continuousProfile realProfile forceData detector
    realDetector currentData _ preparedAt time inside

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
