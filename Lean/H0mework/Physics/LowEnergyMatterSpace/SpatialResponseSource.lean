import H0mework.Physics.LowEnergyMatterSpace.SpatialResponseNative
import H0mework.Physics.LowEnergyMatterSpace.SpatialResponseCAR
import H0mework.Physics.LowEnergyMatterSpace.LocalSource

/-! Original bounded local P286 pulses and the original current density consume spatial Kubo. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open SU7MotherLieAlgebra DiracCliffordRepresentation Stage9DEF
open Stage9C.Material.SpinPair StageNineFullDiracAdjointMaterial
noncomputable section

theorem local_force_original (profile : ℝ → BoundedProfile)
    (data : LorentzianIndex → P286LieBlockData) (u : MatterL2) (s : ℝ) :
    perturbationForce (fun r => localGaugeHamiltonian (profile r) data) u s=ᵐ[volume]
      fun x => profile s x • gaugeForceOperator data (spatialUnitary s u x) := by
  filter_upwards [Lp.coeFn_smul (-Complex.I) (localGaugeHamiltonian (profile s) data (spatialUnitary s u)),
    localMatrixOperator_ae (profile s) (gaugeHamiltonianMatrix data) (spatialUnitary s u)] with x scaled matrix
  change ((-Complex.I) • localGaugeHamiltonian (profile s) data (spatialUnitary s u)) x=_
  rw [scaled]
  change (-Complex.I) • (localMatrixOperator (profile s) (gaugeHamiltonianMatrix data) (spatialUnitary s u) x)=_
  rw [matrix]
  exact smul_comm _ _ _

theorem local_force_native (profile : ℝ → BoundedProfile)
    (realProfile : ∀ s, ∀ᵐ x ∂volume, star (profile s x)=profile s x)
    (data : LorentzianIndex → P286LieBlockData) (u : MatterL2) (s : ℝ) :
    perturbationForce (fun r => localGaugeHamiltonian (profile r) data) u s=ᵐ[volume]
      fun x => gaugeForceOperator ((profile s x).re • data) (spatialUnitary s u x) := by
  filter_upwards [Lp.coeFn_smul (-Complex.I) (localGaugeHamiltonian (profile s) data (spatialUnitary s u)),
    localGaugeHamiltonian_native_ae (profile s) (realProfile s) data (spatialUnitary s u)] with x scaled native
  change ((-Complex.I) • localGaugeHamiltonian (profile s) data (spatialUnitary s u)) x=_
  rw [scaled]
  change (-Complex.I) • (localGaugeHamiltonian (profile s) data (spatialUnitary s u) x)=_
  rw [native]
  rfl

def measuredCurrent (detector : BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (v : MatterL2) : ℝ :=
  ∫ x, (detector x).re*gaugeCurrentValue data (v x)
    ((spinScale : ℂ) • fullCanonicalDiracAdjoint (tripletLift (v x)))

theorem measuredCurrent_pair (detector : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (data : LorentzianIndex → P286LieBlockData) (v : MatterL2) :
    measuredCurrent detector data v=(inner ℂ v (localCurrentOperator detector data v)).re :=
  (localCurrent_original detector real data v).symm

theorem local_epsilon_current (profile : ℝ → BoundedProfile) (continuousProfile : Continuous profile)
    (realProfile : ∀ s, ∀ᵐ x ∂volume, star (profile s x)=profile s x)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (currentData : LorentzianIndex → P286LieBlockData) (u : MatterL2) (t : ℝ) :
    HasDerivAt (fun epsilon => measuredCurrent detector currentData
      (epsilonPath (fun s => localGaugeHamiltonian (profile s) forceData) u t epsilon))
      (Complex.I*∫ s in (0 : ℝ)..t, kuboKernel (fun r => localGaugeHamiltonian (profile r) forceData)
        (localCurrentOperator detector currentData) u t s).re 0 := by
  simp_rw [measuredCurrent_pair detector realDetector currentData]
  have generated := epsilonCurrent_derivative (fun s => localGaugeHamiltonian (profile s) forceData)
    (localCurrentOperator detector currentData) u t
  rw [currentVariation_kubo _ (localGaugeHistory_continuous profile continuousProfile forceData)
    (fun s => localGaugeHamiltonian_selfAdjoint (profile s) (realProfile s) forceData)] at generated
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 generated

theorem local_native_kubo (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (profile : ℝ → BoundedProfile) (continuousProfile : Continuous profile)
    (realProfile : ∀ s, ∀ᵐ x ∂volume, star (profile s x)=profile s x)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (currentData : LorentzianIndex → P286LieBlockData) (t : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative preparation continuousPreparation preparedAt
          (responseOperator (fun s => localGaugeHamiltonian (profile s) forceData)
            (localGaugeHistory_continuous profile continuousProfile forceData)
            (localCurrentOperator detector currentData) t))))=
      Complex.I*∫ s in (0 : ℝ)..t,
        kuboKernel (fun r => localGaugeHamiltonian (profile r) forceData)
          (localCurrentOperator detector currentData)
          (normalizedPreparation preparation continuousPreparation preparedAt) t s :=
  native_kubo preparation continuousPreparation preparedAt _
    (localGaugeHistory_continuous profile continuousProfile forceData)
    (fun s => localGaugeHamiltonian_selfAdjoint (profile s) (realProfile s) forceData) _ t

theorem local_source_CAR (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (nonzero : spatialPreparation preparation continuousPreparation preparedAt≠0)
    (profile : ℝ → BoundedProfile) (continuousProfile : Continuous profile)
    (realProfile : ∀ s, ∀ᵐ x ∂volume, star (profile s x)=profile s x)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (currentData : LorentzianIndex → P286LieBlockData) (t : ℝ) :
    currentVariation (fun s => localGaugeHamiltonian (profile s) forceData)
      (localCurrentOperator detector currentData) (normalizedPreparation preparation continuousPreparation preparedAt) t=
      Complex.I*∫ s in (0 : ℝ)..t,
        kuboCAR (fun r => localGaugeHamiltonian (profile r) forceData)
          (localCurrentOperator detector currentData)
          (normalizedPreparation preparation continuousPreparation preparedAt) t s :=
  source_currentVariation_CAR preparation continuousPreparation preparedAt nonzero _
    (localGaugeHistory_continuous profile continuousProfile forceData)
    (fun s => localGaugeHamiltonian_selfAdjoint (profile s) (realProfile s) forceData) _
    (localCurrentOperator_selfAdjoint detector realDetector currentData) t

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
