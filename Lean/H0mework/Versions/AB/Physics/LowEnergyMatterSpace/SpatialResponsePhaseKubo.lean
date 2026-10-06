import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.SpatialResponsePhase
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.SpatialResponseSource

/-! Physical-time Heisenberg currents and kernels equal the already-generated co-rotating response. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.ResponsePhase
open _root_.SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open SU7MotherLieAlgebra DiracCliffordRepresentation
noncomputable section

def originalFreeOperator (t : ℝ) : MatterL2 →L[ℂ] MatterL2 :=
  (originalSpatialUnitary t).toContinuousLinearEquiv.toContinuousLinearMap

def originalHeisenberg (observable : MatterL2 →L[ℂ] MatterL2) (t : ℝ) : MatterL2 →L[ℂ] MatterL2 :=
  (originalFreeOperator t).adjoint.comp (observable.comp (originalFreeOperator t))

theorem originalHeisenberg_pair (observable : MatterL2 →L[ℂ] MatterL2)
    (t : ℝ) (u v : MatterL2) :
    inner ℂ u (originalHeisenberg observable t v)=
      inner ℂ (originalSpatialUnitary t u) (observable (originalSpatialUnitary t v)) := by
  change inner ℂ u ((originalFreeOperator t).adjoint (observable (originalFreeOperator t v)))=
    inner ℂ (originalFreeOperator t u) (observable (originalFreeOperator t v))
  exact ContinuousLinearMap.adjoint_inner_right (originalFreeOperator t) u (observable (originalFreeOperator t v))

theorem localGauge_originalHeisenberg (profile : BoundedProfile)
    (data : LorentzianIndex → P286LieBlockData) (t : ℝ) :
    originalHeisenberg (localGaugeHamiltonian profile data) t=heisenberg (localGaugeHamiltonian profile data) t := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [originalHeisenberg_pair,originalSpatialUnitary_readback,originalSpatialUnitary_readback,
    ← localGauge_phase,phaseRead_pair]
  exact (heisenberg_pair _ t u v).symm

theorem localCurrent_originalHeisenberg (profile : BoundedProfile)
    (data : LorentzianIndex → P286LieBlockData) (t : ℝ) :
    originalHeisenberg (localCurrentOperator profile data) t=heisenberg (localCurrentOperator profile data) t := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [originalHeisenberg_pair,originalSpatialUnitary_readback,originalSpatialUnitary_readback,
    localCurrent_phase_pair]
  exact (heisenberg_pair _ t u v).symm

theorem original_current_pair (profile : BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (t : ℝ) (u v : MatterL2) :
    inner ℂ (originalSpatialUnitary t u) (localCurrentOperator profile data (originalSpatialUnitary t v))=
      inner ℂ (spatialUnitary t u) (localCurrentOperator profile data (spatialUnitary t v)) := by
  rw [originalSpatialUnitary_readback,originalSpatialUnitary_readback,localCurrent_phase_pair]

theorem original_measuredCurrent (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x)
    (data : LorentzianIndex → P286LieBlockData) (t : ℝ) (u : MatterL2) :
    measuredCurrent profile data (originalSpatialUnitary t u)=measuredCurrent profile data (spatialUnitary t u) := by
  rw [measuredCurrent_pair profile real,measuredCurrent_pair profile real,original_current_pair]

def originalKuboKernel (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (current : MatterL2 →L[ℂ] MatterL2) (u : MatterL2) (t s : ℝ) : ℂ :=
  inner ℂ u (((originalHeisenberg (perturbation s) s).comp (originalHeisenberg current t)-
    (originalHeisenberg current t).comp (originalHeisenberg (perturbation s) s)) u)

theorem local_originalKuboKernel (profile : ℝ → BoundedProfile)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (currentData : LorentzianIndex → P286LieBlockData) (u : MatterL2) (t s : ℝ) :
    originalKuboKernel (fun r => localGaugeHamiltonian (profile r) forceData)
      (localCurrentOperator detector currentData) u t s=
      kuboKernel (fun r => localGaugeHamiltonian (profile r) forceData)
        (localCurrentOperator detector currentData) u t s := by
  rw [originalKuboKernel,localGauge_originalHeisenberg,localCurrent_originalHeisenberg]
  rfl

theorem heisenbergGauge_phase (profile : BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (r t : ℝ) (u : MatterL2) :
    phaseRead r (heisenberg (localGaugeHamiltonian profile data) t u)=
      heisenberg (localGaugeHamiltonian profile data) t (phaseRead r u) := by
  simp only [heisenberg_apply]
  rw [spatialUnitary_phase,localGauge_phase,spatialUnitary_phase]

theorem heisenbergCurrent_phase (profile : BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (r t : ℝ) (u : MatterL2) :
    phaseRead r (heisenberg (localCurrentOperator profile data) t u)=
      heisenberg (localCurrentOperator profile data) t (phaseRead r u) := by
  simp only [heisenberg_apply]
  rw [spatialUnitary_phase,localCurrent_phase,spatialUnitary_phase]

theorem kuboKernel_prepared_phase (profile : ℝ → BoundedProfile)
    (forceData : LorentzianIndex → P286LieBlockData) (detector : BoundedProfile)
    (currentData : LorentzianIndex → P286LieBlockData) (u : MatterL2) (r t s : ℝ) :
    kuboKernel (fun a => localGaugeHamiltonian (profile a) forceData)
      (localCurrentOperator detector currentData) (phaseRead r u) t s=
      kuboKernel (fun a => localGaugeHamiltonian (profile a) forceData)
        (localCurrentOperator detector currentData) u t s := by
  change inner ℂ (phaseRead r u)
    (heisenberg (localGaugeHamiltonian (profile s) forceData) s
        (heisenberg (localCurrentOperator detector currentData) t (phaseRead r u))-
      heisenberg (localCurrentOperator detector currentData) t
        (heisenberg (localGaugeHamiltonian (profile s) forceData) s (phaseRead r u)))=_
  rw [← heisenbergCurrent_phase,← heisenbergGauge_phase,← heisenbergGauge_phase,
    ← heisenbergCurrent_phase,← map_sub,phaseRead_pair]
  rfl

theorem originalKernel_prepared_readback (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (profile : ℝ → BoundedProfile) (forceData : LorentzianIndex → P286LieBlockData)
    (detector : BoundedProfile) (currentData : LorentzianIndex → P286LieBlockData) (t s : ℝ) :
    originalKuboKernel (fun a => localGaugeHamiltonian (profile a) forceData)
      (localCurrentOperator detector currentData)
      (phaseRead preparedAt (normalizedPreparation preparation continuousPreparation preparedAt)) t s=
      kuboKernel (fun a => localGaugeHamiltonian (profile a) forceData)
        (localCurrentOperator detector currentData)
        (normalizedPreparation preparation continuousPreparation preparedAt) t s := by
  rw [local_originalKuboKernel,kuboKernel_prepared_phase]

theorem spatialMoment_phase {ι : Type*} [Fintype ι] (prepared : MatterL2)
    (tests : ι → MatterL2) (r : ℝ) (word : List (SpatialCAR.Letter (Option ι))) :
    SpatialCAR.spatialMoment (phaseRead r prepared) (fun i => phaseRead r (tests i)) word=
      SpatialCAR.spatialMoment prepared tests word := by
  have familyPhase (i : Option ι) :
      SpatialCAR.family (phaseRead r prepared) (fun j => phaseRead r (tests j)) i=
        phaseRead r (SpatialCAR.family prepared tests i) := by
    cases i <;> rfl
  rw [SpatialCAR.spatialMoment_gram,SpatialCAR.spatialMoment_gram]
  simp_rw [familyPhase,phaseRead_pair]

theorem originalSpatialCAR_readback {ι : Type*} [Fintype ι] (prepared : MatterL2)
    (tests : ι → MatterL2) (times : ι → ℝ) (word : List (SpatialCAR.Letter (Option ι))) :
    SpatialCAR.spatialMoment prepared (fun i => originalSpatialUnitary (times i) (tests i)) word=
      SpatialCAR.spatialMoment prepared
        (fun i => phaseRead (times i) (spatialUnitary (times i) (tests i))) word := by
  congr 1
  funext i
  exact originalSpatialUnitary_readback (times i) (tests i)

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.ResponsePhase
