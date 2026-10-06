import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.PerturbedNative
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.SpatialResponsePhaseDuhamel

/-! The finite local source flow obeys the actual original-clock interaction equation. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open ResponsePhase SU7MotherLieAlgebra DiracCliffordRepresentation Stage9DEF
noncomputable section

theorem originalSpatial_zero (u : MatterL2) : originalSpatialUnitary 0 u=u := by
  rw [originalSpatialUnitary_readback,spatialUnitary_zero,phaseRead_zero]

theorem originalSpatial_add (s t : ℝ) (u : MatterL2) :
    originalSpatialUnitary (s+t) u=originalSpatialUnitary s (originalSpatialUnitary t u) := by
  simp only [originalSpatialUnitary_readback,spatialUnitary_add,phaseRead_add,spatialUnitary_phase]

theorem originalHeisenberg_apply (observable : MatterL2 →L[ℂ] MatterL2) (t : ℝ) (u : MatterL2) :
    originalHeisenberg observable t u=originalSpatialUnitary (-t) (observable (originalSpatialUnitary t u)) := by
  apply ext_inner_left ℂ
  intro v
  rw [originalHeisenberg_pair]
  have paired := (originalSpatialUnitary t).inner_map_map v
    (originalSpatialUnitary (-t) (observable (originalSpatialUnitary t u)))
  rw [← originalSpatial_add,add_neg_cancel,originalSpatial_zero] at paired
  exact paired

namespace LocalPerturbed
variable (profile : ℝ → BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (development : PerturbedDevelopment (fun t => localGaugeHamiltonian (profile t) data))

def originalCurve (epsilon start : ℝ) (initial : MatterL2) (time : ℝ) : MatterL2 :=
  originalSpatialUnitary time
    (development.curve epsilon start (originalSpatialUnitary (-start) initial) time)

theorem originalCurve_starts (epsilon start : ℝ) (initial : MatterL2)
    (coupling : |epsilon|≤1) (located : start ∈ Ioo (-development.radius) development.radius) :
    originalCurve profile data development epsilon start initial start=initial := by
  rw [originalCurve,development.starts epsilon start _ coupling located,
    ← originalSpatial_add,add_neg_cancel,originalSpatial_zero]

theorem originalCurve_interaction (epsilon start time : ℝ) (initial : MatterL2) :
    originalSpatialUnitary (-time) (originalCurve profile data development epsilon start initial time)=
      development.curve epsilon start (originalSpatialUnitary (-start) initial) time := by
  rw [originalCurve,← originalSpatial_add,neg_add_cancel,originalSpatial_zero]

theorem originalCurve_equation (epsilon start : ℝ) (initial : MatterL2)
    (coupling : |epsilon|≤1) (located : start ∈ Ioo (-development.radius) development.radius)
    (time : ℝ) (inside : time ∈ Ioo (-development.radius) development.radius) :
    HasDerivAt (fun t => originalSpatialUnitary (-t)
      (originalCurve profile data development epsilon start initial t))
      (originalSpatialUnitary (-time) ((-Complex.I*(epsilon : ℂ)) •
        localGaugeHamiltonian (profile time) data
          (originalCurve profile data development epsilon start initial time))) time := by
  simp only [originalCurve_interaction]
  convert! development.evolves epsilon start (originalSpatialUnitary (-start) initial) coupling located time inside using 1
  rw [map_smul]
  change (-Complex.I*(epsilon : ℂ)) • originalSpatialUnitary (-time)
    (localGaugeHamiltonian (profile time) data (originalSpatialUnitary time
      (development.curve epsilon start (originalSpatialUnitary (-start) initial) time)))=_
  rw [← originalHeisenberg_apply,localGauge_originalHeisenberg]
  rfl

theorem curve_phase (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (epsilon : ℝ) (coupling : |epsilon|≤1) (start time : ℝ)
    (atStart : start ∈ Ioo (-development.radius) development.radius)
    (atTime : time ∈ Ioo (-development.radius) development.radius) (r : ℝ) (initial : MatterL2) :
    development.curve epsilon start (phaseRead r initial) time=
      phaseRead r (development.curve epsilon start initial time) := by
  apply perturbed_curve_unique _ (fun t => localGaugeHamiltonian_selfAdjoint (profile t) (realProfile t) data)
    epsilon development.radius start atStart
    (development.curve epsilon start (phaseRead r initial))
    (fun t => phaseRead r (development.curve epsilon start initial t))
    (development.evolves epsilon start _ coupling atStart) _ _ atTime
  · intro t inside
    have generated := ((phaseRead r).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (development.evolves epsilon start initial coupling atStart t inside)
    convert! generated using 1
    change interactionGenerator (fun s => localGaugeHamiltonian (profile s) data) epsilon t
      (phaseRead r (development.curve epsilon start initial t))=
        phaseRead r (interactionGenerator (fun s => localGaugeHamiltonian (profile s) data) epsilon t
          (development.curve epsilon start initial t))
    change (-Complex.I*(epsilon : ℂ)) • heisenberg (localGaugeHamiltonian (profile t) data) t
      (phaseRead r (development.curve epsilon start initial t))=
        phaseRead r ((-Complex.I*(epsilon : ℂ)) • heisenberg (localGaugeHamiltonian (profile t) data) t
          (development.curve epsilon start initial t))
    rw [map_smul,heisenbergGauge_phase]
  · rw [development.starts epsilon start _ coupling atStart,development.starts epsilon start _ coupling atStart]

theorem originalCurve_prepared (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (epsilon : ℝ) (coupling : |epsilon|≤1) (time : ℝ)
    (inside : time ∈ Ioo (-development.radius) development.radius) (preparedAt : ℝ) (initial : MatterL2) :
    originalCurve profile data development epsilon 0 (phaseRead preparedAt initial) time=
      phaseRead (time+preparedAt) (development.physicalCurve epsilon 0 initial time) := by
  have zeroInside : (0 : ℝ) ∈ Ioo (-development.radius) development.radius :=
    ⟨neg_lt_zero.mpr development.positive,development.positive⟩
  rw [originalCurve,neg_zero,originalSpatial_zero,
    curve_phase profile data development realProfile epsilon coupling 0 time zeroInside inside]
  rw [originalSpatialUnitary_readback,← spatialUnitary_phase,← phaseRead_add]
  simp only [PerturbedDevelopment.physicalCurve,neg_zero,spatialUnitary_zero]

theorem original_current (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (epsilon : ℝ) (coupling : |epsilon|≤1) (time : ℝ)
    (inside : time ∈ Ioo (-development.radius) development.radius) (preparedAt : ℝ) (initial : MatterL2)
    (detector : BoundedProfile) (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (currentData : LorentzianIndex → P286LieBlockData) :
    measuredCurrent detector currentData
      (originalCurve profile data development epsilon 0 (phaseRead preparedAt initial) time)=
      measuredCurrent detector currentData (development.physicalCurve epsilon 0 initial time) := by
  rw [originalCurve_prepared profile data development realProfile epsilon coupling time inside,
    measuredCurrent_pair detector realDetector,measuredCurrent_pair detector realDetector,
    localCurrent_phase_pair]

theorem original_current_source (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (epsilon : ℝ) (coupling : |epsilon|≤1) (time : ℝ)
    (inside : time ∈ Ioo (-development.radius) development.radius)
    (preparation : ℝ → MatterFiber →L[ℂ] MatterL2) (continuousPreparation : Continuous preparation)
    (preparedAt : ℝ) (detector : BoundedProfile) (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (currentData : LorentzianIndex → P286LieBlockData) :
    measuredCurrent detector currentData
      (originalCurve profile data development epsilon 0
        (phaseRead preparedAt (normalizedPreparation preparation continuousPreparation preparedAt)) time)=
    (State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative preparation continuousPreparation preparedAt
          (development.finiteObservable (fun t => localGaugeHamiltonian_selfAdjoint (profile t) (realProfile t) data)
            epsilon coupling 0 time ⟨neg_lt_zero.mpr development.positive,development.positive⟩ inside
            (localCurrentOperator detector currentData)))))).re := by
  rw [original_current profile data development realProfile epsilon coupling time inside preparedAt _
    detector realDetector currentData]
  exact development.finite_current_source _ epsilon coupling 0 time _ inside
    preparation continuousPreparation preparedAt detector realDetector currentData

end LocalPerturbed
end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
