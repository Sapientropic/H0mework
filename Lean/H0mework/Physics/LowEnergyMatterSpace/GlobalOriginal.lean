import H0mework.Physics.LowEnergyMatterSpace.GlobalResponse

/-! The all-time source flow retains the original clock and preparation phase in its actual current. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.GlobalLocal
open ResponsePhase SU7MotherLieAlgebra DiracCliffordRepresentation Stage9DEF
noncomputable section
variable (profile : ℝ → BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (development : GlobalPerturbedDevelopment (fun t => localGaugeHamiltonian (profile t) data))

def originalCurve (epsilon start : ℝ) (initial : MatterL2) (time : ℝ) : MatterL2 :=
  originalSpatialUnitary time
    (development.curve epsilon start (originalSpatialUnitary (-start) initial) time)

theorem originalCurve_starts (epsilon start : ℝ) (initial : MatterL2) :
    originalCurve profile data development epsilon start initial start=initial := by
  rw [originalCurve,development.starts,← originalSpatial_add,add_neg_cancel,originalSpatial_zero]

theorem originalCurve_interaction (epsilon start time : ℝ) (initial : MatterL2) :
    originalSpatialUnitary (-time) (originalCurve profile data development epsilon start initial time)=
      development.curve epsilon start (originalSpatialUnitary (-start) initial) time := by
  rw [originalCurve,← originalSpatial_add,neg_add_cancel,originalSpatial_zero]

theorem originalCurve_equation (epsilon start : ℝ) (initial : MatterL2) (time : ℝ) :
    HasDerivAt (fun t => originalSpatialUnitary (-t)
      (originalCurve profile data development epsilon start initial t))
      (originalSpatialUnitary (-time) ((-Complex.I*(epsilon : ℂ)) • localGaugeHamiltonian (profile time) data
        (originalCurve profile data development epsilon start initial time))) time := by
  simp only [originalCurve_interaction]
  convert! development.evolves epsilon start (originalSpatialUnitary (-start) initial) time using 1
  rw [map_smul]
  change (-Complex.I*(epsilon : ℂ)) • originalSpatialUnitary (-time)
    (localGaugeHamiltonian (profile time) data (originalSpatialUnitary time
      (development.curve epsilon start (originalSpatialUnitary (-start) initial) time)))=_
  rw [← originalHeisenberg_apply,localGauge_originalHeisenberg]
  rfl

theorem originalCurve_norm (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (epsilon start time : ℝ) (initial : MatterL2) :
    ‖originalCurve profile data development epsilon start initial time‖=‖initial‖ := by
  rw [originalCurve,(originalSpatialUnitary time).norm_map,
    development.norm (fun t => localGaugeHamiltonian_selfAdjoint (profile t) (realProfile t) data),
    (originalSpatialUnitary (-start)).norm_map]

theorem curve_phase (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (epsilon start time r : ℝ) (initial : MatterL2) :
    development.curve epsilon start (phaseRead r initial) time=
      phaseRead r (development.curve epsilon start initial time) := by
  apply congrFun (global_curve_unique _
    (fun t => localGaugeHamiltonian_selfAdjoint (profile t) (realProfile t) data) epsilon start
    (development.curve epsilon start (phaseRead r initial))
    (fun t => phaseRead r (development.curve epsilon start initial t))
    (development.evolves epsilon start _) _ _) time
  · intro t
    have generated := ((phaseRead r).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (development.evolves epsilon start initial t)
    convert! generated using 1
    change (-Complex.I*(epsilon : ℂ)) • heisenberg (localGaugeHamiltonian (profile t) data) t
      (phaseRead r (development.curve epsilon start initial t))=
        phaseRead r ((-Complex.I*(epsilon : ℂ)) • heisenberg (localGaugeHamiltonian (profile t) data) t
          (development.curve epsilon start initial t))
    rw [map_smul,heisenbergGauge_phase]
  · rw [development.starts,development.starts]

theorem originalCurve_prepared (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (epsilon time preparedAt : ℝ) (initial : MatterL2) :
    originalCurve profile data development epsilon 0 (phaseRead preparedAt initial) time=
      phaseRead (time+preparedAt) (development.physicalCurve epsilon 0 time initial) := by
  rw [originalCurve,neg_zero,originalSpatial_zero,
    curve_phase profile data development realProfile epsilon 0 time]
  rw [originalSpatialUnitary_readback,← spatialUnitary_phase,← phaseRead_add]
  simp only [GlobalPerturbedDevelopment.physicalCurve,neg_zero,spatialUnitary_zero]

theorem original_current (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (epsilon time preparedAt : ℝ) (initial : MatterL2) (detector : BoundedProfile)
    (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (currentData : LorentzianIndex → P286LieBlockData) :
    measuredCurrent detector currentData
      (originalCurve profile data development epsilon 0 (phaseRead preparedAt initial) time)=
      measuredCurrent detector currentData (development.physicalCurve epsilon 0 time initial) := by
  rw [originalCurve_prepared profile data development realProfile,
    measuredCurrent_pair detector realDetector,measuredCurrent_pair detector realDetector,localCurrent_phase_pair]

theorem original_field_derivative (continuousProfile : Continuous profile)
    (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x) (initial : MatterL2) (time : ℝ) :
    HasDerivAt (fun epsilon => originalCurve profile data development epsilon 0 initial time)
      (originalLocalFirstOrder profile data time initial) 0 := by
  have generated := ((phaseRead time).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (development.coupling_derivative (localGaugeHistory_continuous profile continuousProfile data)
      (fun t => localGaugeHamiltonian_selfAdjoint (profile t) (realProfile t) data) initial time)
  rw [originalLocalFirstOrder_readback profile continuousProfile]
  convert! generated using 1
  funext epsilon
  simp only [originalCurve,GlobalPerturbedDevelopment.physicalCurve,neg_zero,
    spatialUnitary_zero,originalSpatialUnitary_readback,phaseRead_zero]
  rfl

theorem original_current_derivative (continuousProfile : Continuous profile)
    (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (initial : MatterL2) (time preparedAt : ℝ) (detector : BoundedProfile)
    (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (currentData : LorentzianIndex → P286LieBlockData) :
    HasDerivAt (fun epsilon => measuredCurrent detector currentData
      (originalCurve profile data development epsilon 0 (phaseRead preparedAt initial) time))
      (Complex.I*∫ s in (0 : ℝ)..time,
        kuboKernel (fun t => localGaugeHamiltonian (profile t) data)
          (localCurrentOperator detector currentData) initial time s).re 0 := by
  simp_rw [original_current profile data development realProfile _ time preparedAt initial detector realDetector,
    measuredCurrent_pair detector realDetector]
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (development.current_kubo (localGaugeHistory_continuous profile continuousProfile data)
      (fun t => localGaugeHamiltonian_selfAdjoint (profile t) (realProfile t) data) _ initial time)

theorem original_prepared_source_derivative (continuousProfile : Continuous profile)
    (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (preparation : ℝ → MatterFiber →L[ℂ] MatterL2) (continuousPreparation : Continuous preparation)
    (preparedAt time : ℝ) (detector : BoundedProfile)
    (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (currentData : LorentzianIndex → P286LieBlockData) :
    HasDerivAt (fun epsilon => measuredCurrent detector currentData
      (originalCurve profile data development epsilon 0
        (phaseRead preparedAt (normalizedPreparation preparation continuousPreparation preparedAt)) time))
      (State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
          (normalizedPreparationNative preparation continuousPreparation preparedAt
            (responseOperator (fun t => localGaugeHamiltonian (profile t) data)
              (localGaugeHistory_continuous profile continuousProfile data) (localCurrentOperator detector currentData) time))))).re 0 := by
  rw [local_native_kubo preparation continuousPreparation preparedAt profile continuousProfile realProfile]
  exact original_current_derivative profile data development continuousProfile realProfile _ time preparedAt
    detector realDetector currentData

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.GlobalLocal
