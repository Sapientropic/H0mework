import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeSector

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFieldTime
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open PreparationVacuumNoetherChart PreparationVacuumYukawaTransport
open ActualDressedNumberField ActualDressedNoether ActualDressedFullCoulomb ActualDressedSourcePreparation
open GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open FullYSourceCutoffVolterra Filter
open scoped Topology InnerProductSpace
local instance finiteReadReal : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointCompression jointY physicalTime timeSlope numberFieldRead

/-- The unchanged complete raw reader consumes the two original finite right Dyson evolutions. -/
def finiteNumberFieldRead (event : DressedEvent) (transfer : PhysicalMomentum) (reader : Field289) (age : ℝ) (h : Field289) : ℂ :=
  -inner ℂ (sourceDressedUnit event.epsilon event.precision)
    (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-age)
      (jointCResolvent (event.momentum-transfer) event.frame event.energy h
        (noetherReader reader event.momentum event.frame h
          (jointN2GreenWords event.momentum event.frame event.energy h
            (partialEvolution (jointCompression event.momentum event.frame h)
              (jointY (PreparationVacuumYukawaTransport.finiteRetainer event.momentum event.frame) h) 2 age
              (sourceDressedUnit event.epsilon event.precision))))))+
  inner ℂ (prepared (sourceProfile event.epsilon event.precision))
    (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-age)
      (jointCResolvent (event.momentum-transfer) event.frame event.energy h
        (noetherReader reader event.momentum event.frame h
          (jointN1GreenWords event.momentum event.frame event.energy h
            (partialEvolution (jointCompression event.momentum event.frame h)
              (jointY (PreparationVacuumYukawaTransport.finiteRetainer event.momentum event.frame) h) 1 age
              (prepared (sourceProfile event.epsilon event.precision)))))))


attribute [local irreducible] finiteNumberFieldRead

theorem actual_finite_number_field_read (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (h : Field289) :
    numberFieldRead event transfer reader age h=finiteNumberFieldRead event transfer reader age h := by
  unfold numberFieldRead finiteNumberFieldRead
  rw [actual_field_time_created_unit,actual_field_time_background]

/-- This all-field identity directly retains both original Green words and every full reader entry. -/
theorem actual_finite_noether_field_germ (event : DressedEvent) (transfer : PhysicalMomentum) :
    ∀ᶠh : Field289 in 𝓝 0,∀(age : ℝ) (reader : Field289),
    dressedEulerObserver event (dressedNoetherKernel event transfer reader age h)=
      finiteNumberFieldRead event transfer reader age h := by
  filter_upwards [actual_noether_number_field_germ event transfer] with h original
  intro age reader
  exact (original age reader).trans (actual_finite_number_field_read event transfer reader age h)

/-- The complete constant-field quantum derivative now has an actually finite right time read. -/
theorem actual_finite_number_field_quantum_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) (i : Fin 289) :
    HasDerivAt (fun r : ℝ=>finiteNumberFieldRead event transfer
        (PreparationVacuumActionFieldLift.fieldUnit i) age (r • force))
      (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) age i).value 0 := by
  exact (actual_number_field_quantum_derivative event transfer force age i).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r=>(actual_finite_number_field_read event transfer _ age (r • force)).symm))

theorem actual_finite_created_time_direction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (age epsilon : ℝ) (precision : 0<epsilon) :
    HasDerivAt (fun r : ℝ=>partialEvolution (jointCompression p F (r • force))
      (jointY (finiteRetainer p F) (r • force)) 2 age (sourceDressedUnit epsilon precision))
      (timeSlope force p F age (sourceDressedUnit epsilon precision)) 0 := by
  have source := ((ContinuousLinearMap.apply ℂ H (sourceDressedUnit epsilon precision)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (physicalTime_direction force p F age)
  exact source.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun r=>(actual_field_time_created_unit p F (r • force) age epsilon precision).symm))

theorem actual_finite_background_time_direction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (age : ℝ) (profile : GaussComposite.SourceGraph.Profile) :
    HasDerivAt (fun r : ℝ=>partialEvolution (jointCompression p F (r • force))
      (jointY (finiteRetainer p F) (r • force)) 1 age (prepared profile))
      (timeSlope force p F age (prepared profile)) 0 := by
  have source := ((ContinuousLinearMap.apply ℂ H (prepared profile)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (physicalTime_direction force p F age)
  exact source.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun r=>(actual_field_time_background p F (r • force) age profile).symm))

end LowEnergy.GaussComposite.ActualDressedFieldTime
