import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedPiPreparationReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFiniteStaticRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualExplicitGreenNoetherWords

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourcePreparedNoetherPi

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback
open PreparationVacuumNoetherChart PreparationVacuumYukawaTransport
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalHalfAxis
open PreparationVacuumGaugeSourceInjection
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse SourcePropagationNoetherTime
open PreparationVacuumLocalizedYukawa PreparationVacuumPreparedCurrent
open CanonicalPhysicalYResolvent
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedNoether ActualDressedFieldTime
open ActualDressedNumberField
open ActualDressedFiniteStaticRead ActualDressedSylvester ActualDressedSignal ActualDressedPencil
open ActualPreparedPiPreparationReturnProducer ActualSourceExplicitEvolutionPolynomial
open SourceGraph FullYSourceCutoffVolterra Set MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix

/-- Both finite evolutions start at the same actual preparation-domain point.
The created and background sectors retain their original N2/N1 Green words. -/
def sourcePreparedFiniteRead (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (h : Field289) : ℂ :=
  let occurrence := ActualPreparedPiPreparationReturn.of_source event
  let created := occurrence.creationMap occurrence.point.val
  let background := sourcePrepared occurrence.point.val;
  -inner ℂ created
    (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-age)
      (jointCResolvent (event.momentum-transfer) event.frame event.energy h
        (noetherReader reader event.momentum event.frame h
          (jointN2GreenWords event.momentum event.frame event.energy h
            (partialEvolution (jointCompression event.momentum event.frame h)
              (jointY (finiteRetainer event.momentum event.frame) h) 2 age created)))))+
  inner ℂ background
    (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-age)
      (jointCResolvent (event.momentum-transfer) event.frame event.energy h
        (noetherReader reader event.momentum event.frame h
          (jointN1GreenWords event.momentum event.frame event.energy h
            (partialEvolution (jointCompression event.momentum event.frame h)
              (jointY (finiteRetainer event.momentum event.frame) h) 1 age background)))))

attribute [local irreducible] sourcePreparedFiniteRead finiteNumberFieldRead

theorem source_prepared_finite_read_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (h : Field289) :
    sourcePreparedFiniteRead event transfer reader age h =
      finiteNumberFieldRead event transfer reader age h := by
  let occurrence := ActualPreparedPiPreparationReturn.of_source event
  have created : occurrence.creationMap occurrence.point.val =
      sourceDressedUnit event.epsilon event.precision :=
    occurrence.creation_transport.trans occurrence.actualUnit_from_source
  have background : sourcePrepared occurrence.point.val =
      prepared (sourceProfile event.epsilon event.precision) :=
    occurrence.background_transport.trans occurrence.preparedBackground_from_source
  unfold sourcePreparedFiniteRead finiteNumberFieldRead
  dsimp only
  rw [show (ActualPreparedPiPreparationReturn.of_source event).creationMap
      (ActualPreparedPiPreparationReturn.of_source event).point.val =
      sourceDressedUnit event.epsilon event.precision from created,
    show sourcePrepared (ActualPreparedPiPreparationReturn.of_source event).point.val =
      prepared (sourceProfile event.epsilon event.precision) from background]

/-- This response is the field derivative of the generated preparation read,
not the undifferentiated one-current photon amplitude. -/
theorem source_prepared_finite_field_derivative (event : DressedEvent)
    (transfer : PhysicalMomentum) (force : Field289) (age : ℝ) (i : Fin 289) :
    HasDerivAt (fun r : ℝ => sourcePreparedFiniteRead event transfer (fieldUnit i) age
      (r • force)) (dressedNoetherJet event transfer (fun _ => ⟨force,0,0⟩) age i).value 0 := by
  exact (actual_finite_number_field_quantum_derivative event transfer force age i).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r =>
      source_prepared_finite_read_actual event transfer (fieldUnit i) age (r • force)))

def sourcePreparedPiEntry (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (i j : Fin 289) : ℂ :=
  ∫t in Ioi (0:ℝ), laplaceWeight lambda t *
    deriv (fun r : ℝ => sourcePreparedFiniteRead event transfer (fieldUnit i) t
      (r • fieldUnit j)) 0

attribute [local irreducible] sourcePreparedPiEntry

/-- The preparation-domain producer returns every entry of the unchanged full Pi. -/
theorem source_prepared_pi_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (i j : Fin 289) :
    sourcePreparedPiEntry event transfer lambda i j =
      dressedStaticPolarization event transfer lambda i j := by
  unfold sourcePreparedPiEntry
  simp_rw [(source_prepared_finite_field_derivative event transfer (fieldUnit j) _ i).deriv]
  symm
  have actual := dressed_static_polarization_finite event transfer lambda positive i j
  simpa only [finite_constant_field_slope_actual] using actual

theorem source_prepared_pi_explicit (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (i j : Fin 289) :
    sourcePreparedPiEntry event transfer lambda i j =
      explicitFullNoetherEntry event transfer lambda i j :=
  (source_prepared_pi_actual event transfer lambda positive i j).trans
    (explicit_full_noether_polarization event transfer lambda positive i j)

theorem source_prepared_pi_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4 → ℂ) (static : p 0 = 0) (lambda : ℂ) (positive : 0 < lambda.re)
    (T : ℝ) (future : 0 ≤ T) (i j : Fin 289) :
    ‖sourcePreparedPiEntry event transfer lambda i j -
      dressedWindowPolarization event transfer p lambda T i j‖ ≤
      dressedSignalTailPrice event transfer p lambda T := by
  rw [source_prepared_pi_actual event transfer lambda positive i j]
  exact dressed_static_polarization_tail event transfer p static lambda positive T future i j

end LowEnergy.GaussComposite.ActualSourcePreparedNoetherPi
