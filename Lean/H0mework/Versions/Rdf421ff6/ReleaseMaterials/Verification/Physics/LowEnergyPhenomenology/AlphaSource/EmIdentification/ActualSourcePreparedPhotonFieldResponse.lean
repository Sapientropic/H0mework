import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedNoetherPi
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePolarizationFlux
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherResponse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourcePreparedPhotonFieldResponse
open CanonicalGradedSpatialSource PreparationVacuumActionFieldLift
open PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection
open PreparationPhysicalNativePhotonFluxReturn
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedFiniteStaticRead
open LowEnergy.GaussComposite.ActualDressedNoether
open ActualDressedSylvester ActualSourcePreparedNoetherPi ActualSourceExplicitEvolutionPolynomial
open Set MeasureTheory
open scoped Topology BigOperators Matrix

/-- The source photon mode reads the entire same preparation field curve.
The mode is fixed at the original background while the actual field varies. -/
def sourcePreparedPhotonFieldRead (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (age : ℝ) (h : Field289) : ℂ :=
  ∑i, sourceNativeFrequencyPolarization branch epsilon s n i *
    sourcePreparedFiniteRead event transfer (fieldUnit i) age h

theorem source_prepared_photon_field_derivative (event : DressedEvent)
    (transfer : PhysicalMomentum) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ => sourcePreparedPhotonFieldRead event transfer branch epsilon s n
      age (r • force))
      (∑i, sourceNativeFrequencyPolarization branch epsilon s n i *
        (dressedNoetherJet event transfer (fun _ => ⟨force,0,0⟩) age i).value) 0 := by
  unfold sourcePreparedPhotonFieldRead
  exact HasDerivAt.fun_sum (fun i _ =>
    (source_prepared_finite_field_derivative event transfer force age i).const_mul _)

def sourcePreparedPhotonPiColumn (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (lambda : ℂ) (j : Fin 289) : ℂ :=
  ∫t in Ioi (0:ℝ), laplaceWeight lambda t *
    deriv (fun r : ℝ => sourcePreparedPhotonFieldRead event transfer branch epsilon s n
      t (r • fieldUnit j)) 0

theorem source_prepared_photon_pi_column (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (lambda : ℂ)
    (positive : 0 < lambda.re) (j : Fin 289) :
    sourcePreparedPhotonPiColumn event transfer branch epsilon s n lambda j =
      ∑i, sourceNativeFrequencyPolarization branch epsilon s n i *
        sourcePreparedPiEntry event transfer lambda i j := by
  let U := sourceNativeFrequencyPolarization branch epsilon s n
  have integrable (i : Fin 289) : IntegrableOn
      (fun t => U i * (laplaceWeight lambda t *
        finiteConstantFieldSlope event transfer (fieldUnit j) t i)) (Ioi (0:ℝ)) :=
    (finite_static_integrand_integrable event transfer (fieldUnit j) lambda positive i).const_mul (U i)
  unfold sourcePreparedPhotonPiColumn
  calc
    _ = ∫t in Ioi (0:ℝ), ∑i, U i * (laplaceWeight lambda t *
        finiteConstantFieldSlope event transfer (fieldUnit j) t i) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [(source_prepared_photon_field_derivative event transfer branch epsilon s n
        (fieldUnit j) t).deriv]
      simp only [Finset.mul_sum, finite_constant_field_slope_actual, U]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑i, ∫t in Ioi (0:ℝ), U i * (laplaceWeight lambda t *
        finiteConstantFieldSlope event transfer (fieldUnit j) t i) :=
      integral_finsetSum Finset.univ (fun i _ => integrable i)
    _ = ∑i, U i * sourcePreparedPiEntry event transfer lambda i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, source_prepared_pi_actual event transfer lambda positive i j,
        dressed_static_polarization_finite event transfer lambda positive i j]
    _ = _ := rfl

theorem source_prepared_photon_pi_explicit (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (lambda : ℂ)
    (positive : 0 < lambda.re) (j : Fin 289) :
    sourcePreparedPhotonPiColumn event transfer branch epsilon s n lambda j =
      ∑i, sourceNativeFrequencyPolarization branch epsilon s n i *
        explicitFullNoetherEntry event transfer lambda i j := by
  rw [source_prepared_photon_pi_column event transfer branch epsilon s n lambda positive j]
  simp_rw [source_prepared_pi_explicit event transfer lambda positive]

/-! The differentiated prepared field can be consumed without identifying it with the
undifferentiated ordinary photon amplitude.  This is the source-native Pi mouth used by
the C_EM matching consumer. -/
theorem actual_dressed_photon_connected_pi_feed
    (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (j : Fin 289) :
    (∫ t in Ioi (0 : ℝ), laplaceWeight lambda t *
      (∑ i : Fin 289,
        sourceNativeFrequencyPolarization branch epsilon s n i *
          (dressedNoetherJet event transfer (fun _ => ⟨fieldUnit j, 0, 0⟩) t i).value)) =
      ∑ i : Fin 289,
        sourceNativeFrequencyPolarization branch epsilon s n i *
          explicitFullNoetherEntry event transfer lambda i j := by
  have derivative (t : ℝ) :
      deriv (fun r : ℝ => sourcePreparedPhotonFieldRead event transfer branch epsilon s n
        t (r • fieldUnit j)) 0 =
        ∑ i : Fin 289, sourceNativeFrequencyPolarization branch epsilon s n i *
          (dressedNoetherJet event transfer (fun _ => ⟨fieldUnit j, 0, 0⟩) t i).value := by
    exact (source_prepared_photon_field_derivative event transfer branch epsilon s n
      (fieldUnit j) t).deriv
  have column := source_prepared_photon_pi_explicit event transfer branch epsilon s n lambda positive j
  unfold sourcePreparedPhotonPiColumn at column
  calc
    (∫ t in Ioi (0 : ℝ), laplaceWeight lambda t *
      (∑ i : Fin 289,
        sourceNativeFrequencyPolarization branch epsilon s n i *
          (dressedNoetherJet event transfer (fun _ => ⟨fieldUnit j, 0, 0⟩) t i).value)) =
        ∫ t in Ioi (0 : ℝ), laplaceWeight lambda t *
          deriv (fun r : ℝ => sourcePreparedPhotonFieldRead event transfer branch epsilon s n
            t (r • fieldUnit j)) 0 := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [derivative]
    _ = sourcePreparedPhotonPiColumn event transfer branch epsilon s n lambda j := by
      rfl
    _ = ∑ i : Fin 289,
        sourceNativeFrequencyPolarization branch epsilon s n i *
          explicitFullNoetherEntry event transfer lambda i j := column

end LowEnergy.GaussComposite.ActualSourcePreparedPhotonFieldResponse
