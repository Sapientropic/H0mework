import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPolarization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFiniteStaticRead
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalHalfAxis
open SourcePropagationNoetherTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedFieldTime
open ActualDressedSylvester ActualDressedSignal ActualDressedPencil
open Set MeasureTheory
open scoped Topology
attribute [local irreducible] dressedStaticPolarization noetherStaticHalf dressedNoetherJet
  dressedEulerObserver dressedKinematicPoint laplaceWeight finiteNumberFieldRead

/-- Read the field derivative of the unchanged finite number-sector expression. -/
def finiteConstantFieldSlope (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (t : ℝ) (i : Fin 289) : ℂ :=
  deriv (fun r : ℝ=>finiteNumberFieldRead event transfer (fieldUnit i) t (r • force)) 0

attribute [local irreducible] finiteConstantFieldSlope

theorem finite_constant_field_slope_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (t : ℝ) (i : Fin 289) :
    finiteConstantFieldSlope event transfer force t i=
      (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) t i).value := by
  unfold finiteConstantFieldSlope
  exact (actual_finite_number_field_quantum_derivative event transfer force t i).deriv

theorem finite_static_integrand_integrable (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    IntegrableOn (fun t=>laplaceWeight lambda t*finiteConstantFieldSlope event transfer force t i)
      (Ioi (0:ℝ)) := by
  simp_rw [finite_constant_field_slope_actual,dressed_noether_jet_original]
  simpa only [IntegrableOn,map_smul,smul_eq_mul] using!
    (dressedEulerObserver event).integrable_comp
      (noether_static_half_integrable (dressedKinematicPoint event transfer) (fieldUnit i)
        force lambda positive)

/-- The actual complete static polarization consumes the finite full-reader slope directly. -/
theorem dressed_static_polarization_finite (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (i j : Fin 289) :
    dressedStaticPolarization event transfer lambda i j=
      ∫t in Ioi (0:ℝ),laplaceWeight lambda t*
        finiteConstantFieldSlope event transfer (fieldUnit j) t i := by
  simp_rw [finite_constant_field_slope_actual,dressed_noether_jet_original]
  unfold dressedStaticPolarization
  symm
  simpa only [noetherStaticHalf,map_smul,smul_eq_mul] using!
    (dressedEulerObserver event).integral_comp_comm
      (noether_static_half_integrable (dressedKinematicPoint event transfer) (fieldUnit i)
        (fieldUnit j) lambda positive)

/-- The same original operator tail pays for this finite-expression read of actual Pi. -/
theorem finite_static_polarization_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re)
    (T : ℝ) (future : 0≤T) (i j : Fin 289) :
    ‖(∫t in Ioi (0:ℝ),laplaceWeight lambda t*
        finiteConstantFieldSlope event transfer (fieldUnit j) t i)-
      dressedWindowPolarization event transfer p lambda T i j‖ ≤
        dressedSignalTailPrice event transfer p lambda T := by
  rw [←dressed_static_polarization_finite event transfer lambda positive i j]
  exact dressed_static_polarization_tail event transfer p static lambda positive T future i j

end LowEnergy.GaussComposite.ActualDressedFiniteStaticRead
