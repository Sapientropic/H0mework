import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedDampingCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedZeroDamping
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualCompositeFieldCurrent Filter Set
open scoped Matrix Topology
attribute [local irreducible] commonEMTensorNumerator commonDeterminant correctedEMTensor

private theorem positive_complex_punctured :
    Tendsto (fun sigma : ℝ => (sigma : ℂ)) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 ({0}ᶜ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero] using (ne_of_gt positive)

private theorem positive_chart (D : ℂ[X]) (nonzero : D≠0) :
    ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi 0), 0<sigma ∧ D.eval (sigma : ℂ)≠0 := by
  have inclusion : Ioi (0 : ℝ) ⊆ ({0}ᶜ) := by
    intro sigma positive
    simpa only [mem_compl_iff, mem_singleton_iff] using (ne_of_gt positive)
  filter_upwards [(source_static_punctured_chart D nonzero).filter_mono (nhdsWithin_mono 0 inclusion),
    self_mem_nhdsWithin] with sigma regular positive
  exact ⟨positive,regular⟩

def sourceDampingEMValue (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu => leadingPoleCoefficient (dampingEMFraction event eps n mu nu) 0

def sourceDampingProbeValue (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  leadingPoleCoefficient (dampingProbeFraction event eps n pd ps dL dR sL sR) 0

/-- Every actual EM entry keeps its own damping pole order and leading coefficient. -/
theorem actual_damping_em_order_return (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nonzero : dampingDeterminant event eps n≠0) (mu nu : Fin 4) :
    Tendsto (fun sigma : ℝ => (sigma : ℂ)^poleOrder (dampingEMFraction event eps n mu nu) 0*
      correctedEMTensor event eps 0 sigma n mu nu) (nhdsWithin 0 (Ioi 0))
        (𝓝 (sourceDampingEMValue event eps n mu nu)) := by
  have base := (pole_order_limit (dampingEMFraction event eps n mu nu) 0).comp positive_complex_punctured
  simp only [Function.comp_def, sub_zero] at base
  apply Tendsto.congr' _ base
  filter_upwards [positive_chart _ nonzero] with sigma chart
  exact congrArg (fun z : ℂ => (sigma : ℂ)^poleOrder (dampingEMFraction event eps n mu nu) 0*z)
    (actual_damping_em_fraction event eps sigma n chart.1 chart.2 mu nu).symm

/-- The independent prepared detector/source pair is read through the full original response. -/
theorem actual_damping_probe_order_return (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (nonzero : dampingDeterminant event eps n≠0) :
    Tendsto (fun sigma : ℝ => (sigma : ℂ)^poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0*
      correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR) (nhdsWithin 0 (Ioi 0))
        (𝓝 (sourceDampingProbeValue event eps n pd ps dL dR sL sR)) := by
  have base := (pole_order_limit (dampingProbeFraction event eps n pd ps dL dR sL sR) 0).comp positive_complex_punctured
  simp only [Function.comp_def, sub_zero] at base
  apply Tendsto.congr' _ base
  filter_upwards [positive_chart _ nonzero] with sigma chart
  exact congrArg (fun z : ℂ => (sigma : ℂ)^poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0*z)
    (actual_damping_probe_fraction event eps sigma n pd ps dL dR sL sR chart.1 chart.2).symm

theorem actual_zero_damping_em_return (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nonzero : dampingDeterminant event eps n≠0)
    (finite : ∀mu nu, poleOrder (dampingEMFraction event eps n mu nu) 0=0) :
    Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n) (nhdsWithin 0 (Ioi 0))
      (𝓝 (sourceDampingEMValue event eps n)) := by
  apply tendsto_pi_nhds.2
  intro mu
  apply tendsto_pi_nhds.2
  intro nu
  simpa only [finite mu nu, pow_zero, one_mul] using actual_damping_em_order_return event eps n nonzero mu nu

theorem actual_zero_damping_probe_return (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (nonzero : dampingDeterminant event eps n≠0)
    (finite : poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0=0) :
    Tendsto (fun sigma : ℝ => correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sourceDampingProbeValue event eps n pd ps dL dR sL sR)) := by
  simpa only [finite, pow_zero, one_mul] using
    actual_damping_probe_order_return event eps n pd ps dL dR sL sR nonzero

theorem singular_damping_no_original_chart (event : DressedEvent) (eps sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) (zero : dampingDeterminant event eps n=0) :
    correctedDet event eps 0 sigma n=0 := by
  by_contra regular
  have commonRegular := actual_common_determinant_nonzero event eps sigma 0 n positive regular
  rw [← damping_slice_eval] at commonRegular
  change (dampingDeterminant event eps n).eval (sigma : ℂ)≠0 at commonRegular
  rw [zero, eval_zero] at commonRegular
  exact commonRegular rfl

/-- Pole branches retain the complete principal packet. Finite return requires both the sixteen-entry tensor and the independent full probe to be regular. -/
inductive ZeroDampingReturn (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Type
  | singular (determinant_zero : dampingDeterminant event eps n=0)
  | polar (determinant_nonzero : dampingDeterminant event eps n≠0)
      (pole : (∃mu nu, 0<poleOrder (dampingEMFraction event eps n mu nu) 0) ∨
        0<poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0)
  | finite (determinant_nonzero : dampingDeterminant event eps n≠0)
      (tensor_orders : ∀mu nu, poleOrder (dampingEMFraction event eps n mu nu) 0=0)
      (probe_order : poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0=0)
      (tensor_return : Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (sourceDampingEMValue event eps n)))
      (probe_return : Tendsto (fun sigma : ℝ => correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (sourceDampingProbeValue event eps n pd ps dL dR sL sR)))

def sourceZeroDampingReturn (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ZeroDampingReturn event eps n pd ps dL dR sL sR := by
  classical
  by_cases zero : dampingDeterminant event eps n=0
  · exact .singular zero
  · by_cases emFinite : ∀mu nu, poleOrder (dampingEMFraction event eps n mu nu) 0=0
    · by_cases probeFinite : poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0=0
      · exact .finite zero emFinite probeFinite (actual_zero_damping_em_return event eps n zero emFinite)
          (actual_zero_damping_probe_return event eps n pd ps dL dR sL sR zero probeFinite)
      · exact .polar zero (Or.inr (Nat.pos_of_ne_zero probeFinite))
    · push Not at emFinite
      have pole : ∃mu nu, 0<poleOrder (dampingEMFraction event eps n mu nu) 0 := by
        obtain ⟨mu,nu,order⟩ := emFinite
        exact ⟨mu,nu,Nat.pos_of_ne_zero order⟩
      exact .polar zero (Or.inl pole)

end LowEnergy.GaussComposite.ActualDressedZeroDamping
