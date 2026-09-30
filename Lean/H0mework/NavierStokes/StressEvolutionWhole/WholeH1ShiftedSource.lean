import H0mework.NavierStokes.StressWholeH1.OriginalSource
import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeWholeH1ShiftedSource

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeOriginalResolventInput NativeResolventCompactness NativeWholeH1OriginalSource

noncomputable section

private theorem shifted_pair_ae {P : Icc (0 : ℝ) 1 → Prop} {left right shift : ℝ}
    (source : ∀ᵐ time ∂commonTimeMeasure 1, P time)
    (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    ∀ᵐ time ∂volume.restrict (Icc left right),
      P (projIcc 0 1 zero_le_one time) ∧ P (projIcc 0 1 zero_le_one (time + shift)) := by
  have common : commonTimeMeasure 1 =
      Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  have interval : ∀ᵐ time ∂volume.restrict (Icc (0 : ℝ) 1), P (projIcc 0 1 zero_le_one time) := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).mpr
    rw [common] at source
    simpa only [projIcc_val] using source
  have extended := (ae_restrict_iff' measurableSet_Icc).mp interval
  have translated := (measurePreserving_add_right (volume : Measure ℝ) shift).quasiMeasurePreserving.ae extended
  filter_upwards [ae_restrict_of_ae extended, ae_restrict_of_ae translated,
    ae_restrict_mem measurableSet_Icc] with time first last inside
  exact ⟨first (firstInside inside), last (lastInside inside)⟩

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

/-- Both physical times retain the same original source and the same already generated sequence. -/
theorem source_faces_shifted_ae (source : StressAt escape) (pointLe : point ≤ 1)
    (left right shift : ℝ) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    ∀ᵐ time ∂volume.restrict (Icc left right),
      (Summable (curlDensity (meanInput source pointLe (.fixed (projIcc 0 1 zero_le_one time))).1) ∧
        Tendsto (fun n => originalInput source pointLe
          ((NativeRecoveryTimeStrongRefinement.generated source pointLe).index n)
          (.fixed (projIcc 0 1 zero_le_one time))) atTop
          (𝓝 (meanInput source pointLe (.fixed (projIcc 0 1 zero_le_one time))))) ∧
      (Summable (curlDensity (meanInput source pointLe (.fixed (projIcc 0 1 zero_le_one (time + shift)))).1) ∧
        Tendsto (fun n => originalInput source pointLe
          ((NativeRecoveryTimeStrongRefinement.generated source pointLe).index n)
          (.fixed (projIcc 0 1 zero_le_one (time + shift)))) atTop
          (𝓝 (meanInput source pointLe (.fixed (projIcc 0 1 zero_le_one (time + shift)))))) :=
  shifted_pair_ae ((meanInput_curl_summable_ae source pointLe).and (originalInput_strong_ae source pointLe))
    firstInside lastInside

end
end SaturationMonoid.NavierStokes.NativeWholeH1ShiftedSource
