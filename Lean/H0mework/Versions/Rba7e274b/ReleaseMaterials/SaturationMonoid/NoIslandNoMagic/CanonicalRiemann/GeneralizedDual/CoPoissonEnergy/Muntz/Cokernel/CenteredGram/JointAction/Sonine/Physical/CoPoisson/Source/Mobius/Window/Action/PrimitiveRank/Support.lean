import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Source
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.UnitTail
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace

def pairedColumn (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0+
  burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate (-h)) 0

theorem sampled_tate_tail_zero (coordinate : BurnolCompletedMellinCoordinate) (column : BurnolL2) :
    inner ℂ (burnolAnnulusSamplingL2 column 0) (burnolTateReciprocalL2 (Paid.exteriorBase coordinate))=0 := by
  have same : Paid.exteriorBase coordinate=burnolNormalizedFirstSourceUnitTail coordinate := rfl
  rw [same,L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [burnolAnnulusSamplingL2_coeFn column 0,burnolNormalizedFirstSourceUnitTail_tate_coeFn coordinate]
    with x sample tail
  simp only [Pi.zero_apply]
  rw [sample,tail]
  unfold burnolAnnulusSamplingRaw
  simp only [Nat.cast_zero,zero_add,one_mul]
  by_cases inside : x∈burnolSamplingAnnulus
  · rw [indicator_of_mem inside,if_neg (not_lt_of_ge inside.1.le),inner_zero_right]
  · rw [indicator_of_notMem inside,inner_zero_left]

 theorem paired_tate_tail_zero (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (pairedColumn coordinate h) (burnolTateReciprocalL2 (Paid.exteriorBase coordinate))=0 := by
  rw [pairedColumn,inner_add_left,sampled_tate_tail_zero,sampled_tate_tail_zero,add_zero]

 theorem sampled_outer_tail_zero (coordinate : BurnolCompletedMellinCoordinate) (column : BurnolL2)
    (_supported : OriginalPaPhysicalGreen.originalPhysicalCutoff (1/2:ℝ) column=column) :
    inner ℂ (burnolAnnulusSamplingL2 column 0) (Paid.exteriorBase coordinate)=0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [burnolAnnulusSamplingL2_coeFn column 0,burnolRadiusUnitTail_coeFn coordinate 4 (by norm_num)] with x sample tail
  simp only [Pi.zero_apply]
  change (Paid.exteriorBase coordinate : ℝ→ℂ) x=_ at tail
  rw [sample,tail]
  unfold burnolAnnulusSamplingRaw
  simp only [Nat.cast_zero,zero_add,one_mul]
  by_cases outer : (4:ℝ) < |x|
  · rw [if_pos outer,indicator_of_notMem (show x∉burnolSamplingAnnulus from fun h=>not_le_of_gt outer h.2),inner_zero_left]
  · rw [if_neg outer,inner_zero_right]

 theorem paired_outer_tail_zero (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (bounded : |h|≤Real.log 2) : inner ℂ (pairedColumn coordinate h) (Paid.exteriorBase coordinate)=0 := by
  rw [pairedColumn,inner_add_left,sampled_outer_tail_zero coordinate _ (OriginalRieszFiniteColumns.fourierColumn_half coordinate h bounded),
    sampled_outer_tail_zero coordinate _ (OriginalRieszFiniteColumns.fourierColumn_half coordinate (-h) (by simpa only [abs_neg] using bounded)),add_zero]

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
