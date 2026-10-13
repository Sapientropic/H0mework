import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.ColumnPullback
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

theorem actual_compact_pullback (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ+)
    (actual : n∈burnolCenteredMobiusCutoffFinset 4) :
    F.cutoff 4 (F.fullPullback n (wholeContactResponse coordinate))=F.fullPullback n (wholeContactResponse coordinate) := by
  have inventory : (n:ℕ)<16 := by
    have source := (mem_burnolCenteredMobiusCutoffFinset 4 n).mp actual
    norm_num [burnolCenteredMobiusCutoff] at source
    exact source
  have small : ((n:ℕ):ℝ)<16 := by exact_mod_cast inventory
  have positive : (0:ℝ)<(n:ℕ) := by exact_mod_cast n.property
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ=>x/(n:ℕ)) volume volume := by
    simpa only [div_eq_mul_inv,mul_comm,smul_eq_mul] using Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
      (r:=((n:ℕ):ℝ)⁻¹) (inv_ne_zero positive.ne')
  apply Lp.ext
  filter_upwards [F.cutoff_read 4 (F.fullPullback n (wholeContactResponse coordinate)),
    full_pullback_read n (wholeContactResponse coordinate),qmp.ae_eq (whole_contact_response_read coordinate)] with x cut pulled source
  simp only [Function.comp_def] at source
  rw [cut]
  by_cases inside : x∈symmetricInterval 4
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,pulled,source,indicator_of_notMem]
    intro quarter
    have bound : |x/(n:ℕ)|≤(1/4:ℝ) := abs_le.mpr quarter
    rw [abs_div,abs_of_pos positive,div_le_iff₀ positive] at bound
    exact inside (abs_le.mp (by nlinarith : |x|≤4))

 theorem actual_response_full_word (coordinate : BurnolCompletedMellinCoordinate) :
    FiniteMobiusResolventFlux.M (wholeContactResponse coordinate)=
      ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,FiniteMobiusResolventFlux.coefficient n •
        F.fullPullback n (wholeContactResponse coordinate) := by
  rw [F.lower_source_cutoff,whole_contact_response_mean]
  simp only [zero_smul,sub_zero]
  apply Finset.sum_congr rfl
  intro n actual
  rw [actual_compact_pullback coordinate n actual]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
