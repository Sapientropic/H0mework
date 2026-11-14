import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.MellinRead

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.CountingMellin
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.FiniteMellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.MellinRead
open scoped Topology InnerProductSpace
open private physical_quarter from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.InitialLog
local notation "q" => (1 / 4 : ℝ)
local notation "AN" => FiniteForcing.source

theorem actual_physical_cotest_mellin (c d : BurnolCompletedMellinCoordinate) :
    HasMellin (physicalCotest c : ℝ → ℂ) (1 - d.value)
      (burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2)) := by
  apply actual_position_gap_mellin
  exact mem_locallyConstantFace_iff_exists.mpr ⟨nativeCotestGap c, (physical_quarter c).symm⟩

/-- At the same finite cutoff, the full continuous forcing yields the actual zeta coefficient of the physical cotest. -/
theorem actual_finite_cotest_mellin (c d : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    HasMellin (AN N (physicalCotest c : BurnolL2) : ℝ → ℂ) (1 - d.value)
      (FiniteForcing.coefficient d.value N *
        burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2)) := by
  have source := actual_finite_source_mellin (physicalCotest c : BurnolL2) (1 - d.value)
    (burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2)) N positive
    (by simp only [sub_re, one_re]; linarith [d.belowOne]) (actual_physical_cotest_mellin c d)
  simpa only [FiniteForcing.coefficient, show (1 - d.value) - 1 = -d.value by ring] using source

private theorem finite_ambient_price (c d : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    burnolAmbientCompletedMellinEvaluator d (AN N (physicalCotest c : BurnolL2)) -
      nativeCotestGap c * (d.value * (q : ℂ) ^ (1 - d.value) / (1 - d.value)^2) =
        FiniteForcing.coefficient d.value N *
          burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2) := by
  have honest := actual_log_quarter_mellin d (AN N (physicalCotest c : BurnolL2))
    (nativeCotestGap c) (actual_native_initial_log_finite c N positive)
  exact honest.2.symm.trans (actual_finite_cotest_mellin c d N positive).2

/-- The actual sharp L2 graph supplies Mellin convergence through its fixed logarithmic quarter and complete mean. -/
theorem actual_counted_cotest_ambient_price (c d : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    burnolAmbientCompletedMellinEvaluator d (pairedCotestForward c) -
      nativeCotestGap c * (d.value * (q : ℂ) ^ (1 - d.value) / (1 - d.value)^2) =
        riemannZeta d.value * burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2) := by
  have graph := actual_paired_cotest_forward c zero
  change Tendsto (fun N : ℕ => AN N (physicalCotest c : BurnolL2)) atTop
    (𝓝 (pairedCotestForward c)) at graph
  have read := ((burnolAmbientCompletedMellinEvaluator d).continuous.tendsto _).comp graph
  have left := read.sub_const
    (nativeCotestGap c * (d.value * (q : ℂ) ^ (1 - d.value) / (1 - d.value)^2))
  have right := (DirichletCoefficient.coefficient_tendsto_riemannZeta d.value
    (by linarith [d.rightHalf]) (by intro same; simpa [same] using d.belowOne)).mul_const
      (burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2))
  have same := left.congr' (show (fun N : ℕ =>
      burnolAmbientCompletedMellinEvaluator d (AN N (physicalCotest c : BurnolL2)) -
        nativeCotestGap c * (d.value * (q : ℂ) ^ (1 - d.value) / (1 - d.value)^2)) =ᶠ[atTop]
      (fun N : ℕ => FiniteForcing.coefficient d.value N *
        burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2)) from by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with N after
      exact finite_ambient_price c d N (by omega))
  exact tendsto_nhds_unique same right

/-- This is the actual native cotest, with the original zeta factor rather than an assumed zero read. -/
theorem actual_counted_cotest_mellin (c d : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    HasMellin (pairedCotestForward c : ℝ → ℂ) (1 - d.value)
      (riemannZeta d.value * burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2)) := by
  have quarter := actual_native_initial_log c zero
  change Constructor.zeroMean (burnolQuarterRestriction (pairedCotestForward c)) =
    nativeCotestGap c • CenteredCountingDual.logarithm at quarter
  have source := actual_log_quarter_mellin d (pairedCotestForward c) (nativeCotestGap c) quarter
  rw [actual_counted_cotest_ambient_price c d zero] at source
  exact source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.CountingMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
