import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.SameN

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.QuarterShell
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalKFiniteOrderRelease OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalRieszSource OriginalUnitMellinSource.Fourier
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.ConjugateLow OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.OppositeForcing
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FixedShell
open scoped InnerProductSpace Topology
open private tf_power from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.Sawtooth
open private allPa_K_power_zero allPa_fourier_power_zero
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
local notation "q" => (1/4 : ℝ)
local notation "R" => burnolDirectRightResolventCLM
local notation "K" => burnolCompletedMellinRieszVector
local notation "Fou" => fourierL2
local notation "T" => burnolTateReciprocalL2
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The reciprocal programme admits its upper endpoint four, so the q shell is generated without a radius limit. -/
theorem actual_quarter_shell_mem (coordinate : BurnolCompletedMellinCoordinate) :
    burnolUnitPowerShellWave coordinate q ∈ burnolOriginalPaInL2 := by
  unfold burnolUnitPowerShellWave
  apply burnolWeightedReciprocalStepWave_inPa q q⁻¹ _ _ (by norm_num) (by norm_num)
    (burnolUnitPowerSlope_continuous coordinate).continuousOn

theorem actual_quarter_shell_realizes (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead
      (burnolRadiusNormalizedUnitTail coordinate q (by norm_num)-burnolNormalizedFirstSourceUnitTail coordinate) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolUnitPowerShellWave coordinate q)) test := by
  rw [←burnolUnitPowerStep_source_eq_actualShell coordinate q (by norm_num) (by norm_num)]
  exact burnolWeightedReciprocalStepSource_realizes q q⁻¹ _ _ (by norm_num) (by norm_num) (by norm_num)
    (burnolUnitPowerSlope_continuous coordinate).continuousOn test

theorem actual_quarter_shell_field (coordinate : BurnolCompletedMellinCoordinate) :
    burnolUnitTailResponse coordinate q-burnolUnitTailResponse coordinate 4 =
      burnolUnitPowerShellWave coordinate q := by
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    (burnolUnitTailResponse coordinate q-burnolUnitTailResponse coordinate 4)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolUnitPowerShellWave coordinate q)) test
  have read := actual_quarter_shell_realizes coordinate test
  rw [←burnolRemainderSourceReadCLM_apply,map_sub,burnolRemainderSourceReadCLM_apply,
    burnolRemainderSourceReadCLM_apply,burnolUnitTailResponse_realizes coordinate q (by norm_num) (by norm_num),
    burnolOriginalUnitTail_realizes] at read
  simpa only [map_sub,sub_apply] using read

def quarterShellPa (coordinate : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  ⟨burnolUnitPowerShellWave coordinate q, by
    obtain ⟨value,_,same⟩ := Submodule.mem_map.mp (actual_quarter_shell_mem coordinate)
    rw [←same]
    exact value.property⟩

theorem actual_quarter_shell_Pa (coordinate : BurnolCompletedMellinCoordinate) :
    quarterShellPa coordinate ∈ burnolCompactCoPoissonClosedRange := by
  obtain ⟨value,inside,same⟩ := Submodule.mem_map.mp (actual_quarter_shell_mem coordinate)
  have exactState : value=quarterShellPa coordinate := Subtype.ext same
  exact exactState ▸ inside

def quarterUnitPower (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) : BurnolL2 :=
  ((R coordinate)^j) (burnolUnitTailResponse coordinate q)

/-- The two whole sawtooth columns remain coupled at the original q clock. -/
theorem actual_quarter_power_sawtooth_field (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) :
    T (Fou (quarterUnitPower coordinate j)) = (q : ℂ)^(-coordinate.value) •
      ((((R coordinate)^j) OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.value)+
        (coordinate.value/2) • (((R coordinate)^(j+1)) OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.value)) := by
  have source := congrArg T (actual_unit_quarter_fourier coordinate)
  rw [map_smul,burnolTateReciprocalL2_involutive] at source
  unfold quarterUnitPower
  rw [tf_power,source,map_smul,map_add,map_smul,pow_succ,mul_apply_eq_comp]
  rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : ℕ,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "Rpow" => CombSource.Division.rawIterate observation half.down
include nontrivial

omit nontrivial in
theorem actual_quarter_power_field (j : ℕ) :
    quarterUnitPower c j=unitPower observation half j+Rpow j (quarterShellPa c : BurnolL2) := by
  have source : burnolUnitTailResponse c q=burnolUnitTailResponse c 4+(quarterShellPa c : BurnolL2) := by
    change _=burnolUnitTailResponse c 4+burnolUnitPowerShellWave c q
    rw [←actual_quarter_shell_field]
    abel
  unfold quarterUnitPower
  rw [source,map_add]
  rfl

/-- All independent conjugate readers consume the same actual shell through the complete m range. -/
theorem actual_quarter_conjugate_reads (j : ℕ) (atMost : j≤m) :
    inner ℂ (K (barC c) : BurnolL2) (quarterUnitPower c j)=
      inner ℂ (K (barC c) : BurnolL2) (unitPower observation half j) ∧
    inner ℂ (Fou (K (barC c) : BurnolL2)) (quarterUnitPower c j)=
      inner ℂ (Fou (K (barC c) : BurnolL2)) (unitPower observation half j) := by
  rw [actual_quarter_power_field observation half j]
  rw [inner_add_right,inner_add_right,
    actual_conjugate_K_Pa_power_zero observation nontrivial half _ (actual_quarter_shell_Pa c) j atMost,
    actual_conjugate_FK_Pa_power_low observation nontrivial half _ (actual_quarter_shell_Pa c) j atMost,
    add_zero,add_zero]
  exact ⟨rfl,rfl⟩

theorem actual_quarter_K_read (j : ℕ) (atMost : j≤m) :
    inner ℂ (K c : BurnolL2) (quarterUnitPower c j)=inner ℂ (K c : BurnolL2) (unitPower observation half j) := by
  rw [actual_quarter_power_field observation half j,inner_add_right,
    allPa_K_power_zero observation nontrivial half _ (actual_quarter_shell_Pa c) j atMost,add_zero]

theorem actual_quarter_FK_low (j : ℕ) (before : j<m) :
    inner ℂ (Fou (K c : BurnolL2)) (quarterUnitPower c j)=
      inner ℂ (Fou (K c : BurnolL2)) (unitPower observation half j) := by
  rw [actual_quarter_power_field observation half j,inner_add_right,
    allPa_fourier_power_zero observation nontrivial half _ (actual_quarter_shell_Pa c) j before,add_zero]

/-- The same-parameter m column retains its genuine Pa source top contact. -/
theorem actual_quarter_combo_top :
    inner ℂ (sourceKernelCombo c) (quarterUnitPower c m)=
      inner ℂ (sourceKernelCombo c) (unitPower observation half m)+
        feedbackCoefficient observation half*burnolPaResolventSourceCoefficient c (quarterShellPa c) := by
  rw [actual_quarter_power_field observation half m,inner_add_right,
    actual_Pa_power_source observation nontrivial half _ (actual_quarter_shell_Pa c)]

theorem actual_quarter_outside (j : ℕ) (atMost : j≤m) :
    O (quarterUnitPower c j)=O (unitPower observation half j) := by
  have physical := CombSource.Division.whole_pa_physical observation nontrivial half.down j atMost
    _ (actual_quarter_shell_Pa c)
  have outside : O (Rpow j (quarterShellPa c : BurnolL2))=0 := by
    exact Submodule.starProjection_orthogonal_apply_eq_zero physical
  rw [actual_quarter_power_field observation half j,map_add,outside,add_zero]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.QuarterShell
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
