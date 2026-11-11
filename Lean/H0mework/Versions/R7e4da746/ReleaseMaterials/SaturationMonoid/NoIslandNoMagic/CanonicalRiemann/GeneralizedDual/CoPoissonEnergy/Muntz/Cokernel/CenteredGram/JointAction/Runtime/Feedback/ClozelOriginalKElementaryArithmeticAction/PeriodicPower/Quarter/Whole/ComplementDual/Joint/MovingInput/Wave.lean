import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Seed
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaNativePortMoments
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Wave
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson
open OriginalKCrossParameterRAdjointSource.PaNativePortSource
open OriginalKCrossParameterRAdjointSource.PaNativePortMoments
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Seed
open scoped Topology InnerProductSpace
open private position_exterior_read fourier_exterior_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Source
local notation "P" => burnolEvenAmbientProjection
local notation "F" => fourierL2
local notation "T" => burnolTateReciprocalL2
local notation "ν" => burnolMobiusSourceL2
local notation "q" => (1 / 4 : ℝ)
local notation "Pa" => burnolCompactCoPoissonClosedRange.toSubmodule
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner

private def originalSeed (c : BurnolCompletedMellinCoordinate) (h : ℝ) (side : Bool) : BurnolL2 :=
  if side then fourierSeed c h else positionSeed c h

private def originalWave (c : BurnolCompletedMellinCoordinate) (h : ℝ) (side : Bool) : BurnolL2 :=
  if side then fourierWave c h else positionWave c h

private theorem seed_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ) (side : Bool) (nonnegative : 0 ≤ h) :
    (originalSeed c h side : ℝ → ℂ) =ᵐ[volume]
      bandRaw h (if side then burnolRieszSingleFourierSourceRaw c else positionSource c) := by
  cases side
  · change (positionSeed c h : ℝ → ℂ) =ᵐ[volume] bandRaw h (positionSource c)
    rw [positionSeed_eq_exterior c h nonnegative]
    exact position_exterior_read c h nonnegative
  · change (fourierSeed c h : ℝ → ℂ) =ᵐ[volume] bandRaw h (burnolRieszSingleFourierSourceRaw c)
    rw [fourierSeed_eq_exterior c h nonnegative]
    exact fourier_exterior_read c h nonnegative

private theorem wave_member (c : BurnolCompletedMellinCoordinate) (h : ℝ) (side : Bool)
    (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : originalWave c h side ∈ burnolOriginalPaInL2 := by
  cases side
  · exact positionWave_inPa c h nonnegative bounded
  · exact fourierWave_inPa c h nonnegative bounded

private theorem physical_wave (c : BurnolCompletedMellinCoordinate) (h : ℝ) (side : Bool)
    (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    (P (originalWave c h side) : BurnolL2) = originalWave c h side := by
  obtain ⟨actual, _, same⟩ := Submodule.mem_map.mp (wave_member c h side nonnegative bounded)
  change (actual : BurnolL2) = originalWave c h side at same
  rw [← same]
  simp only [burnolEvenAmbientProjection, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

private theorem physical_wave_member (c : BurnolCompletedMellinCoordinate) (h : ℝ) (side : Bool)
    (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    P (originalWave c h side) ∈ burnolCompactCoPoissonClosedRange := by
  obtain ⟨actual, inside, same⟩ := Submodule.mem_map.mp (wave_member c h side nonnegative bounded)
  change (actual : BurnolL2) = originalWave c h side at same
  rw [← same]
  simp only [burnolEvenAmbientProjection, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact inside

/-- The original two wave writers recover their literal finite seeds through the actual inverse source. -/
theorem actual_original_wave_inverse_source (c : BurnolCompletedMellinCoordinate) (h : ℝ) (side : Bool)
    (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    ν (P (originalWave c h side)) = originalSeed c h side := by
  have raw := seed_raw c h side nonnegative
  have even : reflectL2 (originalSeed c h side) = originalSeed c h side :=
    burnolReflectL2_eq_of_even_raw _ _ raw (fun x => by simp only [bandRaw, abs_neg])
  have gap : (originalSeed c h side : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae raw, ae_restrict_mem (measurableSet_symmetricInterval q)] with x read inside
    rw [read, bandRaw, if_neg (fun active => (not_lt_of_ge (abs_le.mpr inside)) active.1)]
  have realizes (test : SchwartzMap ℝ ℂ) : burnolRemainderSourceRead (originalSeed c h side) test =
      ∫ x : ℝ, test x * (P (originalWave c h side) : BurnolL2) x := by
    rw [physical_wave c h side nonnegative bounded]
    cases side
    · simpa only [originalSeed, originalWave, Bool.false_eq_true, if_false,
        Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
        using positionSeed_realizes c h nonnegative test
    · simpa only [originalSeed, originalWave, if_true,
        Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
        using fourierSeed_realizes c h nonnegative test
  have inverse := burnolRemainderSourceRead_cutoff_source _ _ even gap realizes
  rw [inverse]
  have radius : q * Real.exp h ≤ 4 := by
    have scale : Real.exp h ≤ 2 := (Real.exp_le_exp.mpr bounded).trans_eq (Real.exp_log (by norm_num))
    nlinarith
  apply Lp.ext
  filter_upwards [burnolRadiusZeroExtension_coe (burnolRadiusRestriction 4 (originalSeed c h side)),
    (ae_restrict_iff' (measurableSet_symmetricInterval (4 : ℝ))).mp
      (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (4 : ℝ)) (originalSeed c h side)), raw] with x extended restricted read
  rw [extended]
  by_cases inside : x ∈ symmetricInterval 4
  · rw [indicator_of_mem inside]
    exact restricted inside
  · rw [indicator_of_notMem inside, read, bandRaw,
      if_neg (fun active => inside (abs_le.mp (active.2.trans radius)))]

def originalPaPair (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolPaAmbientCarrier :=
  (1 / 2 : ℂ) • (P (positionWave c h) + evenFaceFourierEquiv burnolUnscaledCommonGapRadius (P (fourierWave c h)))

private theorem originalPaPair_mem (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : originalPaPair c h ∈ burnolCompactCoPoissonClosedRange := by
  apply Pa.smul_mem
  apply Pa.add_mem
  · exact physical_wave_member c h false nonnegative bounded
  · exact burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange
      (physical_wave_member c h true nonnegative bounded)

theorem actual_original_pair_tate_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    T (ν (originalPaPair c h)) = jointInput c zero h := by
  rw [actual_joint_input_original_seeds c zero h nonnegative bounded]
  have left := actual_original_wave_inverse_source c h false nonnegative bounded
  have right := actual_original_wave_inverse_source c h true nonnegative bounded
  change ν (P (positionWave c h)) = positionSeed c h at left
  change ν (P (fourierWave c h)) = fourierSeed c h at right
  have fourier := burnolMobiusSource_fourier (P (fourierWave c h))
    (physical_wave_member c h true nonnegative bounded)
  rw [originalPaPair, map_smul, map_add, map_smul, map_add,
    fourier, left, right, burnolTateReciprocalL2_involutive]

/-- The new same-K Pa feedback is the original R correction of the original two waves. -/
theorem actual_jointPa_original_correction (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    jointPa c zero h = burnolPaSourceCorrection c ⟨originalPaPair c h, originalPaPair_mem c h nonnegative bounded⟩ := by
  rw [jointPa, ← actual_original_pair_tate_source c zero h nonnegative bounded]
  exact sourceVolterraPhysical_original_correction c _ (originalPaPair_mem c h nonnegative bounded)

def originalPairInput (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : ↥Pa :=
  ⟨originalPaPair c h, originalPaPair_mem c h nonnegative bounded⟩

/-- Every original Unit4 fee is read from these two actual source feet. -/
theorem actual_original_pair_port (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (j : ℕ) :
    port c j (originalPairInput c h nonnegative bounded) =
      (2 : ℂ) * (-2 : ℂ)^j / (j.factorial : ℂ) *
        ∫ t : ℝ in Icc q 4, (t : ℂ)^(-c.value) * (Real.log (t / q) : ℂ)^j * jointInput c zero h t := by
  rw [actual_port_log_moment]
  change _ * (∫ t : ℝ in Icc q 4, _ * _ * T (ν (originalPaPair c h)) t) = _
  rw [actual_original_pair_tate_source c zero h nonnegative bounded]

/-- The literal original m-th R step consumes the entire computed Unit4 fee. -/
theorem actual_original_pair_order_R (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    burnolDirectRightResolventCLM c
      ((loop c (order c.value - 1) (originalPairInput c h nonnegative bounded) : BurnolPaAmbientCarrier) : BurnolL2) =
      ((loop c (order c.value) (originalPairInput c h nonnegative bounded) : BurnolPaAmbientCarrier) : BurnolL2) +
        ((2 : ℂ) * (-2 : ℂ)^(order c.value - 1) / ((order c.value - 1).factorial : ℂ) *
          ∫ t : ℝ in Icc q 4, (t : ℂ)^(-c.value) * (Real.log (t / q) : ℂ)^(order c.value - 1) *
            jointInput c zero h t) • burnolUnitTailResponse c 4 := by
  have actual := actual_original_R c (order c.value - 1) (originalPairInput c h nonnegative bounded)
  have positive := generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  change 0 < order c.value at positive
  rw [Nat.sub_add_cancel positive, actual_original_pair_port c zero h nonnegative bounded] at actual
  exact actual

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Wave
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
