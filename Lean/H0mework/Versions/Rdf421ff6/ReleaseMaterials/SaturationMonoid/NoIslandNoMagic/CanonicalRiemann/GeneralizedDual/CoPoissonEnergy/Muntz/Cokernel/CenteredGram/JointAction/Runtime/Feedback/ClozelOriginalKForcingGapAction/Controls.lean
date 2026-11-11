import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local notation "q" => (1/4 : ℝ)

private theorem seed_quarter : burnolQuarterRestriction ConstantDual.seed = (1 : ℂ) • intervalConstant q := by
  change burnolQuarterRestriction (burnolQuarterZeroExtension (intervalConstant q)) = _
  rw [burnolQuarterRestriction_zeroExtension,one_smul]

private theorem seed_inner : inner ℂ ConstantDual.seed ConstantDual.seed = (1/2 : ℂ) := by
  have read := inward_constant_contact _ _ seed_quarter 0 (by norm_num)
  simpa only [neg_zero,zero_div,Real.exp_zero,Complex.ofReal_one,burnolMultiplicativeDilation_zero,star_one,mul_one] using read

private theorem outward_shell_constant_orthogonal (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ ConstantDual.seed (outwardConstantShell h) = 0 := by
  have paired : inner ℂ ConstantDual.seed (outwardConstantShell h) =
      inner ℂ (intervalConstant q) (burnolQuarterRestriction (outwardConstantShell h)) :=
    ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _
  rw [paired,outwardConstantShell_quarter_zero h nonnegative,inner_zero_right]

/-- The retained shell has exact source energy, independent of its pairing with a resolvent column. -/
theorem outward_shell_norm_sq (h : ℝ) (nonnegative : 0 ≤ h) :
    ‖outwardConstantShell h‖^2 = (1-Real.exp (-h))/2 := by
  have orthogonal := outward_shell_constant_orthogonal h nonnegative
  have reverseOrthogonal := inner_eq_zero_symm.mp orthogonal
  have source := (burnolMultiplicativeDilation (-h)).inner_map_map ConstantDual.seed ConstantDual.seed
  have decomposed : burnolMultiplicativeDilation (-h) ConstantDual.seed =
      outwardConstantShell h + (Real.exp (-h/2) : ℂ) • ConstantDual.seed := by
    simp only [outwardConstantShell,sub_add_cancel]
  simp only [decomposed,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    orthogonal,reverseOrthogonal,seed_inner,mul_zero,add_zero] at source
  have densityReal : (starRingEnd ℂ) (Real.exp (-h/2) : ℂ) = (Real.exp (-h/2) : ℂ) :=
    Complex.conj_ofReal _
  rw [densityReal] at source
  have densitySquared : (Real.exp (-h/2) : ℂ)*(Real.exp (-h/2) : ℂ) = (Real.exp (-h) : ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 1
    ring
  have energy : inner ℂ (outwardConstantShell h) (outwardConstantShell h) =
      (1-(Real.exp (-h) : ℂ))/2 := by
    linear_combination source - (1/2 : ℂ)*densitySquared
  have realEnergy : inner ℂ (outwardConstantShell h) (outwardConstantShell h) =
      (((1-Real.exp (-h))/2 : ℝ) : ℂ) := by
    convert! energy using 1
    push_cast
    rfl
  calc
    ‖outwardConstantShell h‖^2 = (inner ℂ (outwardConstantShell h) (outwardConstantShell h)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) (outwardConstantShell h)).symm
    _ = (1-Real.exp (-h))/2 := by rw [realEnergy];rfl

theorem original_outward_shell_nonzero : outwardConstantShell (Real.log stageZeroSonineQ) ≠ 0 := by
  have positive : 0 < Real.log stageZeroSonineQ := by
    apply Real.log_pos
    change 1 < Real.sqrt 3
    have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have nonnegative := Real.sqrt_nonneg 3
    nlinarith
  have energy := outward_shell_norm_sq (Real.log stageZeroSonineQ) positive.le
  have exponential : Real.exp (-Real.log stageZeroSonineQ) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  intro zero
  rw [zero,norm_zero] at energy
  norm_num at energy
  linarith

theorem outward_shell_zero_shift : outwardConstantShell 0 = 0 := by
  simp only [outwardConstantShell,neg_zero,zero_div,Real.exp_zero,Complex.ofReal_one,
    burnolMultiplicativeDilation_zero,one_smul,sub_self]

theorem regular0_contact_zero_shift (coordinate : BurnolCompletedMellinCoordinate) :
    finitePair coordinate 0 (regularColumns coordinate 0) ConstantDual.seed +
    finitePair coordinate 0 ConstantDual.seed (regularColumns coordinate 0) +
    finitePair coordinate 0 ConstantDual.seed ConstantDual.seed = 0 := by
  have source := regular0_contact_calculated coordinate 0 (by norm_num)
  rw [outward_shell_zero_shift] at source
  norm_num [pairedMellinTranslationCharacter,fullMellinTranslationCharacter,
    reciprocalMellinTranslationCharacter] at source
  exact source

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (rightHalf : 1/2<observation.coordinate.re)
local notation "c" => originalKCoordinate observation.coordinate
 (And.right (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial)) rightHalf
local notation "h" => Real.log stageZeroSonineQ
local notation "L" => star (sourceRate c)+sourceRate c

/-- Deleting the retained shell changes the actual residual by this exact source pairing; source energy does not assert that pairing nonzero. -/
theorem installed_omit_outward_shell_effect :
 (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual -
 L⁻¹ *
  (star (Kernel.A c)*Kernel.A c*(calculatedForcing00 c h -
    (L/2)*(inner ℂ (regularColumns c 0) (outwardConstantShell h) +
      star (inner ℂ (regularColumns c 0) (outwardConstantShell h)))) +
   star (Kernel.A c)*Kernel.beta c*sourceGramForcing c h 0 1 +
   star (Kernel.beta c)*Kernel.A c*sourceGramForcing c h 1 0 +
   star (Kernel.beta c)*Kernel.beta c*sourceGramForcing c h 1 1) =
  (star (Kernel.A c)*Kernel.A c/2)*
    (inner ℂ (regularColumns c 0) (outwardConstantShell h) +
      star (inner ℂ (regularColumns c 0) (outwardConstantShell h))) := by
  rw [installed_residual_calculated_contact]
  apply mul_left_cancel₀ (sourceRate_sum_ne_zero c)
  simp only [mul_sub,← mul_assoc,mul_inv_cancel₀ (sourceRate_sum_ne_zero c),one_mul]
  ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
