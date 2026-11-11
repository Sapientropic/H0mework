import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source

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
local notation "mu" => burnolQuarterMeanCoefficient (burnolTruncatedFourier (Response.u : BurnolQuarterIntervalL2))

/-- The actual expanding constant shell is retained as its own full L² source. -/
def outwardConstantShell (h : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation (-h) ConstantDual.seed - (Real.exp (-h/2) : ℂ) • ConstantDual.seed

private theorem seed_quarter : burnolQuarterRestriction ConstantDual.seed = (1 : ℂ) • intervalConstant q := by
  change burnolQuarterRestriction (burnolQuarterZeroExtension (intervalConstant q)) = _
  rw [burnolQuarterRestriction_zeroExtension,one_smul]

theorem outwardConstantShell_quarter_zero (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolQuarterRestriction (outwardConstantShell h) = 0 := by
  unfold outwardConstantShell
  rw [map_sub,map_smul,quarter_dilation_constant _ _ seed_quarter (-h) (by linarith),seed_quarter]
  simp only [mul_one,smul_smul,mul_one,sub_self]

private theorem reverse_dilation_pair (left right : BurnolL2) (h : ℝ) :
    inner ℂ left (burnolMultiplicativeDilation h right) =
      star (inner ℂ right (burnolMultiplicativeDilation (-h) left)) := by
  have flip := (burnolMultiplicativeDilation h).inner_map_eq_flip right left
  rw [← burnolMultiplicativeDilation_neg_eq_symm h] at flip
  simpa only [Complex.star_def,inner_conj_symm] using (congrArg star flip)

/-- All three contact Grams now contain one retained outward-shell pairing and computed inward data. -/
theorem regular0_contact_calculated (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    finitePair coordinate h (regularColumns coordinate 0) ConstantDual.seed +
    finitePair coordinate h ConstantDual.seed (regularColumns coordinate 0) +
    finitePair coordinate h ConstantDual.seed ConstantDual.seed =
      (((Real.exp (-h/2) : ℂ)/2) - pairedMellinTranslationCharacter coordinate.value h/2) *
        (1 + (mu+1/2-sourceRate coordinate)/star coordinate.value +
          star ((mu+1/2-sourceRate coordinate)/star coordinate.value)) +
      (1/2 : ℂ) * (inner ℂ (regularColumns coordinate 0) (outwardConstantShell h) +
        star (inner ℂ (regularColumns coordinate 0) (outwardConstantShell h))) := by
  have inward := regular0_inward_constant_contact coordinate h nonnegative
  have stationary := regular0_inward_constant_contact coordinate 0 (by norm_num)
  simp only [neg_zero,zero_div,Real.exp_zero,Complex.ofReal_one,burnolMultiplicativeDilation_zero] at stationary
  have constant := inward_constant_contact _ _ seed_quarter h nonnegative
  simp only [star_one,mul_one] at constant
  have self := inward_constant_contact _ _ seed_quarter 0 (by norm_num)
  simp only [neg_zero,zero_div,Real.exp_zero,Complex.ofReal_one,burnolMultiplicativeDilation_zero,star_one,mul_one] at self
  have outward : inner ℂ (regularColumns coordinate 0) (burnolMultiplicativeDilation (-h) ConstantDual.seed) =
      (Real.exp (-h/2) : ℂ) * inner ℂ (regularColumns coordinate 0) ConstantDual.seed +
        inner ℂ (regularColumns coordinate 0) (outwardConstantShell h) := by
    simp only [outwardConstantShell,inner_sub_right,inner_smul_right]
    ring
  have reverseOut := reverse_dilation_pair ConstantDual.seed (regularColumns coordinate 0) h
  have reverseIn := reverse_dilation_pair ConstantDual.seed (regularColumns coordinate 0) (-h)
  simp only [neg_neg] at reverseIn
  have reverseConstant := reverse_dilation_pair ConstantDual.seed ConstantDual.seed (-h)
  simp only [neg_neg] at reverseConstant
  have stationaryReverse : inner ℂ ConstantDual.seed (regularColumns coordinate 0) =
      star (inner ℂ (regularColumns coordinate 0) ConstantDual.seed) := by
    exact (inner_conj_symm _ _).symm
  unfold finitePair
  rw [inner_add_right,inner_add_right,inner_add_right,inward,outward,reverseOut,reverseIn,
    reverseConstant,inward,constant,stationaryReverse,stationary,self]
  rw [outward,stationary]
  have realScalar : star (Real.exp (-h/2) : ℂ) = (Real.exp (-h/2) : ℂ) := by
    exact Complex.conj_ofReal _
  simp only [star_add,star_mul,star_div₀,star_ofNat,star_one,star_star,realScalar]
  ring

/-- The determined first contact is built from B's actual mean and its retained R-source shell. -/
def calculatedForcing00 (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  finitePair coordinate h (regularForcing coordinate 0) (regularColumns coordinate 0) +
  finitePair coordinate h (regularColumns coordinate 0) (regularForcing coordinate 0) +
  (star (sourceRate coordinate)+sourceRate coordinate) *
    (((Real.exp (-h/2) : ℂ)/2 - pairedMellinTranslationCharacter coordinate.value h/2) *
      (1 + (mu+1/2-sourceRate coordinate)/star coordinate.value +
        star ((mu+1/2-sourceRate coordinate)/star coordinate.value)) +
     (1/2 : ℂ) * (inner ℂ (regularColumns coordinate 0) (outwardConstantShell h) +
       star (inner ℂ (regularColumns coordinate 0) (outwardConstantShell h))))

theorem sourceGramForcing00_calculated (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceGramForcing coordinate h 0 0 = calculatedForcing00 coordinate h := by
  unfold sourceGramForcing calculatedForcing00
  simp only [jumpColumns,Matrix.cons_val_zero]
  rw [regular0_contact_calculated coordinate h nonnegative]

private theorem original_shift_nonnegative : 0 ≤ Real.log stageZeroSonineQ := by
  apply Real.log_nonneg
  change 1 ≤ Real.sqrt 3
  exact Real.one_le_sqrt.mpr (by norm_num)

private theorem weighted_source_calculated (coordinate : BurnolCompletedMellinCoordinate) :
    (star (sourceRate coordinate)+sourceRate coordinate)⁻¹ *
      (∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients coordinate i)*sourceCoefficients coordinate j*
        sourceGramForcing coordinate (Real.log stageZeroSonineQ) i j) =
    (star (sourceRate coordinate)+sourceRate coordinate)⁻¹ *
      (star (Kernel.A coordinate)*Kernel.A coordinate*calculatedForcing00 coordinate (Real.log stageZeroSonineQ) +
       star (Kernel.A coordinate)*Kernel.beta coordinate*sourceGramForcing coordinate (Real.log stageZeroSonineQ) 0 1 +
       star (Kernel.beta coordinate)*Kernel.A coordinate*sourceGramForcing coordinate (Real.log stageZeroSonineQ) 1 0 +
       star (Kernel.beta coordinate)*Kernel.beta coordinate*sourceGramForcing coordinate (Real.log stageZeroSonineQ) 1 1) := by
  simp only [Fin.sum_univ_two,sourceCoefficients,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [sourceGramForcing00_calculated coordinate _ original_shift_nonnegative]
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (rightHalf : 1/2<observation.coordinate.re)
local notation "c" => originalKCoordinate observation.coordinate
 (And.right (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial)) rightHalf

/-- This actual residual consumes the B-generated contact calculation, leaving every other source entry. -/
theorem installed_residual_calculated_contact :
 (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual =
 (star (sourceRate c)+sourceRate c)⁻¹ *
  (star (Kernel.A c)*Kernel.A c*calculatedForcing00 c (Real.log stageZeroSonineQ) +
   star (Kernel.A c)*Kernel.beta c*sourceGramForcing c (Real.log stageZeroSonineQ) 0 1 +
   star (Kernel.beta c)*Kernel.A c*sourceGramForcing c (Real.log stageZeroSonineQ) 1 0 +
   star (Kernel.beta c)*Kernel.beta c*sourceGramForcing c (Real.log stageZeroSonineQ) 1 1) := by
  rw [installed_fixedResidual_from_source_forcing]
  exact weighted_source_calculated c

theorem installed_calculated_contact_on_original_evolution :
 let root:=runtimeEffectRoot observation nontrivial
 let visit:=runtimeEffectVisit observation nontrivial
 let registered:=runtimeEffectRootedActive observation nontrivial
 let receipt:=installedOriginalKReceiptAt observation nontrivial rightHalf
 let evolution:=root.canonicalCausalAnswerAndNext (ULift.up visit)
 HEq (evolution.generated,
       evolution.generated.projectionOutcome (runtimeEffectRecognition observation nontrivial).rootEffectProjection,
       evolution.nextCurrent,receipt.kernel,receipt.fixedResidual)
     (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit,
       registered.installedFiber,root.generatedNextCurrentAt visit,generatedK c,
       (star (sourceRate c)+sourceRate c)⁻¹ *
        (star (Kernel.A c)*Kernel.A c*calculatedForcing00 c (Real.log stageZeroSonineQ) +
         star (Kernel.A c)*Kernel.beta c*sourceGramForcing c (Real.log stageZeroSonineQ) 0 1 +
         star (Kernel.beta c)*Kernel.A c*sourceGramForcing c (Real.log stageZeroSonineQ) 1 0 +
         star (Kernel.beta c)*Kernel.beta c*sourceGramForcing c (Real.log stageZeroSonineQ) 1 1)) := by
  have actual := installed_source_action_on_original_evolution observation nontrivial rightHalf
  rw [weighted_source_calculated c] at actual
  exact actual

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
