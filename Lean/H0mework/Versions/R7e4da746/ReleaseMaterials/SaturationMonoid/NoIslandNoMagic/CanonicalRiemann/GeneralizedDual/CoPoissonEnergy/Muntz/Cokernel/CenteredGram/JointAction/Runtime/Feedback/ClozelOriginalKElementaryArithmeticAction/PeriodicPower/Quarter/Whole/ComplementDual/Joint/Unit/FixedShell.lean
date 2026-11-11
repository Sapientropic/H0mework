import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.OppositeForcing
import H0mework.Versions.R7e4da746.Arithmetic.RiemannNativeCurrent.UnitResponseRadius

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FixedShell
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalKFiniteOrderRelease OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.ConjugateLow OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.OppositeForcing
open scoped InnerProductSpace Topology
local notation "q" => burnolUnscaledCommonGapRadius
local notation "D" => burnolMultiplicativeDilation
local notation "R" => burnolDirectRightResolventCLM
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem power_dilation (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ)
    (h : ℝ) (value : BurnolL2) :
    ((R coordinate)^j) (D h value) = D h (((R coordinate)^j) value) := by
  induction j with
  | zero => rfl
  | succ j previous =>
    simp only [pow_succ',mul_apply_eq_comp,previous]
    exact burnolDirectRightResolvent_dilation (coordinate.value/2) h _

private theorem ambient_read (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (physical : value ∈ evenBurnolClosedFace q) :
    burnolAmbientCompletedMellinEvaluator coordinate value = inner ℂ (K coordinate : BurnolL2) value := by
  let state : BurnolPaAmbientCarrier := ⟨value,physical⟩
  have source := congrArg (fun functional : BurnolPaAmbientCarrier →L[ℂ] ℂ => functional state)
    (burnolAmbientCompletedMellinEvaluator_restrict coordinate)
  exact source.trans (burnolCompletedMellinRieszVector_readback coordinate state).symm

/-- The original radius-one source is acted before any reader or physical cut. -/
def unitOnePower (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) : BurnolL2 :=
  ((R coordinate)^j) (burnolUnitTailResponse coordinate 1)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

/-- The same actual Pa field stays in the physical range through the original order, at the independent conjugate K reader. -/
theorem actual_conjugate_K_Pa_power_zero (state : BurnolPaAmbientCarrier)
    (inside : state ∈ burnolCompactCoPoissonClosedRange) (j : ℕ) (atMost : j ≤ m) :
    inner ℂ (K (barC c) : BurnolL2) (CombSource.Division.rawIterate observation half.down j (state : BurnolL2)) = 0 := by
  have actionRight : 1/4 < ((c).value/2).re := by
    rw [Complex.div_re]; norm_num; linarith [(c).rightHalf]
  have readRight : 1/4 < ((barC c).value/2).re := by
    rw [Complex.div_re]; norm_num; linarith [(barC c).rightHalf]
  have readBelow : ((barC c).value/2).re < 1/2 := by
    rw [Complex.div_re]; norm_num; linarith [(barC c).belowOne]
  have readCoordinate : burnolDivisionCompletedMellinCoordinate ((barC c).value/2) readRight readBelow = barC c := by
    have coordinate_eq {left right : BurnolCompletedMellinCoordinate} (same : left.value = right.value) : left = right := by
      cases left
      cases right
      cases same
      rfl
    apply coordinate_eq
    change 2*((barC c).value/2) = (barC c).value
    ring
  induction j with
  | zero =>
    have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal (barC c)
      observation.conjugate_mathlibZero
    exact inner_eq_zero_symm.mp (orthogonal state inside)
  | succ j previous =>
    have previous := previous (by omega)
    have input := CombSource.Division.whole_pa_physical observation nontrivial half.down j (by omega) state inside
    have output := CombSource.Division.whole_pa_physical observation nontrivial half.down (j+1) atMost state inside
    have source := CombSource.Pricing.ambient_R_scalar_action ((c).value/2) actionRight
      (CombSource.Division.rawIterate observation half.down j (state : BurnolL2)) input.1.1
      ((barC c).value/2) readRight readBelow
    rw [readCoordinate,ambient_read _ _ input,previous,mul_zero] at source
    have step : CombSource.Division.rawIterate observation half.down (j+1) (state : BurnolL2) =
        burnolDirectRightResolvent ((c).value/2)
          (CombSource.Division.rawIterate observation half.down j (state : BurnolL2)) := by
      simp only [CombSource.Division.rawIterate,pow_succ',mul_apply_eq_comp,CombSource.Division.rawAction]
      rfl
    rw [←step] at source
    rw [ambient_read _ _ output] at source
    exact source

omit nontrivial in
/-- Both radius-one shifts are generated as their own actual Pa shell, with the complete normalization. -/
theorem actual_unit_one_shell_field (h : ℝ)
    (above : (1/4 : ℝ) < Real.exp (-h)) (below : Real.exp (-h) < 4) :
    D h (unitOnePower c m) =
      fullMellinTranslationCharacter (c).value h • unitPower observation half m +
        fullMellinTranslationCharacter (c).value h •
          CombSource.Division.rawIterate observation half.down m
            (burnolActualUnitPowerShellPaState c (Real.exp (-h)) above below : BurnolL2) := by
  have bound : (1*Real.exp (-h))⁻¹ ≤ (4 : ℝ) := by
    rw [one_mul,inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    exact above.le
  have moved := burnolUnitTailResponse_radius_dilation c 1 (by norm_num) (by norm_num) h bound
  rw [one_mul] at moved
  have shell := burnolUnitTailResponse_shell c (Real.exp (-h)) above below
  have split : burnolUnitTailResponse c (Real.exp (-h)) = burnolUnitTailResponse c 4 +
      (burnolActualUnitPowerShellPaState c (Real.exp (-h)) above below : BurnolL2) := by
    change burnolUnitTailResponse c (Real.exp (-h)) = burnolUnitTailResponse c 4 +
      burnolUnitPowerShellWave c (Real.exp (-h))
    rw [←shell]
    abel
  unfold unitOnePower
  rw [←power_dilation,moved,split,map_smul,map_add,smul_add]
  rfl

/-- The acted original m-field consumes a newly generated shell rather than an assumed shifted Pa state. -/
theorem actual_unit_one_conjugate_top_transport (h : ℝ)
    (above : (1/4 : ℝ) < Real.exp (-h)) (below : Real.exp (-h) < 4) :
    inner ℂ (K (barC c) : BurnolL2) (D h (unitOnePower c m)) =
      fullMellinTranslationCharacter (c).value h *
        inner ℂ (K (barC c) : BurnolL2) (unitPower observation half m) ∧
    inner ℂ (fourierL2 (K (barC c) : BurnolL2)) (D h (unitOnePower c m)) =
      fullMellinTranslationCharacter (c).value h *
        ((-2*star (oppositeBMatrix c)/((barC c).value-(c).value))*e) := by
  have member := burnolActualUnitPowerShellPaState_mem c (Real.exp (-h)) above below
  have first := actual_conjugate_K_Pa_power_zero observation nontrivial half _ member m le_rfl
  have second := actual_conjugate_FK_Pa_power_low observation nontrivial half _ member m le_rfl
  rw [actual_unit_one_shell_field observation half h above below]
  simp only [inner_add_right,inner_smul_right,first,second,mul_zero,add_zero]
  exact ⟨trivial,congrArg (fun fee : ℂ => fullMellinTranslationCharacter (c).value h*fee)
    (actual_conjugate_fourier_original_top observation nontrivial half)⟩

omit nontrivial in
private theorem fixed_radius_bounds :
    (1/4 : ℝ) < Real.exp (-Real.log stageZeroSonineQ) ∧ Real.exp (-Real.log stageZeroSonineQ) < 4 ∧
    (1/4 : ℝ) < Real.exp (-(-Real.log stageZeroSonineQ)) ∧ Real.exp (-(-Real.log stageZeroSonineQ)) < 4 := by
  have rootSquare : stageZeroSonineQ^2 = 3 := by
    change Real.sqrt 3^2 = 3
    exact Real.sq_sqrt (by norm_num)
  have rootLower : 1 < stageZeroSonineQ := by nlinarith [stageZeroSonineQ_pos]
  have rootUpper : stageZeroSonineQ < 2 := by nlinarith [stageZeroSonineQ_pos]
  rw [neg_neg,Real.exp_neg,Real.exp_log stageZeroSonineQ_pos]
  constructor
  · rw [lt_inv_comm₀ (by norm_num) stageZeroSonineQ_pos]
    norm_num
    linarith
  constructor
  · rw [inv_lt_comm₀ stageZeroSonineQ_pos (by norm_num)]
    linarith
  constructor <;> linarith

/-- The fixed plus and minus h0 mouths retain the same original order and complete top on each side. -/
theorem actual_fixed_two_unit_top_transport :
    (inner ℂ (K (barC c) : BurnolL2) (D (Real.log stageZeroSonineQ) (unitOnePower c m)) =
      fullMellinTranslationCharacter (c).value (Real.log stageZeroSonineQ)*
        inner ℂ (K (barC c) : BurnolL2) (unitPower observation half m) ∧
     inner ℂ (fourierL2 (K (barC c) : BurnolL2)) (D (Real.log stageZeroSonineQ) (unitOnePower c m)) =
      fullMellinTranslationCharacter (c).value (Real.log stageZeroSonineQ)*
        ((-2*star (oppositeBMatrix c)/((barC c).value-(c).value))*e)) ∧
    (inner ℂ (K (barC c) : BurnolL2) (D (-Real.log stageZeroSonineQ) (unitOnePower c m)) =
      fullMellinTranslationCharacter (c).value (-Real.log stageZeroSonineQ)*
        inner ℂ (K (barC c) : BurnolL2) (unitPower observation half m) ∧
     inner ℂ (fourierL2 (K (barC c) : BurnolL2)) (D (-Real.log stageZeroSonineQ) (unitOnePower c m)) =
      fullMellinTranslationCharacter (c).value (-Real.log stageZeroSonineQ)*
        ((-2*star (oppositeBMatrix c)/((barC c).value-(c).value))*e)) :=
  ⟨actual_unit_one_conjugate_top_transport observation nontrivial half _ fixed_radius_bounds.1 fixed_radius_bounds.2.1,
   actual_unit_one_conjugate_top_transport observation nontrivial half _ fixed_radius_bounds.2.2.1 fixed_radius_bounds.2.2.2⟩

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FixedShell
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
