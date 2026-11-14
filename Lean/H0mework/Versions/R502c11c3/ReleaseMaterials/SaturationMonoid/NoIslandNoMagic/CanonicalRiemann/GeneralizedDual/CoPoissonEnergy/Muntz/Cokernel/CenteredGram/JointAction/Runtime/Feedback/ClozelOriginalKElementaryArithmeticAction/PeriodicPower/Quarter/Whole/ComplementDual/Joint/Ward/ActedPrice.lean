import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ActedSchur
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Price
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKFiniteOrderRelease.GenericSourceStepBAction OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Price OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open scoped Topology InnerProductSpace
open private cotest_forward_even from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PairedValue
open private outgoing_even outgoing_step inverse_fourier_power from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ActedSchur
open private position_read first_B_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private correction_smooth_dual dual_smooth_split from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "R" => burnolDirectRightResolventCLM
local notation "F" => fourierL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "X" => burnolAmbientMeanZeroPosition
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "a" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "bNative" => OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source.correction
local notation "leading" => ForcingPrimitive.leadingCoefficient

/-- The same actual outgoing cotest supplies both complete next B feet, including backward contacts. -/
theorem actual_native_acted_B_step (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (j : ℕ) :
    a (nativeOutgoingCotest c (j+1)) = firstNext (barC c) (nativeOutgoingCotest c j) ∧
      d (nativeOutgoingCotest c (j+1)) = secondNext (barC c) (nativeOutgoingCotest c j) := by
  rw [outgoing_step]
  exact actual_sourceStep_B (barC c) _ (outgoing_even c zero j)

theorem actual_native_acted_field (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (j : ℕ) :
    fourierL2.symm (((R c)^j) (nativeCotest c)) = nativeOutgoingCotest c j := by
  rw [nativeCotest, actual_paired_cotest_common_value c zero, inverse_fourier_power]
  have even := cotest_forward_even c zero
  have fourier := congrArg fourierL2.symm (fourierL2_fourierL2 (pairedCotestForward c))
  rw [fourierL2.symm_apply_apply, even] at fourier
  rw [← fourier, fourierL2.symm_apply_apply]
  rfl

/-- The full L1 dual inverse pays the actual acted correction leg through its two genuine B feet. -/
theorem actual_native_acted_correction_price (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (j : ℕ) :
    inner ℂ (((R c)^j) (nativeCotest c)) (F (E (bNative c.value c.belowOne : Hq))) =
      inner ℂ (Y (nativeOutgoingCotest c j))
        (leading c • logBFirst c 0 - burnolRieszSingleFourierSource c) -
      star (∫ x : ℝ, star (seedRaw c.value x) *
        burnolMeanZeroFourierRaw (d (nativeOutgoingCotest c j)) x ∂μq) := by
  let w := nativeOutgoingCotest c j
  let u := smooth (dualRaw c.value c.belowOne) (actual_dual_integrable c.value c.belowOne)
  have original : u = leading c • logBFirst c 0 - burnolRieszSingleFourierSource c :=
    actual_original_dual_fourier_source c
  have uEven : reflectRestricted q (u : Hq) = (u : Hq) := by
    have evenLog : reflectRestricted q (logBFirst c 0 : Hq) = (logBFirst c 0 : Hq) :=
      congrArg (fun state : M => (state : Hq)) (log_B_even c 0)
    rw [original]
    change reflectRestricted q (leading c • (logBFirst c 0 : Hq) - (burnolRieszSingleFourierSource c : Hq)) = _
    rw [map_sub, map_smul, burnolRieszSingleFourierSource_reflection_fixed, evenLog]
    rfl
  have corrEven : reflectRestricted q (bNative c.value c.belowOne : Hq) = (bNative c.value c.belowOne : Hq) :=
    congrArg (fun state : M => (state : Hq)) (actual_correction_reflection c.value c.belowOne)
  have nativeFirst : S u = bNative c.value c.belowOne := correction_smooth_dual c.value c.belowOne
  have nativeSecond : u = firstSource c.value c.belowOne + S (bNative c.value c.belowOne) :=
    dual_smooth_split c.value c.belowOne
  have first : a w + S (d w) = X w := burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs w)
  have second : S (a w) + d w = Y w := burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs w)
  have core : inner ℂ (X w) (bNative c.value c.belowOne) =
      inner ℂ (Y w) u - inner ℂ (d w) (firstSource c.value c.belowOne) := by
    calc
      _ = inner ℂ (a w) (bNative c.value c.belowOne) + inner ℂ (S (d w)) (bNative c.value c.belowOne) := by
        rw [← first, inner_add_left]
      _ = inner ℂ (S (a w)) u + inner ℂ (d w) (S (bNative c.value c.belowOne)) := by
        congr 1
        · rw [← nativeFirst]
          exact (meanZero_fourier_pairing_of_reflection (a w) u uEven).symm
        · exact meanZero_fourier_pairing_of_reflection (d w) (bNative c.value c.belowOne) corrEven
      _ = inner ℂ (Y w - d w) u + inner ℂ (d w) (u - firstSource c.value c.belowOne) := by
        rw [eq_sub_of_add_eq second, eq_sub_of_add_eq' nativeSecond.symm]
      _ = _ := by rw [inner_sub_left, inner_sub_right]; ring
  have dEvenM : sourceMeanZeroReflection (d w) = d w := by
    rw [← (B_fourier w).1]
    exact first_B_even (F w)
  have mixed := actual_mixed_centered_pair (seedRaw c.value) (actual_seed_integrable c.value c.belowOne)
    (actual_seed_mean c.value c.belowOne) (d w) (congrArg (fun state : M => (state : Hq)) dEvenM)
  change inner ℂ (firstSource c.value c.belowOne) (d w) = _ at mixed
  have mixedReverse : inner ℂ (d w) (firstSource c.value c.belowOne) =
      star (∫ x : ℝ, star (seedRaw c.value x) * burnolMeanZeroFourierRaw (d w) x ∂μq) := by
    rw [← mixed]
    exact (inner_conj_symm _ _).symm
  rw [original, mixedReverse] at core
  have moved := fourierL2.inner_map_map (fourierL2.symm (((R c)^j) (nativeCotest c)))
    (E (bNative c.value c.belowOne : Hq))
  rw [fourierL2.apply_symm_apply, actual_native_acted_field c zero j] at moved
  have extended := ContinuousLinearMap.adjoint_inner_right Rq w (bNative c.value c.belowOne : Hq)
  change inner ℂ w (E (bNative c.value c.belowOne : Hq)) =
    inner ℂ (Rq w) (bNative c.value c.belowOne : Hq) at extended
  have centered : inner ℂ (Rq w) (bNative c.value c.belowOne : Hq) = inner ℂ (X w) (bNative c.value c.belowOne) := by
    rw [position_read w (outgoing_even c zero j)]
    exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (bNative c.value c.belowOne) (Rq w)).symm
  exact moved.trans (extended.trans (centered.trans core))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
