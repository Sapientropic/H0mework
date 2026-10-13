import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalPaAction.Consumer
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.Correction

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open scoped InnerProductSpace Topology
namespace Pa
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalPaAction
  (E Q invisible invisible_mem actualPa actualPa_mem actual_native_p_Pa_split actual_complete_reconstruction)
end Pa
namespace P
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction (R)
end P
namespace D
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFirstFullSourceDynamics
  (factory initial firstCfg packet input raw raw_successor next_pair original_runtime_whole original_root_future)
end D
namespace Paid
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalRAction (original_R_direct)
end Paid
local instance complete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

-- This difference keeps both orientations. In particular radius > 4 has a negative source band.
def signedUnitSource (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ)
    (positive : 0 < radius) : BurnolL2 :=
  burnolRadiusNormalizedUnitTail coordinate radius positive - burnolNormalizedFirstSourceUnitTail coordinate

def signedUnitResponse (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  burnolUnitTailResponse coordinate radius - burnolUnitTailResponse coordinate 4

theorem signed_unit_source_raw (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ)
    (positive : 0 < radius) :
    (signedUnitSource coordinate radius positive : ℝ → ℂ) =ᵐ[volume]
      fun x => (if radius < |x| then -( ((|x| : ℝ) : ℂ) ^ (-coordinate.value)) else 0) -
        (if (4 : ℝ) < |x| then -( ((|x| : ℝ) : ℂ) ^ (-coordinate.value)) else 0) := by
  filter_upwards [Lp.coeFn_sub (burnolRadiusNormalizedUnitTail coordinate radius positive)
    (burnolNormalizedFirstSourceUnitTail coordinate), burnolRadiusUnitTail_coeFn coordinate radius positive,
    burnolNormalizedFirstSourceUnitTail_coeFn coordinate] with x subRead low high
  rw [signedUnitSource, subRead, Pi.sub_apply, low, high]
  rfl

theorem signed_unit_realizes (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ)
    (positive : 0 < radius) (bounded : radius⁻¹ ≤ 4) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (signedUnitSource coordinate radius positive) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (signedUnitResponse coordinate radius)) test := by
  rw [signedUnitSource, signedUnitResponse, ← burnolRemainderSourceReadCLM_apply, map_sub,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    burnolUnitTailResponse_realizes coordinate radius positive bounded, burnolOriginalUnitTail_realizes,
    map_sub, sub_apply]

def unitAction (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation shift (burnolUnitTailResponse coordinate 4) -
    fullMellinTranslationCharacter coordinate.value shift • burnolUnitTailResponse coordinate 4

theorem unit_action_signed_shell (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (bounded : (4 * Real.exp (-shift))⁻¹ ≤ 4) :
    unitAction coordinate shift = fullMellinTranslationCharacter coordinate.value shift •
      signedUnitResponse coordinate (4 * Real.exp (-shift)) := by
  rw [unitAction, burnolUnitTailResponse_radius_dilation coordinate 4 (by norm_num) (by norm_num) shift bounded,
    signedUnitResponse, smul_sub]

def projectPa : BurnolL2 →L[ℂ] burnolCompactCoPoissonClosedRange.toSubmodule :=
  burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto.comp burnolEvenAmbientProjection

def correction (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.comp
    ((burnolPaSourceCorrection coordinate).comp projectPa)

def coefficient (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  (burnolPaResolventSourceCoefficient coordinate).comp Pa.E

theorem projection_read (value : BurnolL2) : (projectPa value : BurnolPaAmbientCarrier) = Pa.E value := rfl

theorem correction_read (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    correction coordinate value = burnolDirectRightResolvent (coordinate.value / 2) (Pa.E value : BurnolL2) -
      coefficient coordinate value • burnolUnitTailResponse coordinate 4 := rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

def coordinate : BurnolCompletedMellinCoordinate :=
  originalKCoordinate observation.coordinate
    (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial).2 half.down

theorem coordinate_value : (coordinate observation nontrivial half).value = observation.coordinate := rfl

def translatedCorrection (shift : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (burnolMultiplicativeDilation shift).toLinearIsometry.toContinuousLinearMap.comp
    (correction (coordinate observation nontrivial half))

def translatedUnit (shift : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (coefficient (coordinate observation nontrivial half)).smulRight
    (fullMellinTranslationCharacter observation.coordinate shift • burnolUnitTailResponse
      (coordinate observation nontrivial half) 4)

def translatedTail (shift : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (coefficient (coordinate observation nontrivial half)).smulRight
    (burnolMultiplicativeDilation shift (burnolUnitTailResponse (coordinate observation nontrivial half) 4))

def translatedShell (shift : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (coefficient (coordinate observation nontrivial half)).smulRight
    (unitAction (coordinate observation nontrivial half) shift)

def translatedInvisible (shift : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (burnolMultiplicativeDilation shift).toLinearIsometry.toContinuousLinearMap.comp
    ((P.R observation nontrivial half).comp
      (ContinuousLinearMap.id ℂ BurnolL2 -
        (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.comp Pa.E))

def fourTerms (shift : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  translatedCorrection observation nontrivial half shift + translatedUnit observation nontrivial half shift +
    translatedShell observation nontrivial half shift + translatedInvisible observation nontrivial half shift

theorem four_terms_eq_action (shift : ℝ) (value : BurnolL2) :
    fourTerms observation nontrivial half shift value =
      burnolMultiplicativeDilation shift (P.R observation nontrivial half value) := by
  change burnolMultiplicativeDilation shift (correction (coordinate observation nontrivial half) value) +
    coefficient (coordinate observation nontrivial half) value •
      (fullMellinTranslationCharacter observation.coordinate shift • burnolUnitTailResponse (coordinate observation nontrivial half) 4) +
    coefficient (coordinate observation nontrivial half) value • unitAction (coordinate observation nontrivial half) shift +
    burnolMultiplicativeDilation shift (P.R observation nontrivial half (value - (Pa.E value : BurnolL2))) = _
  rw [correction_read, unitAction, coordinate_value, ← Paid.original_R_direct observation nontrivial half,
    map_sub, map_smul, map_sub, map_sub]
  module

def sourceShift : ℝ := Real.log (Real.sqrt 3)

theorem source_shift_exp : Real.exp sourceShift = Real.sqrt 3 := by
  exact Real.exp_log (Real.sqrt_pos.2 (by norm_num))

theorem negative_source_radius : 4 < 4 * Real.exp (-(-sourceShift)) := by
  rw [neg_neg, source_shift_exp]
  have : (1 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  linarith

theorem positive_source_radius_bound : (4 * Real.exp (-sourceShift))⁻¹ ≤ 4 := by
  rw [Real.exp_neg, source_shift_exp, mul_inv_rev, inv_inv]
  have : Real.sqrt 3 ≤ (16 : ℝ) := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  norm_num at *
  linarith

theorem negative_source_radius_bound : (4 * Real.exp (-(-sourceShift)))⁻¹ ≤ 4 := by
  have positive : 0 < 4 * Real.exp (-(-sourceShift)) := by positivity
  have high : 4 ≤ 4 * Real.exp (-(-sourceShift)) := (negative_source_radius).le
  calc
    _ ≤ (4 : ℝ)⁻¹ := (inv_le_inv₀ positive (by norm_num)).2 high
    _ ≤ 4 := by norm_num

def pairTotal : (BurnolL2 × BurnolL2) →L[ℂ] BurnolL2 :=
  ContinuousLinearMap.fst ℂ _ _ + ContinuousLinearMap.snd ℂ _ _

def bothCorrection : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  ((translatedCorrection observation nontrivial half sourceShift).comp pairTotal).prod
    ((translatedCorrection observation nontrivial half (-sourceShift)).comp pairTotal)
def bothUnit : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  ((translatedUnit observation nontrivial half sourceShift).comp pairTotal).prod
    ((translatedUnit observation nontrivial half (-sourceShift)).comp pairTotal)
def bothTail : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  ((translatedTail observation nontrivial half sourceShift).comp pairTotal).prod
    ((translatedTail observation nontrivial half (-sourceShift)).comp pairTotal)

def bothShell : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  ((translatedShell observation nontrivial half sourceShift).comp pairTotal).prod
    ((translatedShell observation nontrivial half (-sourceShift)).comp pairTotal)
def bothInvisible : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  ((translatedInvisible observation nontrivial half sourceShift).comp pairTotal).prod
    ((translatedInvisible observation nontrivial half (-sourceShift)).comp pairTotal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
