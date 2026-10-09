import H0mework.Arithmetic.SonineProjection.MeanZeroBlock
import H0mework.Versions.V2.Arithmetic.MellinProjection.AmbientMellinProjection

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

theorem reflectRestricted_quarter_involutive
    (state : BurnolQuarterIntervalL2) :
    reflectRestricted (1 / 4 : ℝ)
        (reflectRestricted (1 / 4 : ℝ) state) = state := by
  apply Lp.ext
  let reflection := negMeasurePreserving_restrict (1 / 4 : ℝ)
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (reflectRestricted (1 / 4 : ℝ) state) reflection,
    reflection.quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving state reflection)]
      with x first second
  simpa [reflectRestricted] using first.trans second

theorem reflectRestricted_quarter_preserves_constantLine
    {state : BurnolQuarterIntervalL2}
    (membership : state ∈ intervalConstantLine (1 / 4 : ℝ)) :
    reflectRestricted (1 / 4 : ℝ) state ∈
      intervalConstantLine (1 / 4 : ℝ) := by
  obtain ⟨coefficient, rfl⟩ := Submodule.mem_span_singleton.mp membership
  rw [map_smul, reflectRestricted_intervalConstant]
  exact Submodule.smul_mem _ coefficient
    (Submodule.mem_span_singleton_self _)

theorem reflectRestricted_quarter_preserves_meanZero
    {state : BurnolQuarterIntervalL2}
    (membership : state ∈ burnolQuarterMeanZeroClosedFace) :
    reflectRestricted (1 / 4 : ℝ) state ∈
      burnolQuarterMeanZeroClosedFace := by
  intro constant constantMem
  have reflectedConstantMem :=
    reflectRestricted_quarter_preserves_constantLine constantMem
  have stateOrthogonal := membership
    (reflectRestricted (1 / 4 : ℝ) constant) reflectedConstantMem
  calc
    inner ℂ constant (reflectRestricted (1 / 4 : ℝ) state) =
        inner ℂ
          (reflectRestricted (1 / 4 : ℝ)
            (reflectRestricted (1 / 4 : ℝ) constant))
          (reflectRestricted (1 / 4 : ℝ) state) := by
      rw [reflectRestricted_quarter_involutive]
    _ = inner ℂ (reflectRestricted (1 / 4 : ℝ) constant) state :=
      (reflectRestricted (1 / 4 : ℝ)).inner_map_map _ _
    _ = 0 := stateOrthogonal

theorem burnolQuarterMeanZeroProjection_reflect
    (state : BurnolQuarterIntervalL2) :
    burnolQuarterMeanZeroProjection
        (reflectRestricted (1 / 4 : ℝ) state) =
      reflectRestricted (1 / 4 : ℝ)
        (burnolQuarterMeanZeroProjection state) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact reflectRestricted_quarter_preserves_meanZero
      (burnolQuarterMeanZeroProjection_mem state)
  · intro test testMem
    have reflectedTestMem :=
      reflectRestricted_quarter_preserves_meanZero testMem
    calc
      inner ℂ
          (reflectRestricted (1 / 4 : ℝ) state -
            reflectRestricted (1 / 4 : ℝ)
              (burnolQuarterMeanZeroProjection state)) test =
        inner ℂ
          (reflectRestricted (1 / 4 : ℝ)
            (state - burnolQuarterMeanZeroProjection state)) test := by
              rw [map_sub]
      _ = inner ℂ
          (reflectRestricted (1 / 4 : ℝ)
            (state - burnolQuarterMeanZeroProjection state))
          (reflectRestricted (1 / 4 : ℝ)
            (reflectRestricted (1 / 4 : ℝ) test)) := by
              rw [reflectRestricted_quarter_involutive]
      _ = inner ℂ (state - burnolQuarterMeanZeroProjection state)
          (reflectRestricted (1 / 4 : ℝ) test) :=
        (reflectRestricted (1 / 4 : ℝ)).inner_map_map _ _
      _ = 0 := Submodule.starProjection_inner_eq_zero
        state _ reflectedTestMem

def burnolAmbientEvenPart (value : BurnolL2) : BurnolL2 :=
  (1 / 2 : ℂ) • (value + reflectL2 value)

theorem burnolAmbientEvenPart_even (value : BurnolL2) :
    reflectL2 (burnolAmbientEvenPart value) = burnolAmbientEvenPart value := by
  unfold burnolAmbientEvenPart
  rw [map_smul, map_add, reflectL2_reflectL2]
  congr 1
  exact add_comm _ _

theorem fourierL2_burnolAmbientEvenPart_even (value : BurnolL2) :
    reflectL2 (fourierL2 (burnolAmbientEvenPart value)) =
      fourierL2 (burnolAmbientEvenPart value) := by
  rw [← fourierL2_reflectL2_commute,
    burnolAmbientEvenPart_even]

def burnolAmbientMeanZeroPosition
    (value : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto
    (burnolQuarterRestriction (burnolAmbientEvenPart value))

def burnolAmbientMeanZeroFourier
    (value : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto
    (burnolQuarterRestriction (fourierL2 (burnolAmbientEvenPart value)))

theorem burnolAmbientMeanZeroPosition_reflection_fixed
    (value : BurnolL2) :
    reflectRestricted (1 / 4 : ℝ)
        (burnolAmbientMeanZeroPosition value : BurnolQuarterIntervalL2) =
      burnolAmbientMeanZeroPosition value := by
  change reflectRestricted (1 / 4 : ℝ)
      (burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction (burnolAmbientEvenPart value))) = _
  rw [← burnolQuarterMeanZeroProjection_reflect]
  have restrictionFixed :
      reflectRestricted (1 / 4 : ℝ)
          (burnolQuarterRestriction (burnolAmbientEvenPart value)) =
        burnolQuarterRestriction (burnolAmbientEvenPart value) := by
    calc
      _ = burnolQuarterRestriction
          (reflectL2 (burnolAmbientEvenPart value)) := by
        exact (restrictToInterval_reflectL2 (1 / 4 : ℝ)
          (burnolAmbientEvenPart value)).symm
      _ = _ := congrArg burnolQuarterRestriction
        (burnolAmbientEvenPart_even value)
  rw [restrictionFixed]
  unfold burnolAmbientMeanZeroPosition burnolQuarterMeanZeroProjection
  rfl

theorem burnolAmbientMeanZeroFourier_reflection_fixed
    (value : BurnolL2) :
    reflectRestricted (1 / 4 : ℝ)
        (burnolAmbientMeanZeroFourier value : BurnolQuarterIntervalL2) =
      burnolAmbientMeanZeroFourier value := by
  change reflectRestricted (1 / 4 : ℝ)
      (burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction
          (fourierL2 (burnolAmbientEvenPart value)))) = _
  rw [← burnolQuarterMeanZeroProjection_reflect]
  have restrictionFixed :
      reflectRestricted (1 / 4 : ℝ)
          (burnolQuarterRestriction
            (fourierL2 (burnolAmbientEvenPart value))) =
        burnolQuarterRestriction
          (fourierL2 (burnolAmbientEvenPart value)) := by
    calc
      _ = burnolQuarterRestriction
          (reflectL2 (fourierL2 (burnolAmbientEvenPart value))) := by
        exact (restrictToInterval_reflectL2 (1 / 4 : ℝ)
          (fourierL2 (burnolAmbientEvenPart value))).symm
      _ = _ := congrArg burnolQuarterRestriction
        (fourierL2_burnolAmbientEvenPart_even value)
  rw [restrictionFixed]
  unfold burnolAmbientMeanZeroFourier burnolQuarterMeanZeroProjection
  rfl

def burnolAmbientMeanZeroBlockRhs
    (value : BurnolL2) : BurnolQuarterMeanZeroCarrier ×
      BurnolQuarterMeanZeroCarrier :=
  (burnolAmbientMeanZeroPosition value,
    burnolAmbientMeanZeroFourier value)

def burnolAmbientMeanZeroFirstCorrection
    (value : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  burnolMeanZeroBlockFirst (burnolAmbientMeanZeroBlockRhs value)

def burnolAmbientMeanZeroSecondCorrection
    (value : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  burnolMeanZeroBlockSecond (burnolAmbientMeanZeroBlockRhs value)

def burnolAmbientRawMeanZeroCorrection (value : BurnolL2) : BurnolL2 :=
  burnolQuarterZeroExtension
      (burnolAmbientMeanZeroFirstCorrection value : BurnolQuarterIntervalL2) +
    fourierL2 (burnolQuarterZeroExtension
      (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2))

def burnolAmbientEvenMeanZeroCorrection (value : BurnolL2) : BurnolL2 :=
  burnolAmbientEvenPart (burnolAmbientRawMeanZeroCorrection value)

def burnolAmbientExtendedSonineProjectionFormula
    (value : BurnolL2) : BurnolL2 :=
  burnolAmbientEvenPart value - burnolAmbientEvenMeanZeroCorrection value

theorem burnolQuarterMeanZeroProjection_coe
    (state : BurnolQuarterMeanZeroCarrier) :
    burnolQuarterMeanZeroProjection (state : BurnolQuarterIntervalL2) =
      (state : BurnolQuarterIntervalL2) := by
  exact Submodule.starProjection_eq_self_iff.mpr state.property

theorem burnolMeanZeroTruncatedFourier_coe
    (state : BurnolQuarterMeanZeroCarrier) :
    (burnolMeanZeroTruncatedFourier state : BurnolQuarterIntervalL2) =
      burnolQuarterMeanZeroProjection
        (burnolTruncatedFourier (state : BurnolQuarterIntervalL2)) := by
  rw [burnolMeanZeroTruncatedFourier_ambient_read,
    burnolQuarterMeanZeroProjection_coe]

theorem burnolAmbientRawMeanZeroCorrection_position
    (value : BurnolL2) :
    burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction
          (burnolAmbientRawMeanZeroCorrection value)) =
      (burnolAmbientMeanZeroFirstCorrection value :
          BurnolQuarterIntervalL2) +
        burnolMeanZeroTruncatedFourier
          (burnolAmbientMeanZeroSecondCorrection value) := by
  unfold burnolAmbientRawMeanZeroCorrection
  rw [map_add, burnolQuarterRestriction_zeroExtension, map_add,
    burnolQuarterMeanZeroProjection_coe]
  change _ + burnolQuarterMeanZeroProjection
      (burnolTruncatedFourier
        (burnolAmbientMeanZeroSecondCorrection value :
          BurnolQuarterIntervalL2)) = _
  rw [← burnolMeanZeroTruncatedFourier_coe]

theorem burnolAmbientRawMeanZeroCorrection_fourier
    (value : BurnolL2) :
    burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction
          (fourierL2 (burnolAmbientRawMeanZeroCorrection value))) =
      (burnolMeanZeroTruncatedFourier
          (burnolAmbientMeanZeroFirstCorrection value) :
            BurnolQuarterIntervalL2) +
        reflectRestricted (1 / 4 : ℝ)
          (burnolAmbientMeanZeroSecondCorrection value :
            BurnolQuarterIntervalL2) := by
  unfold burnolAmbientRawMeanZeroCorrection
  rw [map_add, fourierL2_fourierL2, map_add]
  have reflectedRestriction :
      burnolQuarterRestriction
          (reflectL2 (burnolQuarterZeroExtension
            (burnolAmbientMeanZeroSecondCorrection value :
              BurnolQuarterIntervalL2))) =
        reflectRestricted (1 / 4 : ℝ)
          (burnolAmbientMeanZeroSecondCorrection value :
            BurnolQuarterIntervalL2) := by
    calc
      _ = reflectRestricted (1 / 4 : ℝ)
          (burnolQuarterRestriction
            (burnolQuarterZeroExtension
              (burnolAmbientMeanZeroSecondCorrection value :
                BurnolQuarterIntervalL2))) :=
        restrictToInterval_reflectL2 (1 / 4 : ℝ) _
      _ = _ := by rw [burnolQuarterRestriction_zeroExtension]
  rw [reflectedRestriction]
  change burnolQuarterMeanZeroProjection
      (burnolTruncatedFourier
          (burnolAmbientMeanZeroFirstCorrection value :
            BurnolQuarterIntervalL2) +
        reflectRestricted (1 / 4 : ℝ)
          (burnolAmbientMeanZeroSecondCorrection value :
            BurnolQuarterIntervalL2)) = _
  rw [map_add, ← burnolMeanZeroTruncatedFourier_coe]
  have reflectedMem := reflectRestricted_quarter_preserves_meanZero
    (burnolAmbientMeanZeroSecondCorrection value).property
  have reflectedFixed :
      burnolQuarterMeanZeroProjection
          (reflectRestricted (1 / 4 : ℝ)
            (burnolAmbientMeanZeroSecondCorrection value :
              BurnolQuarterIntervalL2)) =
        reflectRestricted (1 / 4 : ℝ)
          (burnolAmbientMeanZeroSecondCorrection value :
            BurnolQuarterIntervalL2) := by
    exact Submodule.starProjection_eq_self_iff.mpr reflectedMem
  rw [reflectedFixed]

theorem burnolAmbientEvenPart_restriction_meanZero
    (value : BurnolL2) :
    burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction (burnolAmbientEvenPart value)) =
      (1 / 2 : ℂ) •
        (burnolQuarterMeanZeroProjection
            (burnolQuarterRestriction value) +
          reflectRestricted (1 / 4 : ℝ)
            (burnolQuarterMeanZeroProjection
              (burnolQuarterRestriction value))) := by
  unfold burnolAmbientEvenPart
  rw [map_smul, map_add, map_smul, map_add]
  have reflectedRestriction :
      burnolQuarterRestriction (reflectL2 value) =
        reflectRestricted (1 / 4 : ℝ)
          (burnolQuarterRestriction value) :=
    restrictToInterval_reflectL2 (1 / 4 : ℝ) value
  rw [reflectedRestriction, burnolQuarterMeanZeroProjection_reflect]

theorem fourierL2_burnolAmbientEvenPart (value : BurnolL2) :
    fourierL2 (burnolAmbientEvenPart value) =
      burnolAmbientEvenPart (fourierL2 value) := by
  unfold burnolAmbientEvenPart
  rw [map_smul, map_add, fourierL2_reflectL2_commute]

theorem burnolAmbientEvenPart_fourierRestriction_meanZero
    (value : BurnolL2) :
    burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction
          (fourierL2 (burnolAmbientEvenPart value))) =
      (1 / 2 : ℂ) •
        (burnolQuarterMeanZeroProjection
            (burnolQuarterRestriction (fourierL2 value)) +
          reflectRestricted (1 / 4 : ℝ)
            (burnolQuarterMeanZeroProjection
              (burnolQuarterRestriction (fourierL2 value)))) := by
  rw [fourierL2_burnolAmbientEvenPart]
  exact burnolAmbientEvenPart_restriction_meanZero (fourierL2 value)

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
