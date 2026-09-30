import H0mework.Versions.Y.Arithmetic.MobiusSource.FirstCell
import H0mework.Versions.Y.Arithmetic.MobiusSource.Tate
import H0mework.Versions.Y.Arithmetic.RiemannSourceGreen.ProbeCutoffValue

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSynthesis

open Complex MeasureTheory Set
open scoped InnerProductSpace
open OriginalPaPhysicalGreen
noncomputable section

theorem halfColumn_wholeAmbient_transpose (column : BurnolL2)
    (supported : originalPhysicalCutoff (1 / 2 : ℝ) column = column)
    (value : BurnolPaAmbientCarrier) :
    inner ℂ column (value : BurnolL2) =
      inner ℂ (burnolAnnulusSamplingL2 column 0) (burnolMobiusSourceL2 value) +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value *
          star (∫ x : ℝ, column x) := by
  have regular : Integrable (column : ℝ → ℂ) := by
    simpa only [supported] using originalPhysicalCutoff_integrable (1 / 2 : ℝ) column
  have cutoffRead := originalPhysicalCutoff_coeFn (1 / 2 : ℝ) column
  rw [supported] at cutoffRead
  have firstCell : ∀ᵐ x : ℝ ∂volume, x ∈ symmetricInterval (1 / 2 : ℝ) →
      burnolMobiusSourceL2 value x = (value : BurnolL2) x -
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value :=
    (ae_restrict_iff' (measurableSet_symmetricInterval (1 / 2 : ℝ))).mp
      (burnolMobiusSource_firstCell value)
  have gap := (ae_restrict_iff'
    (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)).mp (burnolAmbientGap_ae value)
  have pointwise : (fun x : ℝ => inner ℂ (column x) ((value : BurnolL2) x)) =ᵐ[volume]
      (fun x : ℝ => inner ℂ (burnolAnnulusSamplingL2 column 0 x) (burnolMobiusSourceL2 value x) +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value * star (column x)) := by
    filter_upwards [cutoffRead, burnolAnnulusSamplingL2_coeFn column 0, firstCell, gap]
      with x columnAt sampled sourceAt gapAt
    simp only [burnolAnnulusSamplingRaw, Nat.cast_zero, zero_add, one_mul] at sampled
    by_cases inside : x ∈ symmetricInterval (1 / 2 : ℝ)
    · by_cases annulus : x ∈ burnolSamplingAnnulus
      · rw [Set.indicator_of_mem annulus] at sampled
        rw [sampled, sourceAt inside]
        simp only [RCLike.inner_apply, starRingEnd_apply]
        ring
      · have halfBound : |x| ≤ (1 / 2 : ℝ) := abs_le.mpr inside
        have quarterBound : |x| ≤ (1 / 4 : ℝ) := by
          by_contra! greater
          exact annulus ⟨greater, halfBound.trans (by norm_num)⟩
        have inGap : x ∈ symmetricInterval burnolUnscaledCommonGapRadius := by
          simpa only [symmetricInterval, burnolUnscaledCommonGapRadius, mem_Icc] using abs_le.mp quarterBound
        rw [Set.indicator_of_notMem annulus] at sampled
        rw [sampled, gapAt inGap]
        simp only [RCLike.inner_apply, starRingEnd_apply, star_zero, mul_zero, zero_add]
    · rw [Set.indicator_of_notMem inside] at columnAt
      have sampleZero : burnolAnnulusSamplingL2 column 0 x = 0 := by
        rw [sampled]
        by_cases annulus : x ∈ burnolSamplingAnnulus
        · rw [Set.indicator_of_mem annulus, columnAt]
        · exact Set.indicator_of_notMem annulus _
      rw [columnAt, sampleZero]
      simp
  have conjugateRegular : Integrable (fun x : ℝ => star (column x)) :=
    (@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp regular
  have meanIntegrable : Integrable (fun x : ℝ =>
      burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value * star (column x)) :=
    conjugateRegular.const_mul _
  rw [L2.inner_def, L2.inner_def, integral_congr_ae pointwise,
    integral_add (L2.integrable_inner (burnolAnnulusSamplingL2 column 0) (burnolMobiusSourceL2 value))
      meanIntegrable,
    integral_const_mul]
  simp only [Complex.star_def, integral_conj]

theorem twoColumn_wholeAmbient_transpose (positionColumn fourierColumn : BurnolL2)
    (positionSupported : originalPhysicalCutoff (1 / 2 : ℝ) positionColumn = positionColumn)
    (fourierSupported : originalPhysicalCutoff (1 / 2 : ℝ) fourierColumn = fourierColumn)
    (value : BurnolPaAmbientCarrier) :
    inner ℂ (positionColumn + fourierL2 fourierColumn) (value : BurnolL2) =
      (inner ℂ (burnolAnnulusSamplingL2 positionColumn 0) (burnolMobiusSourceL2 value) +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value *
          star (∫ x : ℝ, positionColumn x)) +
      (inner ℂ (burnolAnnulusSamplingL2 fourierColumn 0)
          (burnolMobiusSourceL2 (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value)) +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) *
          star (∫ x : ℝ, fourierColumn x)) := by
  have twice : fourierL2 (fourierL2 (value : BurnolL2)) = (value : BurnolL2) := by
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp value.property.2
  have siblingRead : inner ℂ (fourierL2 fourierColumn) (value : BurnolL2) =
      inner ℂ fourierColumn
        (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value : BurnolL2) := by
    have actual := fourierL2.inner_map_map fourierColumn (fourierL2 (value : BurnolL2))
    rw [twice] at actual
    exact actual
  rw [inner_add_left, siblingRead,
    halfColumn_wholeAmbient_transpose positionColumn positionSupported value,
    halfColumn_wholeAmbient_transpose fourierColumn fourierSupported]

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
