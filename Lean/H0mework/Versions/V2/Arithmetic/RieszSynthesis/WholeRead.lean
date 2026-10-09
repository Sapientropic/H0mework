import H0mework.Versions.V2.Arithmetic.RieszSynthesis.WholeTranspose
import H0mework.Versions.V2.Arithmetic.RieszColumns.ColumnsRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSynthesis

open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszFiniteColumns OriginalRieszFiniteSource
noncomputable section

def sourceFourierDefect (value : BurnolPaAmbientCarrier) : BurnolL2 :=
  burnolMobiusSourceL2 (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) -
    burnolTateReciprocalL2 (burnolMobiusSourceL2 value)

theorem sourceFourierDefect_onPa (value : BurnolPaAmbientCarrier)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) : sourceFourierDefect value = 0 := by
  rw [sourceFourierDefect, burnolMobiusSource_fourier value inPa, sub_self]

/-- Both source faces are evaluated on their actual full Ambient input. -/
def wholeSourceRead (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (value : BurnolPaAmbientCarrier) : ℂ :=
  (inner ℂ (burnolAnnulusSamplingL2 (positionColumn coordinate shift) 0) (burnolMobiusSourceL2 value) +
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value *
      star (∫ x : ℝ, positionColumn coordinate shift x)) +
  (inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0)
      (burnolMobiusSourceL2 (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value)) +
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) *
      star (∫ x : ℝ, fourierColumn coordinate shift x))

theorem forcing_wholeSourceRead (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (bounded : |shift| ≤ Real.log 2) (value : BurnolPaAmbientCarrier) :
    inner ℂ (forcingIntegral coordinate shift) (value : BurnolL2) =
      wholeSourceRead coordinate shift value := by
  rw [forcingIntegral_columns]
  exact twoColumn_wholeAmbient_transpose (positionColumn coordinate shift) (fourierColumn coordinate shift)
    (positionColumn_half coordinate shift bounded) (fourierColumn_half coordinate shift bounded) value

theorem wholeSourceRead_keeps_defect (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (value : BurnolPaAmbientCarrier) :
    wholeSourceRead coordinate shift value = firstSourceRead coordinate shift value +
      inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0) (sourceFourierDefect value) := by
  unfold wholeSourceRead firstSourceRead sourceFourierDefect
  rw [inner_sub_right]
  ring

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
