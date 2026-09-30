import H0mework.Versions.Y.Arithmetic.RiemannBandKernel.TransposeKernel
import H0mework.Versions.Y.Arithmetic.MobiusSource.Tate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex MeasureTheory
open scoped InnerProductSpace
noncomputable section

theorem twoColumn_fullPa_transpose (positionColumn fourierColumn : BurnolL2)
    (positionIntegrable : Integrable positionColumn)
    (positionMoment : MemLp (fun x : ℝ => (x : ℂ) * positionColumn x) 2 volume)
    (fourierIntegrable : Integrable fourierColumn)
    (fourierMoment : MemLp (fun x : ℝ => (x : ℂ) * fourierColumn x) 2 volume)
    (value : BurnolPaAmbientCarrier) (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    inner ℂ (positionColumn + fourierL2 fourierColumn) (value : BurnolL2) =
      (inner ℂ (burnolPaSamplingKernel positionColumn) (burnolMobiusSourceL2 value) +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value *
          star (∫ x : ℝ, positionColumn x)) +
      (inner ℂ (burnolPaSamplingKernel fourierColumn)
          (burnolTateReciprocalL2 (burnolMobiusSourceL2 value)) +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) *
          star (∫ x : ℝ, fourierColumn x)) := by
  have siblingIn : evenFaceFourierEquiv burnolUnscaledCommonGapRadius value ∈
      burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inPa
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
    burnolPaSamplingKernel_fullPa positionColumn positionIntegrable positionMoment value inPa,
    burnolPaSamplingKernel_fullPa fourierColumn fourierIntegrable fourierMoment _ siblingIn,
    burnolMobiusSource_fourier value inPa]

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
