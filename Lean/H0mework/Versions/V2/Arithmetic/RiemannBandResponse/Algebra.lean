import H0mework.Versions.V2.Arithmetic.RiemannUnitRegularity.GeneratorCounting

/-! The original resolvent commutes with its actual dilation and reads the unit
response from the Fourier face of the same counting primitive. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolDirectRightResolvent_dilation (z : ℂ) (shift : ℝ) (value : BurnolL2) :
    burnolDirectRightResolvent z (burnolMultiplicativeDilation shift value) =
      burnolMultiplicativeDilation shift (burnolDirectRightResolvent z value) := by
  have mapped : burnolMultiplicativeDilation shift
      (∫ h : ℝ in Ioi 0, burnolDirectRightResolventIntegrand z value h) =
      ∫ h : ℝ in Ioi 0, burnolMultiplicativeDilation shift (burnolDirectRightResolventIntegrand z value h) :=
    (LinearIsometry.integral_comp_comm (burnolMultiplicativeDilation shift).toLinearIsometry _).symm
  unfold burnolDirectRightResolvent
  rw [map_neg, mapped]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h _
  simp only [burnolDirectRightResolventIntegrand, map_smul, burnolMultiplicativeDilation_add]
  rw [add_comm]

theorem burnolUnitTailResponse_fourierResolvent (coordinate : BurnolCompletedMellinCoordinate) :
    burnolUnitTailResponse coordinate 1 = fourierL2 burnolUnitCountingPrimitiveL2 +
      (coordinate.value / 2) • burnolDirectRightResolvent (coordinate.value / 2)
        (fourierL2 burnolUnitCountingPrimitiveL2) := by
  have right : 1 / 4 < (coordinate.value / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  have pair := burnolCountingPrimitiveFourierPair_eq_resolvent
  have head : burnolUnitCountingPrimitiveL2 =
      (-1 / 2 : ℂ) • burnolDirectRightResolvent (1 / 2) (fourierL2 burnolUnitCountingPrimitiveL2) -
        fourierL2 burnolUnitCountingPrimitiveL2 := eq_sub_of_add_eq pair
  have sourceRead : burnolDirectRightResolvent (coordinate.value / 2) burnolUnitCountingPrimitiveL2 =
      (-1 / 2 : ℂ) • burnolDirectRightResolvent (coordinate.value / 2)
        (burnolDirectRightResolvent (1 / 2) (fourierL2 burnolUnitCountingPrimitiveL2)) -
        burnolDirectRightResolvent (coordinate.value / 2) (fourierL2 burnolUnitCountingPrimitiveL2) := by
    calc
      _ = burnolDirectRightResolvent (coordinate.value / 2)
          ((-1 / 2 : ℂ) • burnolDirectRightResolvent (1 / 2) (fourierL2 burnolUnitCountingPrimitiveL2) -
            fourierL2 burnolUnitCountingPrimitiveL2) := congrArg (burnolDirectRightResolvent _) head
      _ = _ := by rw [burnolDirectRightResolvent_sub _ right, burnolDirectRightResolvent_smul]
  have identity := burnolDirectRightResolvent_identity (coordinate.value / 2) (1 / 2)
    right (by norm_num) (fourierL2 burnolUnitCountingPrimitiveL2)
  rw [burnolUnitTailResponse_one_eq_fixedResolvent, sourceRead]
  calc
    _ = -burnolUnitCountingPrimitiveL2 +
        ((coordinate.value - 1) / 2) • burnolDirectRightResolvent (coordinate.value / 2)
          (fourierL2 burnolUnitCountingPrimitiveL2) +
        (1 / 2 : ℂ) • ((coordinate.value / 2 - 1 / 2) •
          burnolDirectRightResolvent (coordinate.value / 2)
            (burnolDirectRightResolvent (1 / 2) (fourierL2 burnolUnitCountingPrimitiveL2))) := by module
    _ = _ := by
      rw [← identity]
      have replaced := congrArg (fun value : BurnolL2 => -value) head
      rw [replaced]
      module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
