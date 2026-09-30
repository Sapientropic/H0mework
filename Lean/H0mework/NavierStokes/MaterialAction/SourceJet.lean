import H0mework.NavierStokes.MaterialAction.JetAction

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeSourceMaterialJet

open MeasureTheory Set
open PhysicsCore DiracExteriorMatterAction StageNineCurrentCoframeMatterTemporalPrincipal
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open NativePhysicalFourier NativePhysicalSource NativePhysicalTimeAction
open NativePhysicalGradient NativePauliCoframeAction NativeMaterialJetAction

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem gradient_trace (state : ComplexVorticityHilbertState) :
    (∑ direction : Coordinate, field state direction direction) = 0 := by
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext wave
  have read (direction : Coordinate) :
      (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (field state direction direction) wave =
        multiplier wave direction * biotSavartVelocityCoefficient wave (state wave) direction := by
    rw [UnitAddTorus.mFourierBasis_repr, field_fourier]
  simp only [map_sum, map_zero, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_zero, Pi.zero_apply,
    read, multiplier, mul_assoc, ← Finset.mul_sum]
  change Complex.I * (((2 * Real.pi : ℝ) : ℂ) *
    (complexWavevector wave ⬝ᵥ biotSavartVelocityCoefficient wave (state wave))) = 0
  rw [complexWavevector_dot_biotSavartVelocityCoefficient, mul_zero, mul_zero]

theorem gradient_trace_ae (state : ComplexVorticityHilbertState) :
    ∀ᵐ point : Torus, (∑ direction : Coordinate, (field state direction direction point).re) = 0 := by
  have zero : field state 0 0 + field state 1 1 + field state 2 2 = 0 := by
    simpa only [Fin.sum_univ_three] using gradient_trace state
  have sum := Lp.coeFn_add (field state 0 0 + field state 1 1) (field state 2 2)
  rw [zero] at sum
  filter_upwards [sum, Lp.coeFn_add (field state 0 0) (field state 1 1),
    Lp.coeFn_zero ℂ 2 (volume : Measure Torus)] with point total hadd hzero
  have combined : field state 0 0 point + field state 1 1 point + field state 2 2 point = 0 := by
    change (0 : ScalarField) point = (field state 0 0 + field state 1 1) point + field state 2 2 point at total
    rw [hzero, hadd] at total
    exact total.symm
  simpa only [Fin.sum_univ_three, Complex.add_re, Complex.zero_re] using congrArg Complex.re combined

def spatialJet (state : ComplexVorticityHilbertState) (point : Torus) (direction : Coordinate) : PhysicalSpace :=
  WithLp.toLp 2 (fun component => (field state direction component point).re)

/-- All four entries come from the same original receipt: its whole time tangent and complete spectral gradient. -/
def receiptJet {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) (point : Torus) :
    Fin 4 → PhysicalSpace :=
  Fin.cases (physicalTangent receipt time.1 point) (spatialJet (receipt.wholePath time) point)

theorem receiptJet_divergence {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, (∑ direction : Fin 3, normalizedJet (receiptJet receipt time point) direction.succ direction) = 0 := by
  filter_upwards [gradient_trace_ae (receipt.wholePath time)] with point divergence
  change (∑ direction : Fin 3, (field (receipt.wholePath time) direction direction point).re / 4) = 0
  rw [← Finset.sum_div, divergence, zero_div]

/-- The original receipt generates a connection whose complete inverse-gamma kinetic response vanishes. -/
theorem receipt_action_zero {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus,
      currentCoframeMatterTemporalPrincipalInverse (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
        (gaugeVectorAt (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
          (covariantDerivative (receiptField receipt time point) (receiptJet receipt time point))) = 0 := by
  filter_upwards [receiptJet_divergence receipt time] with point divergence
  rw [NativeMaterialJetAction.actual_inverse_response]
  rw [divergence, Complex.ofReal_zero, mul_zero, zero_smul]

theorem receipt_kineticVector_zero {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus,
      gaugeVectorAt (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
        (covariantDerivative (receiptField receipt time point) (receiptJet receipt time point)) = 0 := by
  filter_upwards [receipt_action_zero receipt time] with point response
  have actual := congrArg (currentCoframeMatterTemporalPrincipal
    (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))) response
  rw [currentCoframeMatterTemporalPrincipalInverse_right _
    (NativeCanonicalFluidCoframe.temporalPrincipal_noncharacteristic _), map_zero] at actual
  exact actual

/-- The producer consumes the original occurrence receipt all the way through its generated next contact. -/
theorem occurrence_kineticVector_zero {nu : Viscosity} (current : GeneratedWholeRestartCurrent nu) (index : ℕ) :
    let occurrence := generatedWholeRestartNativeActualOccurrence current index
    let receipt := NativeStressSource.occurrenceReceipt occurrence
    let time : Icc (0 : ℝ) occurrence.response.1.contact.time.1 :=
      ⟨_, receipt.requestedTimePos.le, le_rfl⟩
    ∀ᵐ point : Torus,
      gaugeVectorAt (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
        (covariantDerivative (receiptField receipt time point) (receiptJet receipt time point)) = 0 := by
  exact receipt_kineticVector_zero _ _

end
end SaturationMonoid.NavierStokes.NativeSourceMaterialJet
