import H0mework.Versions.X.NavierStokes.StressResolvent.FiniteResolvent

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeResolventAdjoint

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open NativeFiniteActionResolvent NativeCommonAdvectorAction

noncomputable section

theorem negative_reality {advector : ComplexVorticityHilbertState}
    (reality : FiniteStateFourierReality advector) : FiniteStateFourierReality (-advector) := by
  intro wave
  funext coordinate
  change -(advector (waveNeg wave) coordinate) = star (-(advector wave coordinate))
  rw [congrFun (reality wave) coordinate]
  simp only [vectorConj, star_neg]

theorem velocity_negative (advector : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    finiteStateVelocityCoefficient (-advector) wave = -(finiteStateVelocityCoefficient advector wave) :=
  (biotSavartVelocityCLM wave).map_neg (advector wave)

theorem bilinear_negative (frequencies : Finset IntegerWavevector)
    (advector transported : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    finiteStateVelocityBilinearCoefficientAt frequencies (-advector) transported wave =
      -finiteStateVelocityBilinearCoefficientAt frequencies advector transported wave := by
  unfold finiteStateVelocityBilinearCoefficientAt
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro first firstMem
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro second secondMem
  by_cases same : first + second = wave
  · simp only [if_pos same, finiteStateVelocityBilinearPairContribution,
      velocity_negative, dotProduct_neg, mul_neg, neg_neg, neg_smul]
  · simp only [if_neg same, neg_zero]

theorem trilinear_negative (frequencies : Finset IntegerWavevector)
    (test advector transported : ComplexVorticityHilbertState) :
    finiteStateVelocityBilinearEnergyPairing frequencies test (-advector) transported =
      -finiteStateVelocityBilinearEnergyPairing frequencies test advector transported := by
  simp only [finiteStateVelocityBilinearEnergyPairing, bilinear_negative, complexCoordinateRealInner,
    Pi.neg_apply, mul_neg, Complex.neg_re, Complex.neg_im, ← neg_add, Finset.sum_neg_distrib]

theorem pairing_symmetric (frequencies : Finset IntegerWavevector) (x y : physicalSpace frequencies) :
    pairing frequencies x y = pairing frequencies y x := by
  change inner ℝ (coefficients frequencies x) (coefficients frequencies y) =
    inner ℝ (coefficients frequencies y) (coefficients frequencies x)
  exact real_inner_comm _ _

theorem operator_mixed_pairing (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (x y : physicalSpace frequencies) :
    pairing frequencies x (physicalOperator frequencies zeroNotMem closed nu advector reality y) =
      finiteStateVelocityBilinearEnergyPairing frequencies (curlLift frequencies x.1) advector
        (curlLift frequencies y.1) - nu.coeff * curlPair frequencies x.1 y.1 := by
  rw [pairing_eq]
  exact operator_pairing frequencies zeroNotMem nu advector x.1 y.1
    (physical_transverse x) (physical_transverse y)

/-- Negating only the original advector gives its dual action with the same viscosity. -/
theorem operator_adjoint (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (x y : physicalSpace frequencies) :
    pairing frequencies (physicalOperator frequencies zeroNotMem closed nu advector reality x) y =
      pairing frequencies x
        (physicalOperator frequencies zeroNotMem closed nu (-advector) (negative_reality reality) y) := by
  rw [pairing_symmetric]
  have cross := cross_dissipation frequencies zeroNotMem closed nu advector x.1 y.1
    (physical_transverse x) (physical_transverse y)
    (physical_reality (fun {_} member => closed _ member) x)
    (physical_reality (fun {_} member => closed _ member) y)
  rw [operator_mixed_pairing, operator_mixed_pairing, trilinear_negative]
  rw [operator_pairing frequencies zeroNotMem nu advector x.1 y.1
    (physical_transverse x) (physical_transverse y),
    operator_pairing frequencies zeroNotMem nu advector y.1 x.1
      (physical_transverse y) (physical_transverse x)] at cross
  linarith

/-- Both inverse maps are generated by the original physical resolvent constructor. -/
theorem resolver_adjoint (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (step : ℝ) (nonnegative : 0 ≤ step)
    (x y : physicalSpace frequencies) :
    pairing frequencies (physicalResolver frequencies zeroNotMem closed nu advector reality step nonnegative x) y =
      pairing frequencies x (physicalResolver frequencies zeroNotMem closed nu (-advector)
        (negative_reality reality) step nonnegative y) := by
  let positiveAction := physicalOperator frequencies zeroNotMem closed nu advector reality
  let negativeAction := physicalOperator frequencies zeroNotMem closed nu (-advector) (negative_reality reality)
  let first := physicalResolver frequencies zeroNotMem closed nu advector reality step nonnegative x
  let last := physicalResolver frequencies zeroNotMem closed nu (-advector) (negative_reality reality) step nonnegative y
  have firstWrite : first - step • positiveAction first = x :=
    resolver_write positiveAction (pairing frequencies) (pairing_faithful frequencies)
      (physicalOperator_dissipative _ _ _ _ _ _) step nonnegative x
  have lastWrite : last - step • negativeAction last = y :=
    resolver_write negativeAction (pairing frequencies) (pairing_faithful frequencies)
      (physicalOperator_dissipative _ _ _ _ _ _) step nonnegative y
  have adjoint := operator_adjoint frequencies zeroNotMem closed nu advector reality first last
  change pairing frequencies first y = pairing frequencies x last
  calc
    _ = pairing frequencies first (last - step • negativeAction last) := congrArg (pairing frequencies first) lastWrite.symm
    _ = pairing frequencies (first - step • positiveAction first) last := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [adjoint]
    _ = _ := congrArg (fun value => pairing frequencies value last) firstWrite

end
end SaturationMonoid.NavierStokes.NativeResolventAdjoint
