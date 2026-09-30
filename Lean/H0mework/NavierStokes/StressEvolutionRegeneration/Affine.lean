import H0mework.NavierStokes.StressDynamics.TemporalDifferential

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeAffineTransport

open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open NativeCommonAdvectorAction NativeRawStressAction NativeTemporalResolventReentry
open NativeRecoveryTimeGramAction NativeTimeJetCarrier

noncomputable section

def pairCoefficient (first second : IntegerWavevector) : ComplexVorticityHilbertState →L[ℝ] ℂ :=
  (-(Complex.I * (2 * Real.pi : ℝ))) •
    ((NativeTemporalResolventReentry.dotCLM second).comp
      ((biotSavartVelocityCLM first).comp (evaluation first)))

theorem pair_original (advector : ComplexVorticityHilbertState) (first second : IntegerWavevector) :
    pairCLM advector first second = pairCoefficient first second advector • evaluation second := by
  simp only [pairCLM, pairCoefficient, smul_apply, ContinuousLinearMap.comp_apply,
    NativeTemporalResolventReentry.dotCLM_apply, smul_eq_mul]
  change -(_ * _) • evaluation second = (-_ * _) • evaluation second
  rw [neg_mul]
  rfl

theorem pair_add (first last : ComplexVorticityHilbertState) (a b : IntegerWavevector) :
    pairCLM (first + last) a b = pairCLM first a b + pairCLM last a b := by
  apply ContinuousLinearMap.ext
  intro velocity
  funext coordinate
  simp only [pair_original, map_add, smul_apply, add_apply, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, add_mul]

theorem pair_smul (scalar : ℝ) (advector : ComplexVorticityHilbertState) (a b : IntegerWavevector) :
    pairCLM (scalar • advector) a b = scalar • pairCLM advector a b := by
  simp only [pair_original, map_smul, smul_assoc]

theorem pair_zero (first second : IntegerWavevector) : pairCLM 0 first second = 0 := by
  apply ContinuousLinearMap.ext
  intro velocity
  funext coordinate
  simp [pair_original, smul_apply, Pi.smul_apply]

theorem convection_zero (frequencies : Finset IntegerWavevector) (wave : IntegerWavevector) :
    convectionCLM frequencies 0 wave = 0 := by
  simp [convectionCLM, pair_zero]

theorem convection_add (frequencies : Finset IntegerWavevector)
    (first last : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    convectionCLM frequencies (first + last) wave =
      convectionCLM frequencies first wave + convectionCLM frequencies last wave := by
  simp only [convectionCLM, pair_add, ite_add_zero, Finset.sum_add_distrib]

theorem convection_smul (frequencies : Finset IntegerWavevector) (scalar : ℝ)
    (advector : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    convectionCLM frequencies (scalar • advector) wave = scalar • convectionCLM frequencies advector wave := by
  simp only [convectionCLM, pair_smul, Finset.smul_sum, smul_ite, smul_zero]

theorem difference_row (frequencies : Finset IntegerWavevector) (nu : Viscosity)
    (advector velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    ((frozenOperator frequencies nu advector - frozenOperator frequencies nu 0) velocity) wave =
      if wave ∈ frequencies then transverseProjectionCLM wave (convectionCLM frequencies advector wave velocity) else 0 := by
  change frozenOperator frequencies nu advector velocity wave - frozenOperator frequencies nu 0 velocity wave = _
  rw [operator_apply, operator_apply]
  by_cases inside : wave ∈ frequencies
  · simp only [if_pos inside, convection_zero, zero_apply, zero_sub]
    change transverseProjectionCLM wave (_ - _) - transverseProjectionCLM wave (-_) = _
    rw [map_sub, map_neg]
    abel
  · simp only [if_neg inside, sub_self]

theorem difference_add (frequencies : Finset IntegerWavevector) (nu : Viscosity)
    (first last : ComplexVorticityHilbertState) :
    frozenOperator frequencies nu (first + last) - frozenOperator frequencies nu 0 =
      (frozenOperator frequencies nu first - frozenOperator frequencies nu 0) +
        (frozenOperator frequencies nu last - frozenOperator frequencies nu 0) := by
  apply ContinuousLinearMap.ext
  intro velocity
  apply lp.ext
  funext wave
  change ((frozenOperator frequencies nu (first + last) - frozenOperator frequencies nu 0) velocity) wave =
    ((frozenOperator frequencies nu first - frozenOperator frequencies nu 0) velocity) wave +
      ((frozenOperator frequencies nu last - frozenOperator frequencies nu 0) velocity) wave
  simp only [difference_row, convection_add, add_apply, map_add, ite_add_zero]

theorem difference_smul (frequencies : Finset IntegerWavevector) (nu : Viscosity)
    (scalar : ℝ) (advector : ComplexVorticityHilbertState) :
    frozenOperator frequencies nu (scalar • advector) - frozenOperator frequencies nu 0 =
      scalar • (frozenOperator frequencies nu advector - frozenOperator frequencies nu 0) := by
  apply ContinuousLinearMap.ext
  intro velocity
  apply lp.ext
  funext wave
  change ((frozenOperator frequencies nu (scalar • advector) - frozenOperator frequencies nu 0) velocity) wave =
    scalar • ((frozenOperator frequencies nu advector - frozenOperator frequencies nu 0) velocity) wave
  simp only [difference_row, convection_smul, smul_apply, map_smul, smul_ite, smul_zero]

/-- The first input is vorticity; the second is the transported velocity. -/
def transport (frequencies : Finset IntegerWavevector) (nu : Viscosity) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState where
  toLinearMap :=
    { toFun := fun advector => frozenOperator frequencies nu advector - frozenOperator frequencies nu 0
      map_add' := difference_add frequencies nu
      map_smul' := difference_smul frequencies nu }
  cont := (frozen_smooth (nu := nu) frequencies).continuous.sub continuous_const

theorem frozen_split (frequencies : Finset IntegerWavevector) (nu : Viscosity)
    (advector : ComplexVorticityHilbertState) :
    frozenOperator frequencies nu advector = transport frequencies nu advector + frozenOperator frequencies nu 0 := by
  change frozenOperator frequencies nu advector =
    (frozenOperator frequencies nu advector - frozenOperator frequencies nu 0) + frozenOperator frequencies nu 0
  exact (sub_add_cancel _ _).symm

theorem frozen_hasFDerivAt (frequencies : Finset IntegerWavevector) (nu : Viscosity)
    (advector : ComplexVorticityHilbertState) :
    HasFDerivAt (frozenOperator frequencies nu) (transport frequencies nu) advector := by
  simpa only [← frozen_split] using
    (transport frequencies nu).hasFDerivAt.add_const (frozenOperator frequencies nu 0)

theorem frozen_fderiv (frequencies : Finset IntegerWavevector) (nu : Viscosity)
    (advector : ComplexVorticityHilbertState) :
    fderiv ℝ (frozenOperator frequencies nu) advector = transport frequencies nu :=
  (frozen_hasFDerivAt frequencies nu advector).fderiv

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeSourceResolvent NativeRecoveryTimeGramAction

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem source_dotA (source : StressAt escape) (index : ℕ) (time : ℝ) :
    dotA source index time = transport (modes source index) nu
      (finiteStateVorticityGenerator (modes source index) nu.coeff ((stage source index).trajectory time)) := by
  rw [dotA, frozen_fderiv]

theorem source_hasDerivAt (source : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (sourceOperator source index)
      (transport (modes source index) nu
        (finiteStateVorticityGenerator (modes source index) nu.coeff ((stage source index).trajectory time))) time := by
  simpa only [source_dotA] using operator_hasDerivAt source index time inside

end
end SaturationMonoid.NavierStokes.NativeAffineTransport
