import H0mework.Versions.X.NavierStokes.StressDynamics.RawAction
import H0mework.NavierStokes.Energy.FiniteKineticDifferenceCancellation
import H0mework.NavierStokes.Energy.WholeKineticDifferenceCancellation

set_option autoImplicit false
open scoped BigOperators Topology Matrix

namespace SaturationMonoid.NavierStokes.NativeCommonAdvectorAction

open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryTimeGramAction

noncomputable section

def evaluation (wave : IntegerWavevector) : ComplexVorticityHilbertState →L[ℝ] ComplexCoordinateVector :=
  lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave

def pairCLM (advector : ComplexVorticityHilbertState) (first second : IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℝ] ComplexCoordinateVector :=
  (-((Complex.I * (2 * Real.pi : ℝ)) *
    (complexWavevector second ⬝ᵥ finiteStateVelocityCoefficient advector first))) • evaluation second

def convectionCLM (modes : Finset IntegerWavevector) (advector : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexVorticityHilbertState →L[ℝ] ComplexCoordinateVector :=
  ∑ first ∈ modes, ∑ second ∈ modes, if first + second = wave then pairCLM advector first second else 0

def rowCLM (modes : Finset IntegerWavevector) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexVorticityHilbertState →L[ℝ] ComplexCoordinateVector :=
  (transverseProjectionCLM wave).comp
    (convectionCLM modes advector wave - (nu.coeff * integerWaveViscousMultiplier wave) • evaluation wave)

/-- The argument of this operator is the transported velocity Fourier field. -/
def frozenOperator (modes : Finset IntegerWavevector) (nu : Viscosity) (advector : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState :=
  ∑ wave ∈ modes, (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp
    (rowCLM modes nu advector wave)

theorem operator_apply (modes : Finset IntegerWavevector) (nu : Viscosity) (advector velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : frozenOperator modes nu advector velocity wave =
    if wave ∈ modes then transverseProjection wave
      (convectionCLM modes advector wave velocity - (nu.coeff * integerWaveViscousMultiplier wave) • velocity wave) else 0 := by
  simp only [frozenOperator, sum_apply, ContinuousLinearMap.comp_apply]
  change finiteComplexVorticityState modes (fun wave => rowCLM modes nu advector wave velocity) wave = _
  rw [finiteComplexVorticityState_apply]
  rfl

theorem operator_supported (modes : Finset IntegerWavevector) (nu : Viscosity) (advector velocity : ComplexVorticityHilbertState) :
    ∀ wave ∉ modes, frozenOperator modes nu advector velocity wave = 0 := by
  intro wave excluded
  rw [operator_apply, if_neg excluded]

theorem operator_transverse (modes : Finset IntegerWavevector) (nu : Viscosity) (advector velocity : ComplexVorticityHilbertState) :
    ∀ wave, complexWavevector wave ⬝ᵥ frozenOperator modes nu advector velocity wave = 0 := by
  intro wave
  rw [operator_apply]
  split_ifs
  · exact complexWavevector_dot_transverseProjection wave _
  · simp

theorem pair_negative (advector velocity : ComplexVorticityHilbertState)
    (advectorReality : FiniteStateFourierReality advector) (velocityReality : FiniteStateFourierReality velocity)
    (first second : IntegerWavevector) : pairCLM advector (waveNeg first) (waveNeg second) velocity =
      vectorConj (pairCLM advector first second velocity) := by
  change -((Complex.I * (2 * Real.pi : ℝ)) * (complexWavevector (waveNeg second) ⬝ᵥ
    finiteStateVelocityCoefficient advector (waveNeg first))) • velocity (waveNeg second) =
    vectorConj (-((Complex.I * (2 * Real.pi : ℝ)) *
      (complexWavevector second ⬝ᵥ finiteStateVelocityCoefficient advector first)) • velocity second)
  rw [finiteStateVelocityCoefficient_waveNeg (advectorReality first), velocityReality second,
    complexWavevector_waveNeg, neg_dotProduct, complexWavevector_dot_vectorConj, vectorConj_smul]
  congr 1
  simp

theorem convection_reality (modes : Finset IntegerWavevector) (closed : FiniteModeNegClosed modes)
    (advector velocity : ComplexVorticityHilbertState) (advectorReality : FiniteStateFourierReality advector)
    (velocityReality : FiniteStateFourierReality velocity) (wave : IntegerWavevector) :
    convectionCLM modes advector (waveNeg wave) velocity = vectorConj (convectionCLM modes advector wave velocity) := by
  simp only [convectionCLM, sum_apply, DFunLike.ite_apply, zero_apply, vectorConj_finset_sum]
  rw [Finset.sum_equiv integerWaveNegEquiv]
  · intro first
    exact (finiteModeNegClosed_mem_iff closed first).symm
  · intro first _
    rw [Finset.sum_equiv integerWaveNegEquiv]
    · intro second
      exact (finiteModeNegClosed_mem_iff closed second).symm
    · intro second _
      have condition : first + second = waveNeg wave ↔ integerWaveNegEquiv first + integerWaveNegEquiv second = wave := by
        constructor <;> intro same <;> have negative := congrArg waveNeg same
        · simpa [integerWaveNegEquiv_apply, waveNeg, add_comm] using negative
        · simpa [integerWaveNegEquiv_apply, waveNeg, add_comm] using negative
      by_cases same : first + second = waveNeg wave
      · rw [if_pos same, if_pos (condition.mp same), integerWaveNegEquiv_apply, integerWaveNegEquiv_apply,
          pair_negative advector velocity advectorReality velocityReality, vectorConj_involutive]
      · rw [if_neg same, if_neg (fun equality => same (condition.mpr equality)), vectorConj_zero]

theorem operator_reality (modes : Finset IntegerWavevector) (closed : FiniteModeNegClosed modes) (nu : Viscosity)
    (advector velocity : ComplexVorticityHilbertState) (advectorReality : FiniteStateFourierReality advector)
    (velocityReality : FiniteStateFourierReality velocity) : FiniteStateFourierReality (frozenOperator modes nu advector velocity) := by
  intro wave
  simp only [operator_apply, finiteModeNegClosed_mem_iff closed]
  split_ifs
  · have scalarConj (r : ℝ) (v : ComplexCoordinateVector) : vectorConj (r • v) = r • vectorConj v := by
      funext coordinate
      simp [vectorConj]
    rw [convection_reality modes closed advector velocity advectorReality velocityReality, velocityReality wave,
      integerWaveViscousMultiplier_waveNeg, ← scalarConj, ← vectorConj_sub, transverseProjection_waveNeg_vectorConj]
  · exact vectorConj_zero.symm

def curlLift (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes (fun wave => fourierCurlCoefficient wave (velocity wave))

theorem curlLift_reads (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes) (velocity : ComplexVorticityHilbertState)
    (transverse : FiniteStateTransverseOn modes velocity) (wave : IntegerWavevector) (inside : wave ∈ modes) :
    finiteStateVelocityCoefficient (curlLift modes velocity) wave = velocity wave := by
  have nonzero : wave ≠ 0 := fun zero => zeroNotMem (zero ▸ inside)
  rw [finiteStateVelocityCoefficient, curlLift, finiteComplexVorticityState_apply, if_pos inside,
    biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ nonzero]
  exact transverseProjection_eq_self_of_transverse nonzero (transverse wave inside)

theorem curlLift_reality (modes : Finset IntegerWavevector) (closed : FiniteModeNegClosed modes)
    (velocity : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality velocity) :
    FiniteStateFourierReality (curlLift modes velocity) := by
  intro wave
  simp only [curlLift, finiteComplexVorticityState_apply, finiteModeNegClosed_mem_iff closed]
  split_ifs
  · rw [reality wave, fourierCurlCoefficient_waveNeg_vectorConj]
  · exact vectorConj_zero.symm

theorem convection_curlLift (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
    (advector velocity : ComplexVorticityHilbertState) (transverse : FiniteStateTransverseOn modes velocity)
    (wave : IntegerWavevector) : convectionCLM modes advector wave velocity =
      finiteStateVelocityBilinearCoefficientAt modes advector (curlLift modes velocity) wave := by
  simp only [convectionCLM, sum_apply]
  unfold finiteStateVelocityBilinearCoefficientAt
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second inside
  rw [finiteStateVelocityBilinearPairContribution, curlLift_reads modes zeroNotMem velocity transverse second inside]
  split_ifs <;> rfl

def velocityPair (modes : Finset IntegerWavevector) (first last : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes, complexCoordinateRealInner (first wave) (last wave)

def curlPair (modes : Finset IntegerWavevector) (first last : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes, complexCoordinateRealInner (fourierCurlCoefficient wave (first wave)) (fourierCurlCoefficient wave (last wave))

theorem curl_pair_row (wave : IntegerWavevector) (nonzero : wave ≠ 0) (first last : ComplexCoordinateVector)
    (firstTransverse : complexWavevector wave ⬝ᵥ first = 0) (lastTransverse : complexWavevector wave ⬝ᵥ last = 0) :
    integerWaveViscousMultiplier wave * complexCoordinateRealInner first last =
      complexCoordinateRealInner (fourierCurlCoefficient wave first) (fourierCurlCoefficient wave last) := by
  have curlTransverse : complexWavevector wave ⬝ᵥ fourierCurlCoefficient wave first = 0 := by
    simp [fourierCurlCoefficient, dotProduct_smul]
  have actual := complexCoordinateRealInner_biotSavartVelocityCoefficient wave nonzero
    (fourierCurlCoefficient wave first) (fourierCurlCoefficient wave last) curlTransverse
  rw [biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ nonzero,
    biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ nonzero,
    transverseProjection_eq_self_of_transverse nonzero firstTransverse,
    transverseProjection_eq_self_of_transverse nonzero lastTransverse] at actual
  have nonzeroScale := (integerWaveViscousMultiplier_pos ⟨wave, nonzero⟩).ne'
  exact (mul_comm _ _).trans ((eq_div_iff nonzeroScale).mp actual)

theorem operator_pairing (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes) (nu : Viscosity)
    (advector first last : ComplexVorticityHilbertState) (firstTransverse : FiniteStateTransverseOn modes first)
    (lastTransverse : FiniteStateTransverseOn modes last) :
    velocityPair modes first (frozenOperator modes nu advector last) =
      finiteStateVelocityBilinearEnergyPairing modes (curlLift modes first) advector (curlLift modes last) -
        nu.coeff * curlPair modes first last := by
  unfold velocityPair finiteStateVelocityBilinearEnergyPairing curlPair
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro wave inside
  have nonzero : wave ≠ 0 := fun zero => zeroNotMem (zero ▸ inside)
  rw [operator_apply, if_pos inside, complexCoordinateRealInner_transverseProjection wave _ _ nonzero (firstTransverse wave inside),
    complexCoordinateRealInner_sub_right, complexCoordinateRealInner_real_smul_right,
    convection_curlLift modes zeroNotMem advector last lastTransverse,
    curlLift_reads modes zeroNotMem first firstTransverse wave inside,
    ← curl_pair_row wave nonzero _ _ (firstTransverse wave inside) (lastTransverse wave inside)]
  ring

theorem cross_dissipation (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
    (closed : FiniteModeNegClosed modes) (nu : Viscosity) (advector first last : ComplexVorticityHilbertState)
    (firstTransverse : FiniteStateTransverseOn modes first) (lastTransverse : FiniteStateTransverseOn modes last)
    (firstReality : FiniteStateFourierReality first) (lastReality : FiniteStateFourierReality last) :
    velocityPair modes first (frozenOperator modes nu advector last) +
      velocityPair modes last (frozenOperator modes nu advector first) = -2 * nu.coeff * curlPair modes first last := by
  have skew := finiteStateVelocityBilinearEnergyPairing_reflect_swap modes closed
    (curlLift modes first) advector (curlLift modes last)
    (curlLift_reality modes closed first firstReality) (curlLift_reality modes closed last lastReality)
  have symmetric : curlPair modes last first = curlPair modes first last := by
    unfold curlPair complexCoordinateRealInner
    simp only [mul_comm]
  rw [operator_pairing modes zeroNotMem nu advector first last firstTransverse lastTransverse,
    operator_pairing modes zeroNotMem nu advector last first lastTransverse firstTransverse, skew, symmetric]
  ring

theorem convection_original (modes : Finset IntegerWavevector) (advector state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : convectionCLM modes advector wave (biotSavartCLM state) =
      finiteStateVelocityBilinearCoefficientAt modes advector state wave := by
  simp only [convectionCLM, sum_apply, finiteStateVelocityBilinearCoefficientAt]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  split_ifs
  · rw [biotSavartCLM_apply]
    rfl
  · rfl

theorem diagonal_original (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes) (nu : Viscosity)
    (state : ComplexVorticityHilbertState) (transverse : FiniteStateTransverseOn modes state) :
    frozenOperator modes nu state (biotSavartCLM state) = biotSavartCLM (finiteStateVorticityGenerator modes nu.coeff state) := by
  apply lp.ext
  funext wave
  rw [operator_apply, convection_original]
  simp only [biotSavartCLM_apply, wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient,
    finiteStateVorticityGenerator_apply]
  by_cases inside : wave ∈ modes
  · have nonzero : wave ≠ 0 := fun zero => zeroNotMem (zero ▸ inside)
    rw [if_pos inside, if_pos inside, biotSavartVelocityCoefficient_sub,
      finiteStateVorticityNonlinearCoefficientAt_eq_fourierCurl modes zeroNotMem state transverse,
      biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ nonzero]
    change transverseProjectionCLM wave (_ - _ • biotSavartVelocityCoefficient wave (state wave)) = _
    rw [map_sub, map_smul]
    simp only [transverseProjectionCLM_apply]
    rw [transverseProjection_eq_self_of_transverse nonzero (complexWavevector_dot_biotSavartVelocityCoefficient wave (state wave))]
    exact congrArg (fun value : ComplexCoordinateVector =>
      transverseProjection wave (finiteStateVelocityNonlinearCoefficientAt modes state wave) - value)
      ((biotSavartVelocityCLM wave).map_smul (nu.coeff * integerWaveViscousMultiplier wave) (state wave)).symm
  · rw [if_neg inside, if_neg inside]
    simp [biotSavartVelocityCoefficient]

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def sourceOperator (stress : StressAt escape) (index : ℕ) (time : ℝ) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState :=
  frozenOperator (wholeRestartModes (NativeRecoveryEscapeCarrier.radius escape (stress.refinement index))) nu
    ((NativeRawStressAction.stage stress index).trajectory time)

theorem source_diagonal (stress : StressAt escape) (index : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    sourceOperator stress index time (NativeRawStressAction.rawField stress index time) = NativeRawStressAction.rawRate stress index time :=
  diagonal_original _ (zero_not_mem_puncturedIntegerWaveFrequencyCube _) nu _
    (fun wave _ => ((NativeRawStressAction.stage stress index).physical time inside).2.2.1 wave)

theorem source_hasDerivAt (stress : StressAt escape) (index : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (NativeRawStressAction.rawField stress index)
      (sourceOperator stress index time (NativeRawStressAction.rawField stress index time)) time := by
  rw [source_diagonal stress index time inside]
  exact NativeRawStressAction.rawField_hasDerivAt stress index time inside

end
end SaturationMonoid.NavierStokes.NativeCommonAdvectorAction
