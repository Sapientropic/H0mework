import H0mework.Physics.DiracEvolution.SafeCanonicalAffineBoundaryForcing
import H0mework.Physics.DiracEvolution.SafeCanonicalForcedCrossLevelEnergy

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineUniformEnergy

open Set
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryForcing
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalForcedCrossLevelEnergy
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy

noncomputable section

set_option autoImplicit false

private theorem fixedP506L0CauchySafeMatterCanonicalAffineCorrection_energy_le
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C κ K δ : ℝ)
    (estimate : CanonicalForcedPhysicalErrorEstimate
      0 timeEnd a b C κ K)
    (forcingBound : ∀ testCount : ℕ, ∀ time ∈ Icc 0 timeEnd,
      ‖boundaryLiftGeneratedSynthesis time a b testCount‖ ≤ δ)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc 0 timeEnd) :
    κ *
        ‖fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
          (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
            timeEnd timeNonnegative a b testCount time)‖ ^ 2 ≤
      gronwallBound 0 (K + κ⁻¹)
        ((‖matterFiberMassRieszCoordinateBilinear‖ * C * δ) ^ 2) time := by
  let error :=
    fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount
  let forcing := fun candidateTime ↦
    boundaryLiftForcing a b testCount candidateTime
  have errorEvolution : ∀ candidateTime ∈ Icc 0 timeEnd,
      HasDerivWithinAt error
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount candidateTime (error candidateTime) +
          forcing candidateTime)
        (Icc 0 timeEnd) candidateTime := by
    intro candidateTime candidateTimeMem
    apply (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_evolution
      timeEnd timeNonnegative a b testCount candidateTime
        candidateTimeMem).congr_deriv
    simp only [error, forcing]
    abel
  have forcingPhysicalBound : ∀ candidateTime ∈ Icc 0 timeEnd,
      ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
        a b testCount (forcing candidateTime)‖ ≤ δ := by
    intro candidateTime candidateTimeMem
    exact forcingBound testCount candidateTime candidateTimeMem
  have energyBound := estimate testCount error forcing errorEvolution δ
    forcingPhysicalBound time timeMem
  have initialEnergyZero :
      ‖galerkinWeakEnergy
        (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
        error 0‖ = 0 := by
    simp [galerkinWeakEnergy, error,
      fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_initial]
  rw [initialEnergyZero] at energyBound
  simpa only [error, sub_zero] using energyBound

private theorem exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound_of_constants
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C κ K δ : ℝ)
    (κPositive : 0 < κ)
    (KNonnegative : 0 ≤ K)
    (estimate : CanonicalForcedPhysicalErrorEstimate
      0 timeEnd a b C κ K)
    (forcingBound : ∀ testCount : ℕ, ∀ time ∈ Icc 0 timeEnd,
      ‖boundaryLiftGeneratedSynthesis time a b testCount‖ ≤ δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ testCount : ℕ, ∀ time ∈ Icc 0 timeEnd,
      ‖fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
        (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
          timeEnd timeNonnegative a b testCount time)‖ ≤ B := by
  let rate := K + κ⁻¹
  let forcingScale :=
    (‖matterFiberMassRieszCoordinateBilinear‖ * C * δ) ^ 2
  let budget := gronwallBound 0 rate forcingScale timeEnd
  let B := budget / κ + 1
  have rateNonnegative : 0 ≤ rate := by
    unfold rate
    positivity
  have forcingScaleNonnegative : 0 ≤ forcingScale := by
    unfold forcingScale
    positivity
  have budgetNonnegative : 0 ≤ budget := by
    calc
      0 = gronwallBound 0 rate forcingScale 0 := by
        rw [gronwallBound_x0]
      _ ≤ gronwallBound 0 rate forcingScale timeEnd :=
        gronwallBound_mono (by positivity) forcingScaleNonnegative
          rateNonnegative timeNonnegative
      _ = budget := rfl
  have BNonnegative : 0 ≤ B := by
    unfold B
    positivity
  refine ⟨B, BNonnegative, ?_⟩
  intro testCount time timeMem
  have energyBound :=
    fixedP506L0CauchySafeMatterCanonicalAffineCorrection_energy_le
      timeEnd timeNonnegative a b C κ K δ estimate forcingBound
        testCount time timeMem
  have energyBoundAtEnd :
      κ *
          ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount
            (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
              timeEnd timeNonnegative a b testCount time)‖ ^ 2 ≤ budget := by
    calc
      _ ≤ gronwallBound 0 rate forcingScale time := by
        simpa only [rate, forcingScale] using energyBound
      _ ≤ gronwallBound 0 rate forcingScale timeEnd := by
        apply gronwallBound_mono (by positivity) forcingScaleNonnegative
          rateNonnegative
        simpa using timeMem.2
      _ = budget := rfl
  let fieldNorm := ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
    a b testCount
    (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount time)‖
  have fieldNormSquareBound : fieldNorm ^ 2 ≤ budget / κ := by
    apply (le_div_iff₀ κPositive).2
    simpa only [fieldNorm, pow_two, mul_comm] using energyBoundAtEnd
  have fieldNormNonnegative : 0 ≤ fieldNorm := norm_nonneg _
  change fieldNorm ≤ B
  unfold B
  nlinarith [sq_nonneg (fieldNorm - 1)]

private theorem exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound_of_forcing
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (δ : ℝ)
    (forcingBound : ∀ testCount : ℕ, ∀ time ∈ Icc 0 timeEnd,
      ‖boundaryLiftGeneratedSynthesis time a b testCount‖ ≤ δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ testCount : ℕ, ∀ time ∈ Icc 0 timeEnd,
      ‖fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
        (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
          timeEnd timeNonnegative a b testCount time)‖ ≤ B := by
  obtain ⟨C, κ, K, _CNonnegative, κPositive, KNonnegative, estimate⟩ :=
    exists_fixedP506L0CauchySafeMatterCanonicalForcedPhysicalError_bound
      0 timeEnd timeNonnegative a b boxOrder
  exact
    exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound_of_constants
      timeEnd timeNonnegative a b C κ K δ κPositive
        KNonnegative estimate forcingBound

theorem exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ testCount : ℕ, ∀ time ∈ Icc 0 timeEnd,
      ‖fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
        (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
          timeEnd timeNonnegative a b testCount time)‖ ≤ B := by
  obtain ⟨δ, _δNonnegative, forcingBound⟩ :=
    exists_boundaryLiftGeneratedSynthesis_uniform_bound
      timeEnd timeNonnegative a b boxOrder
  exact
    exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound_of_forcing
      timeEnd timeNonnegative a b boxOrder δ forcingBound

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineUniformEnergy
