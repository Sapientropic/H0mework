import H0mework.NavierStokes.FullOrder.RecoveryTimeCanonical
import H0mework.NavierStokes.FullOrder.RecoveryTimeGramWrite
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeBackgroundProjection

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeRecoveryTimeGramReadout NativePhysicalFourier NativeStressSource
open NativeEndpointVelocityCarrier
open NativeRecoveryTimeCanonical (background component)

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem background_inner (stress : StressAt escape) (pointLe : point ≤ 1) (left right : IntegerWavevector) :
    inner ℂ (background stress pointLe left) (background stress pointLe right) =
      inner ℂ (lp.single 2 left (1 : ℂ) : ScalarSequence) (lp.single 2 right 1) := by
  exact tendsto_nhds_unique (pairing_tendsto stress pointLe (.inl left) (.inl right))
    (tendsto_const_nhds (x := inner ℂ (lp.single 2 left (1 : ℂ) : ScalarSequence) (lp.single 2 right 1)))

theorem background_orthonormal (stress : StressAt escape) (pointLe : point ≤ 1) :
    Orthonormal ℂ (background stress pointLe) := by
  classical
  rw [orthonormal_iff_ite]
  intro left right
  rw [background_inner, lp.inner_single_left]
  by_cases same : left = right
  · subst right
    simp [lp.single_apply]
  · simp [RCLike.inner_apply, lp.single_apply, same]

def embed (stress : StressAt escape) (pointLe : point ≤ 1) : ScalarSequence →ₗᵢ[ℂ] Space stress pointLe :=
  (background_orthonormal stress pointLe).orthogonalFamily.linearIsometry

theorem embed_single (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    embed stress pointLe (lp.single 2 wave (1 : ℂ)) = background stress pointLe wave := by
  simp [embed, OrthogonalFamily.linearIsometry_apply_single, LinearIsometry.toSpanSingleton_apply]

def meanRead (stress : StressAt escape) (pointLe : point ≤ 1) : Space stress pointLe →L[ℂ] ScalarSequence :=
  (embed stress pointLe).toContinuousLinearMap.adjoint

theorem meanRead_row (stress : StressAt escape) (pointLe : point ≤ 1) (value : Space stress pointLe)
    (wave : IntegerWavevector) : meanRead stress pointLe value wave = inner ℂ (background stress pointLe wave) value := by
  have adjoint := (embed stress pointLe).toContinuousLinearMap.adjoint_inner_right (lp.single 2 wave (1 : ℂ)) value
  change inner ℂ (lp.single 2 wave (1 : ℂ)) (meanRead stress pointLe value) =
    inner ℂ (embed stress pointLe (lp.single 2 wave (1 : ℂ))) value at adjoint
  rw [lp.inner_single_left, embed_single] at adjoint
  simpa only [RCLike.inner_apply, map_one, mul_one, meanRead] using adjoint

theorem meanRead_embed (stress : StressAt escape) (pointLe : point ≤ 1) (value : ScalarSequence) :
    meanRead stress pointLe (embed stress pointLe value) = value := by
  exact congrArg (fun operator : ScalarSequence →L[ℂ] ScalarSequence => operator value)
    (embed stress pointLe).adjoint_comp_self

theorem background_component (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (frequency wave : IntegerWavevector) (coordinate : Coordinate) :
    inner ℂ (background stress pointLe frequency) (component stress pointLe node wave coordinate) =
      receipt.wholePath (physicalTime escape pointLe node) (frequency - wave) coordinate := by
  have selected := pairing_tendsto stress pointLe (.inl frequency) (.inr (node, wave, coordinate))
  simp only [background_gram] at selected
  have original := ((continuous_apply coordinate).tendsto _ |>.comp
    (velocity_tendsto stress pointLe node (frequency - wave))).mono_left (generated stress pointLe).cofinal
  exact tendsto_nhds_unique selected original

theorem meanRead_component (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    meanRead stress pointLe (component stress pointLe node wave coordinate) =
      NativePairedCarrierJets.shifted (receipt.wholePath (physicalTime escape pointLe node)) wave coordinate := by
  apply lp.ext
  funext frequency
  rw [meanRead_row]
  exact background_component stress pointLe node frequency wave coordinate

def projection (stress : StressAt escape) (pointLe : point ≤ 1) : Space stress pointLe →L[ℂ] Space stress pointLe :=
  (embed stress pointLe).toContinuousLinearMap.comp (meanRead stress pointLe)

def remainder (stress : StressAt escape) (pointLe : point ≤ 1) : Space stress pointLe →L[ℂ] Space stress pointLe :=
  ContinuousLinearMap.id ℂ _ - projection stress pointLe

theorem decomposition (stress : StressAt escape) (pointLe : point ≤ 1) (value : Space stress pointLe) :
    value = embed stress pointLe (meanRead stress pointLe value) + remainder stress pointLe value := by
  change value = embed stress pointLe (meanRead stress pointLe value) +
    (value - embed stress pointLe (meanRead stress pointLe value))
  abel

theorem meanRead_remainder (stress : StressAt escape) (pointLe : point ≤ 1) (value : Space stress pointLe) :
    meanRead stress pointLe (remainder stress pointLe value) = 0 := by
  change meanRead stress pointLe (value - embed stress pointLe (meanRead stress pointLe value)) = 0
  rw [map_sub, meanRead_embed, sub_self]

theorem remainder_orthogonal (stress : StressAt escape) (pointLe : point ≤ 1)
    (value : Space stress pointLe) (mean : ScalarSequence) :
    inner ℂ (embed stress pointLe mean) (remainder stress pointLe value) = 0 := by
  have same := (embed stress pointLe).toContinuousLinearMap.adjoint_inner_right mean (remainder stress pointLe value)
  change inner ℂ mean (meanRead stress pointLe (remainder stress pointLe value)) = _ at same
  rw [meanRead_remainder, inner_zero_right] at same
  exact same.symm

theorem projection_idempotent (stress : StressAt escape) (pointLe : point ≤ 1) (value : Space stress pointLe) :
    projection stress pointLe (projection stress pointLe value) = projection stress pointLe value := by
  change embed stress pointLe (meanRead stress pointLe (embed stress pointLe (meanRead stress pointLe value))) = _
  rw [meanRead_embed]
  rfl

theorem remainder_inner (stress : StressAt escape) (pointLe : point ≤ 1) (left right : Space stress pointLe) :
    inner ℂ (remainder stress pointLe left) (remainder stress pointLe right) =
      inner ℂ left right - inner ℂ (meanRead stress pointLe left) (meanRead stress pointLe right) := by
  have first := (embed stress pointLe).toContinuousLinearMap.adjoint_inner_left (meanRead stress pointLe right) left
  have second := (embed stress pointLe).toContinuousLinearMap.adjoint_inner_right (meanRead stress pointLe left) right
  change inner ℂ (meanRead stress pointLe left) (meanRead stress pointLe right) =
    inner ℂ left (embed stress pointLe (meanRead stress pointLe right)) at first
  change inner ℂ (meanRead stress pointLe left) (meanRead stress pointLe right) =
    inner ℂ (embed stress pointLe (meanRead stress pointLe left)) right at second
  change inner ℂ (left - embed stress pointLe (meanRead stress pointLe left))
    (right - embed stress pointLe (meanRead stress pointLe right)) = _
  rw [inner_sub_left, inner_sub_right, inner_sub_right, ← first, ← second,
    (embed stress pointLe).inner_map_map]
  ring

theorem norm_account (stress : StressAt escape) (pointLe : point ≤ 1) (value : Space stress pointLe) :
    ‖value‖ ^ 2 = ‖meanRead stress pointLe value‖ ^ 2 + ‖remainder stress pointLe value‖ ^ 2 := by
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), remainder_inner]
  change (inner ℂ value value).re =
    (inner ℂ (meanRead stress pointLe value) (meanRead stress pointLe value)).re +
      (inner ℂ value value - inner ℂ (meanRead stress pointLe value) (meanRead stress pointLe value)).re
  rw [Complex.sub_re]
  ring

def residual (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) : Space stress pointLe :=
  remainder stress pointLe (component stress pointLe node wave coordinate)

theorem component_decomposition (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    component stress pointLe node wave coordinate =
      embed stress pointLe (NativePairedCarrierJets.shifted (receipt.wholePath (physicalTime escape pointLe node)) wave coordinate) +
        residual stress pointLe node wave coordinate := by
  rw [← meanRead_component]
  exact decomposition stress pointLe _

theorem cross_time_residual_pairing (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (left right : IntegerWavevector × Coordinate) :
    inner ℂ (residual stress pointLe first left.1 left.2) (residual stress pointLe last right.1 right.2) =
      inner ℂ (component stress pointLe first left.1 left.2) (component stress pointLe last right.1 right.2) -
        inner ℂ (NativePairedCarrierJets.shifted (receipt.wholePath (physicalTime escape pointLe first)) left.1 left.2)
          (NativePairedCarrierJets.shifted (receipt.wholePath (physicalTime escape pointLe last)) right.1 right.2) := by
  rw [residual, residual, remainder_inner, meanRead_component, meanRead_component]

theorem shifted_inner_mixed (left right : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality left) (leftWave rightWave : IntegerWavevector) (output input : Coordinate) :
    inner ℂ (NativePairedCarrierJets.shifted left leftWave output) (NativePairedCarrierJets.shifted right rightWave input) =
      -NativeHigherTimeJets.mixedFlux right left (leftWave - rightWave) output input := by
  rw [NativeHigherTimeJets.mixedFlux, neg_neg, lp.inner_eq_tsum]
  change (∑' frequency : IntegerWavevector, inner ℂ (left (frequency - leftWave) output) (right (frequency - rightWave) input)) = _
  rw [← (Equiv.addRight rightWave).tsum_eq]
  apply tsum_congr
  intro frequency
  simp only [Equiv.coe_addRight, add_sub_cancel_right, RCLike.inner_apply, starRingEnd_apply]
  have reflected : star (left (frequency + rightWave - leftWave) output) = left (leftWave - rightWave - frequency) output := by
    have indexEq : leftWave - rightWave - frequency = -(frequency + rightWave - leftWave) := by abel
    rw [indexEq]
    exact (congrFun (reality (frequency + rightWave - leftWave)) output).symm
  rw [reflected]

def stressBetween (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  -inner ℂ (component stress pointLe first wave output) (component stress pointLe last 0 input)

theorem component_pair_between (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (left right : IntegerWavevector × Coordinate) :
    inner ℂ (component stress pointLe first left.1 left.2) (component stress pointLe last right.1 right.2) =
      -stressBetween stress pointLe first last (left.1 - right.1) left.2 right.2 := by
  have raw (index : ℕ) : gram escape pointLe index (.inr (first, left)) (.inr (last, right)) =
      gram escape pointLe index (.inr (first, left.1 - right.1, left.2)) (.inr (last, 0, right.2)) := by
    change inner ℂ
      (NativePairedCarrierJets.shifted (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index first)) left.1 left.2)
      (NativePairedCarrierJets.shifted (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index last)) right.1 right.2) =
        inner ℂ
          (NativePairedCarrierJets.shifted (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index first)) (left.1 - right.1) left.2)
          (NativePairedCarrierJets.shifted (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index last)) 0 right.2)
    have realLeft := wholeVelocity_reality (NativeRecoveryTimeGramRaw.velocity escape pointLe index first)
      (NativeRecoveryTimeGramRaw.velocity_reality escape pointLe index first)
    have firstPair := shifted_inner_mixed
      (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index first))
      (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index last)) realLeft left.1 right.1 left.2 right.2
    have secondPair := shifted_inner_mixed
      (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index first))
      (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index last)) realLeft (left.1 - right.1) 0 left.2 right.2
    exact firstPair.trans (by simpa only [sub_zero] using secondPair.symm)
  have primary := pairing_tendsto stress pointLe (.inr (first, left)) (.inr (last, right))
  have normalized := pairing_tendsto stress pointLe (.inr (first, left.1 - right.1, left.2)) (.inr (last, 0, right.2))
  have equal := tendsto_nhds_unique primary (normalized.congr' (Eventually.of_forall fun index => (raw (stress.refinement index)).symm))
  simpa only [stressBetween, neg_neg, component] using equal

theorem cross_time_residual_stress (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (left right : IntegerWavevector × Coordinate) :
    inner ℂ (residual stress pointLe first left.1 left.2) (residual stress pointLe last right.1 right.2) =
      -(stressBetween stress pointLe first last (left.1 - right.1) left.2 right.2 -
        NativeHigherTimeJets.mixedFlux (receipt.wholePath (physicalTime escape pointLe last))
          (receipt.wholePath (physicalTime escape pointLe first)) (left.1 - right.1) left.2 right.2) := by
  rw [cross_time_residual_pairing, component_pair_between, shifted_inner_mixed _ _
    (NativeRecoveryPhysical.wholeMild_reality ledger receipt (physicalTime escape pointLe first))]
  ring

theorem residual_stress (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (left right : IntegerWavevector × Coordinate) :
    inner ℂ (residual stress pointLe node left.1 left.2) (residual stress pointLe node right.1 right.2) =
      -(stressRead stress pointLe node (left.1 - right.1) left.2 right.2 -
        quadraticFlux (receipt.wholePath (physicalTime escape pointLe node)) (left.1 - right.1) left.2 right.2) :=
  cross_time_residual_stress stress pointLe node node left right

theorem anchor_residual_stress (stress : StressAt escape) (pointLe : point ≤ 1)
    (left right : IntegerWavevector × Coordinate) :
    inner ℂ (residual stress pointLe .anchor left.1 left.2) (residual stress pointLe .anchor right.1 right.2) =
      -(stress.stress (left.1 - right.1) left.2 right.2 -
        quadraticFlux (receipt.wholePath (physicalTime escape pointLe .anchor)) (left.1 - right.1) left.2 right.2) := by
  rw [residual_stress, source_anchor_stress]

theorem meanRead_action (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    meanRead stress pointLe (NativeRecoveryTimeGramWrite.action stress pointLe first last wave coordinate) =
      NativePairedCarrierJets.shifted (receipt.wholePath (physicalTime escape pointLe last)) wave coordinate -
        NativePairedCarrierJets.shifted (receipt.wholePath (physicalTime escape pointLe first)) wave coordinate := by
  change meanRead stress pointLe (component stress pointLe last wave coordinate - component stress pointLe first wave coordinate) = _
  rw [map_sub, meanRead_component, meanRead_component]

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeBackgroundProjection
