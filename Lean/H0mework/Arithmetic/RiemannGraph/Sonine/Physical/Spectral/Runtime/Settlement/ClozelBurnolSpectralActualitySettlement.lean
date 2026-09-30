import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import H0mework.Arithmetic.BurnolMellin.PairedMellinCharacterRigidity
import H0mework.Arithmetic.RiemannGraph.Sonine.Physical.Spectral.Runtime.Face.ClozelBurnolPhysicalActionFace
import H0mework.Arithmetic.RiemannGraph.Sonine.Physical.Spectral.Runtime.Claim.ClozelBurnolSpectralActualityClaim

/-!
# Spectral actuality settlement

A settlement contains a normalized kernel event for the already installed
true Fourier-fixed multiplicative compression.  Symmetry makes its paired
character real, contractivity bounds its norm, and the source-neutral paired
character rigidity theorem forces the critical line.  None of these data is
stored in the zero-field claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace SpectralActuality

open scoped InnerProductSpace

noncomputable section

def pairedPhysicalActionPencil (coordinate : ℂ) :
    BurnolPhysicalActionCarrier →L[ℂ] BurnolPhysicalActionCarrier :=
  burnolPhysicalActionCompression -
    pairedMellinTranslationCharacter coordinate (Real.log stageZeroSonineQ) •
      ContinuousLinearMap.id ℂ BurnolPhysicalActionCarrier

structure NormalizedPhysicalKernelEventAt (coordinate : ℂ) : Type where
  state : BurnolPhysicalActionCarrier
  normalized : ‖state‖ = 1
  kernel : pairedPhysicalActionPencil coordinate state = 0

theorem NormalizedPhysicalKernelEventAt.state_ne_zero
    {coordinate : ℂ} (event : NormalizedPhysicalKernelEventAt coordinate) :
    event.state ≠ 0 := by
  intro stateZero
  have : (0 : ℝ) = 1 := by simpa [stateZero] using event.normalized
  norm_num at this

theorem NormalizedPhysicalKernelEventAt.eigenlaw
    {coordinate : ℂ} (event : NormalizedPhysicalKernelEventAt coordinate) :
    burnolPhysicalActionCompression event.state =
      pairedMellinTranslationCharacter coordinate
        (Real.log stageZeroSonineQ) • event.state := by
  exact sub_eq_zero.mp event.kernel

theorem NormalizedPhysicalKernelEventAt.character_real
    {coordinate : ℂ} (event : NormalizedPhysicalKernelEventAt coordinate) :
    (pairedMellinTranslationCharacter coordinate
      (Real.log stageZeroSonineQ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  let embed : BurnolPhysicalActionCarrier → BurnolL2 := fun state =>
    ((state : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
      BurnolL2)
  have embed_smul (coefficient : ℂ) (state : BurnolPhysicalActionCarrier) :
      embed (coefficient • state) = coefficient • embed state := rfl
  have embed_norm (state : BurnolPhysicalActionCarrier) :
      ‖embed state‖ = ‖state‖ := rfl
  have ambientEigen := congrArg embed event.eigenlaw
  have innerOne : inner ℂ (embed event.state) (embed event.state) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, embed_norm, event.normalized]
    norm_num
  have symmetric :=
    burnolPhysicalActionCompression_symmetric event.state event.state
  change inner ℂ (embed (burnolPhysicalActionCompression event.state))
      (embed event.state) =
    inner ℂ (embed event.state)
      (embed (burnolPhysicalActionCompression event.state)) at symmetric
  rw [ambientEigen, embed_smul, inner_smul_left, inner_smul_right, innerOne,
    mul_one, mul_one] at symmetric
  exact symmetric

theorem NormalizedPhysicalKernelEventAt.character_norm_le_one
    {coordinate : ℂ} (event : NormalizedPhysicalKernelEventAt coordinate) :
    ‖pairedMellinTranslationCharacter coordinate
      (Real.log stageZeroSonineQ)‖ ≤ 1 := by
  have contraction := burnolPhysicalActionCompression_contractive event.state
  have ambientEigen := congrArg
    (fun state : BurnolPhysicalActionCarrier =>
      ((state : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
        BurnolL2)) event.eigenlaw
  have ambientNormalized :
      ‖((event.state :
        EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) : BurnolL2)‖ =
        1 := event.normalized
  calc
    ‖pairedMellinTranslationCharacter coordinate
        (Real.log stageZeroSonineQ)‖ =
      ‖pairedMellinTranslationCharacter coordinate
          (Real.log stageZeroSonineQ) •
        (((event.state :
          EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
            BurnolL2))‖ := by
        rw [norm_smul, ambientNormalized, mul_one]
    _ = ‖((burnolPhysicalActionCompression event.state :
          EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
            BurnolL2)‖ := congrArg norm ambientEigen.symm
    _ ≤ ‖event.state‖ := contraction
    _ = 1 := event.normalized

theorem NormalizedPhysicalKernelEventAt.criticalLine
    {coordinate : ℂ} (event : NormalizedPhysicalKernelEventAt coordinate) :
    coordinate.re = 1 / 2 :=
  pairedMellinTranslationCharacter_rigidity coordinate
    (Real.log stageZeroSonineQ) burnolPhysicalAction_shift_ne_zero
    event.character_real event.character_norm_le_one

structure SpectralActualitySettlementAt
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    (event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial) : Type where
  private mk ::
  claim : SpectralActualityClaimAt event
  claim_eq : claim = SpectralActualityClaimAt.generate event
  kernelEvent : NormalizedPhysicalKernelEventAt coordinate
  criticalLine : coordinate.re = 1 / 2

def SpectralActualitySettlementAt.ofKernelEvent
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    (event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial)
    (kernelEvent : NormalizedPhysicalKernelEventAt coordinate) :
    SpectralActualitySettlementAt event where
  claim := SpectralActualityClaimAt.generate event
  claim_eq := rfl
  kernelEvent := kernelEvent
  criticalLine := kernelEvent.criticalLine

theorem settlement_nonempty_of_characteristicLanding
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    (event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial)
    (landing : Nonempty (NormalizedPhysicalKernelEventAt coordinate)) :
    Nonempty (SpectralActualitySettlementAt event) := by
  rcases landing with ⟨kernelEvent⟩
  exact ⟨SpectralActualitySettlementAt.ofKernelEvent event kernelEvent⟩

theorem SpectralActualitySettlementAt.forces_criticalLine
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    {event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial}
    (settlement : SpectralActualitySettlementAt event) :
    coordinate.re = 1 / 2 :=
  settlement.criticalLine

end
end SpectralActuality
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
