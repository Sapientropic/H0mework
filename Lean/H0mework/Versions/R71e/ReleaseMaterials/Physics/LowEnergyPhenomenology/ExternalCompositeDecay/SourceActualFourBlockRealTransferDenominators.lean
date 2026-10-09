import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferCanonicalSource
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDualPolynomial
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferScalar
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockImaginaryPoint

set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorPairedSourceFrame

abbrev DenominatorIndex := Fin 10 ⊕ (Fin 6 ⊕ Unit)

def sourceDenominator : DenominatorIndex → ℂ → ℂ
  | .inl i,x => MixedSpectatorCanonical79Data.denominator x 0 i
  | .inr (.inl i),x => MixedSpectatorDual24Data.denominator x 0 i
  | .inr (.inr _),x => MixedSpectatorScalar61Exchange.denominator (worldTransfer x 0)

theorem actual_denominator_analytic (z : ℂ) (i : DenominatorIndex) :
    AnalyticAt ℂ (sourceDenominator i) z := by
  rcases i with i | (i | i)
  · exact actual_canonical_denominator_analytic z i
  · exact actual_dual_denominator_analytic z i
  · exact actual_scalar_denominator_analytic z

theorem actual_denominator_imaginary_nonzero (i : DenominatorIndex) :
    sourceDenominator i Complex.I ≠ 0 := by
  rcases i with i | (i | i)
  · have h := ActualFourBlockElastic.actual_imaginary_canonical_regular i
    simpa only [sourceDenominator,ActualFourBlockElastic.zero_signed_radius,Complex.ofReal_zero] using h
  · have h := ActualFourBlockElastic.actual_imaginary_dual_regular i
    simpa only [sourceDenominator,ActualFourBlockElastic.zero_signed_radius,Complex.ofReal_zero] using h
  · exact ActualFourBlockElastic.actual_imaginary_scalar_regular

theorem actual_denominators_regular (x : ℂ)
    (h : ∀i : DenominatorIndex,sourceDenominator i x ≠ 0) :
    MixedSpectatorCanonical79Exchange.RegularMomentum x 0 ∧
      MixedSpectatorDual24Exchange.RegularMomentum x 0 ∧
      MixedSpectatorScalar61Exchange.denominator (worldTransfer x 0) ≠ 0 := by
  refine ⟨?_,?_,h (.inr (.inr ()))⟩
  · intro i
    rw [ActualFourBlockElastic.zero_signed_radius,Complex.ofReal_zero]
    exact h (.inl i)
  · intro i
    rw [ActualFourBlockElastic.zero_signed_radius,Complex.ofReal_zero]
    exact h (.inr (.inl i))

end LowEnergy.ActualFourBlockRealTransfer
