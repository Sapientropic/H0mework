import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferContact
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferCanonical
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDual
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferReader

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorPairedSourceFrame Set
open scoped BigOperators
attribute [local irreducible] ActualCandidateBra.pairPoint
  MixedSpectatorContactExchange.contactCoefficient
  MixedSpectatorCanonical79Exchange.canonicalCoefficient
  MixedSpectatorDual24Exchange.dualCoefficient

theorem actual_amplitude_meromorphic (dual : Bool) :
    MeromorphicOn (fun x => amplitude x dual) univ := by
  intro z hz
  unfold amplitude
  apply MeromorphicAt.add
  · apply MeromorphicAt.add
    · apply MeromorphicAt.fun_sum
      intro a _
      apply MeromorphicAt.fun_sum
      intro b _
      apply MeromorphicAt.mul
      · apply MeromorphicAt.mul
        · exact MeromorphicAt.const (-1/2 : ℂ) z
        · exact (actual_contact_coefficient_analytic z a b).meromorphicAt
      · exact MeromorphicAt.const (ActualCandidateBra.pairPoint dual a b) z
    · apply MeromorphicAt.fun_sum
      intro a _
      apply MeromorphicAt.fun_sum
      intro b _
      apply MeromorphicAt.mul
      · apply MeromorphicAt.mul
        · exact MeromorphicAt.const (-1/2 : ℂ) z
        · exact actual_canonical_coefficient_meromorphic a b z hz
      · exact MeromorphicAt.const (ActualCandidateBra.pairPoint dual a b) z
  · apply MeromorphicAt.fun_sum
    intro a _
    apply MeromorphicAt.fun_sum
    intro b _
    apply MeromorphicAt.mul
    · apply MeromorphicAt.mul
      · exact MeromorphicAt.const (-1/2 : ℂ) z
      · exact actual_dual_coefficient_meromorphic a b z hz
    · exact MeromorphicAt.const (ActualCandidateBra.pairPoint dual a b) z

theorem actual_amplitude_analytic_I (dual : Bool) :
    AnalyticAt ℂ (fun x => amplitude x dual) Complex.I := by
  unfold amplitude
  apply AnalyticAt.add
  · apply AnalyticAt.add
    · apply Finset.analyticAt_fun_sum
      intro a _
      apply Finset.analyticAt_fun_sum
      intro b _
      apply AnalyticAt.mul
      · apply AnalyticAt.mul
        · exact analyticAt_const
        · exact actual_contact_coefficient_analytic Complex.I a b
      · exact analyticAt_const
    · apply Finset.analyticAt_fun_sum
      intro a _
      apply Finset.analyticAt_fun_sum
      intro b _
      apply AnalyticAt.mul
      · apply AnalyticAt.mul
        · exact analyticAt_const
        · exact actual_canonical_coefficient_analytic_I a b
      · exact analyticAt_const
  · apply Finset.analyticAt_fun_sum
    intro a _
    apply Finset.analyticAt_fun_sum
    intro b _
    apply AnalyticAt.mul
    · apply AnalyticAt.mul
      · exact analyticAt_const
      · exact actual_dual_coefficient_analytic_I a b
    · exact analyticAt_const

end LowEnergy.ActualFourBlockRealTransfer
