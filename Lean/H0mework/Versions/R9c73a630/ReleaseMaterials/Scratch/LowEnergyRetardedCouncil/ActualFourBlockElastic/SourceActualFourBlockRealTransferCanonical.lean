import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferCanonicalSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferCanonicalNumerator
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferCanonicalInverseSelection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorCanonical79Data MixedSpectatorCanonical79Exchange
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators

private theorem selected_inverse_meromorphic (z : ℂ) (entry : Option (Fin 526 × Fin 10)) :
    MeromorphicAt (fun x => selectedCanonicalInverse x entry) z := by
  cases entry with
  | none => exact analyticAt_const.meromorphicAt
  | some indices =>
    exact (actual_canonical_numerator_analytic z indices.1).meromorphicAt.div
      (actual_canonical_denominator_analytic z indices.2).meromorphicAt

private theorem selected_inverse_analytic_I (entry : Option (Fin 526 × Fin 10)) :
    AnalyticAt ℂ (fun x => selectedCanonicalInverse x entry) Complex.I := by
  cases entry with
  | none => exact analyticAt_const
  | some indices =>
    apply (actual_canonical_numerator_analytic Complex.I indices.1).div
      (actual_canonical_denominator_analytic Complex.I indices.2)
    simpa only [ActualFourBlockElastic.zero_signed_radius, Complex.ofReal_zero] using
      ActualFourBlockElastic.actual_imaginary_canonical_regular indices.2

theorem actual_canonical_inverse_meromorphic (z : ℂ) (a b : Fin 79) :
    MeromorphicAt (fun x => axialInverse x 0 a b) z := by
  simp_rw [actual_canonical_inverse_selection]
  exact ((MeromorphicAt.const _ _).mul (selected_inverse_meromorphic z _)).mul
    (MeromorphicAt.const _ _) |>.div (MeromorphicAt.const _ _)

theorem actual_canonical_inverse_analytic_I (a b : Fin 79) :
    AnalyticAt ℂ (fun x => axialInverse x 0 a b) Complex.I := by
  simp_rw [actual_canonical_inverse_selection]
  exact (analyticAt_const.mul (selected_inverse_analytic_I _)).mul analyticAt_const
    |>.div_const

theorem actual_canonical_coefficient_meromorphic (a b : Fin 97) :
    MeromorphicOn (fun x => canonicalCoefficient x 0 a b) Set.univ := by
  intro z _
  unfold canonicalCoefficient
  simp only [ActualFourBlockElastic.zero_signed_radius, Complex.ofReal_zero]
  apply MeromorphicAt.fun_sum
  intro i _
  apply MeromorphicAt.fun_sum
  intro j _
  exact ((actual_canonical_world_source_analytic true z i a).meromorphicAt.mul
    (actual_canonical_inverse_meromorphic z i j)).mul
      (actual_canonical_world_source_analytic false z j b).meromorphicAt

theorem actual_canonical_coefficient_analytic_I (a b : Fin 97) :
    AnalyticAt ℂ (fun x => canonicalCoefficient x 0 a b) Complex.I := by
  unfold canonicalCoefficient
  simp only [ActualFourBlockElastic.zero_signed_radius, Complex.ofReal_zero]
  apply Finset.analyticAt_fun_sum
  intro i _
  apply Finset.analyticAt_fun_sum
  intro j _
  exact ((actual_canonical_world_source_analytic true Complex.I i a).mul
    (actual_canonical_inverse_analytic_I i j)).mul
      (actual_canonical_world_source_analytic false Complex.I j b)

end LowEnergy.ActualFourBlockRealTransfer
