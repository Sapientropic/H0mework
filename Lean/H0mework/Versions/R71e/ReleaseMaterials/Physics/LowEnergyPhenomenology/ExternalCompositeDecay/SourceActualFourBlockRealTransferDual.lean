import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDualRead
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDualPolynomial
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockImaginaryPoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorDual24Exchange
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open Set
open scoped BigOperators

private theorem inverse_meromorphic (a b : Fin 24) (z : ℂ) :
    MeromorphicAt (fun x => MixedSpectatorDual24Data.axialInverse x 0 a b) z := by
  have h : (fun x => MixedSpectatorDual24Data.axialInverse x 0 a b) =
      (fun x => dualRead x 0 a b) := funext (fun x => actual_dual_read x 0 a b)
  rw [h]
  unfold dualRead
  cases hs : dualIndex a b with
  | none => simpa only [hs] using (MeromorphicAt.const ((0 : ℂ)/(lapse : ℂ)) z)
  | some p =>
      rcases p with ⟨i,d⟩
      apply MeromorphicAt.div
      · apply MeromorphicAt.div
        · exact (actual_dual_numerator_analytic z i).meromorphicAt
        · exact (actual_dual_denominator_analytic z d).meromorphicAt
      · exact MeromorphicAt.const (lapse : ℂ) z

private theorem inverse_analytic_I (a b : Fin 24) :
    AnalyticAt ℂ (fun x => MixedSpectatorDual24Data.axialInverse x 0 a b) Complex.I := by
  have h : (fun x => MixedSpectatorDual24Data.axialInverse x 0 a b) =
      (fun x => dualRead x 0 a b) := funext (fun x => actual_dual_read x 0 a b)
  rw [h]
  unfold dualRead
  cases hs : dualIndex a b with
  | none => simpa only [hs] using (analyticAt_const (v := (0 : ℂ)/(lapse : ℂ)))
  | some p =>
      rcases p with ⟨i,d⟩
      have hd : MixedSpectatorDual24Data.denominator Complex.I 0 d ≠ 0 := by
        have h := ActualFourBlockElastic.actual_imaginary_dual_regular d
        simpa only [ActualFourBlockElastic.zero_signed_radius,Complex.ofReal_zero] using h
      simp only [div_eq_mul_inv]
      apply AnalyticAt.mul
      · apply AnalyticAt.mul
        · exact actual_dual_numerator_analytic Complex.I i
        · exact (actual_dual_denominator_analytic Complex.I d).inv hd
      · exact analyticAt_const

theorem actual_dual_coefficient_meromorphic (a b : Fin 97) :
    MeromorphicOn (fun x => dualCoefficient x 0 a b) univ := by
  intro z _
  unfold dualCoefficient
  simp only [ActualFourBlockElastic.zero_signed_radius,Complex.ofReal_zero]
  apply MeromorphicAt.fun_sum
  intro i _
  apply MeromorphicAt.fun_sum
  intro j _
  exact ((MeromorphicAt.const (worldSourceMap 0 i a) z).mul
    (inverse_meromorphic i j z)).mul (MeromorphicAt.const (worldSourceMap 0 j b) z)

theorem actual_dual_coefficient_analytic_I (a b : Fin 97) :
    AnalyticAt ℂ (fun x => dualCoefficient x 0 a b) Complex.I := by
  unfold dualCoefficient
  simp only [ActualFourBlockElastic.zero_signed_radius,Complex.ofReal_zero]
  apply Finset.analyticAt_fun_sum
  intro i _
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (analyticAt_const.mul (inverse_analytic_I i j)).mul analyticAt_const

end LowEnergy.ActualFourBlockRealTransfer
