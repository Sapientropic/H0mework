import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferCanonical
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators

private theorem selected_inverse_analytic (z : ℂ)
    (h : ∀i : Fin 10, MixedSpectatorCanonical79Data.denominator z 0 i ≠ 0)
    (entry : Option (Fin 526 × Fin 10)) :
    AnalyticAt ℂ (fun x => selectedCanonicalInverse x entry) z := by
  cases entry with
  | none => exact analyticAt_const
  | some indices =>
    exact (actual_canonical_numerator_analytic z indices.1).div
      (actual_canonical_denominator_analytic z indices.2) (h indices.2)

theorem actual_canonical_inverse_analytic (z : ℂ)
    (h : ∀i : Fin 10, MixedSpectatorCanonical79Data.denominator z 0 i ≠ 0)
    (a b : Fin 79) :
    AnalyticAt ℂ (fun x => MixedSpectatorCanonical79Data.axialInverse x 0 a b) z := by
  simp_rw [actual_canonical_inverse_selection]
  exact (analyticAt_const.mul (selected_inverse_analytic z h _)).mul analyticAt_const
    |>.div_const

theorem actual_canonical_coefficient_analytic (z : ℂ)
    (h : MixedSpectatorCanonical79Exchange.RegularMomentum z 0) (a b : Fin 97) :
    AnalyticAt ℂ (fun x => MixedSpectatorCanonical79Exchange.canonicalCoefficient x 0 a b) z := by
  have hd (i : Fin 10) : MixedSpectatorCanonical79Data.denominator z 0 i ≠ 0 := by
    simpa only [ActualFourBlockElastic.zero_signed_radius, Complex.ofReal_zero] using h i
  unfold MixedSpectatorCanonical79Exchange.canonicalCoefficient
  simp only [ActualFourBlockElastic.zero_signed_radius, Complex.ofReal_zero]
  apply Finset.analyticAt_fun_sum
  intro i _
  apply Finset.analyticAt_fun_sum
  intro j _
  exact ((actual_canonical_world_source_analytic true z i a).mul
    (actual_canonical_inverse_analytic z hd i j)).mul
      (actual_canonical_world_source_analytic false z j b)

theorem actual_dual_inverse_analytic (z : ℂ)
    (h : ∀i : Fin 6, MixedSpectatorDual24Data.denominator z 0 i ≠ 0) (a b : Fin 24) :
    AnalyticAt ℂ (fun x => MixedSpectatorDual24Data.axialInverse x 0 a b) z := by
  have he : (fun x => MixedSpectatorDual24Data.axialInverse x 0 a b) =
      (fun x => dualRead x 0 a b) := funext (fun x => actual_dual_read x 0 a b)
  rw [he]
  unfold dualRead
  cases hs : dualIndex a b with
  | none => simpa only [hs] using (analyticAt_const (v := (0 : ℂ)/(lapse : ℂ)))
  | some p =>
    rcases p with ⟨i,d⟩
    simp only [div_eq_mul_inv]
    apply AnalyticAt.mul
    · apply AnalyticAt.mul
      · exact actual_dual_numerator_analytic z i
      · exact (actual_dual_denominator_analytic z d).inv (h d)
    · exact analyticAt_const

theorem actual_dual_coefficient_analytic (z : ℂ)
    (h : MixedSpectatorDual24Exchange.RegularMomentum z 0) (a b : Fin 97) :
    AnalyticAt ℂ (fun x => MixedSpectatorDual24Exchange.dualCoefficient x 0 a b) z := by
  have hd (i : Fin 6) : MixedSpectatorDual24Data.denominator z 0 i ≠ 0 := by
    simpa only [ActualFourBlockElastic.zero_signed_radius, Complex.ofReal_zero] using h i
  unfold MixedSpectatorDual24Exchange.dualCoefficient
  simp only [ActualFourBlockElastic.zero_signed_radius, Complex.ofReal_zero]
  apply Finset.analyticAt_fun_sum
  intro i _
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (analyticAt_const.mul (actual_dual_inverse_analytic z hd i j)).mul analyticAt_const

end LowEnergy.ActualFourBlockRealTransfer
