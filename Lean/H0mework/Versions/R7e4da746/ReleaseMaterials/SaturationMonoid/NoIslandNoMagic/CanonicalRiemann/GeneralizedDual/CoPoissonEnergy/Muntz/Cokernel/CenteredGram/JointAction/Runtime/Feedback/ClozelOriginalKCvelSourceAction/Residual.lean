import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "T2" => burnolMeanZeroTruncatedFourierSquare
local instance residualComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def actualSourceTail (N : ℕ) : BurnolQuarterMeanZeroCarrier := (T2 ^ N) Response.u

theorem actual_source_stock_complete (N : ℕ) :
    Response.u = actualSourceStock N + actualSourceTail N := by
  have generated := @NormedRing.inverse_one_sub_nth_order' (BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier) ContinuousLinearMap.toNormedRing inferInstance N T2 burnolMeanZeroTruncatedFourierSquare_opNorm_lt_one
  have actual := congrArg (fun action : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier => action Response.eta) generated
  exact actual

theorem actual_source_tail_action (N : ℕ) : actualSourceTail (N+1) = T2 (actualSourceTail N) := by
  simp only [actualSourceTail,pow_succ',mul_apply_eq_comp]

theorem actual_source_tail_bound (N : ℕ) :
    ‖actualSourceTail N‖ ≤ (1/4:ℝ)^N * ‖Response.u‖ := by
  have qnorm : ‖T2‖ ≤ (1/4:ℝ) := by
    apply (ContinuousLinearMap.opNorm_comp_le T T).trans
    have bound := mul_le_mul burnolMeanZeroTruncatedFourier_opNorm_le_half
      burnolMeanZeroTruncatedFourier_opNorm_le_half (norm_nonneg T) (by norm_num : 0 ≤ (1/2:ℝ))
    exact bound.trans_eq (by norm_num)
  cases N with
  | zero => simp [actualSourceTail]
  | succ N =>
    exact ((T2 ^ (N+1)).le_opNorm Response.u).trans
      (mul_le_mul_of_nonneg_right ((norm_pow_le' T2 (Nat.succ_pos N)).trans
        (pow_le_pow_left₀ (norm_nonneg T2) qnorm (N+1))) (norm_nonneg Response.u))

def actualVelocityTail (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  let u := actualStockExtension (actualSourceTail N)
  let v := actualStockExtension (T (actualSourceTail N))
  Kernel.A coordinate • (fourierL2 u - v) + Kernel.beta coordinate • (u - fourierL2 v)

theorem actual_velocity_stock_complete (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    OriginalKBoundarySourceAction.Source.velocity coordinate =
      actualVelocityStock coordinate N + actualVelocityTail coordinate N := by
  have source := actual_source_stock_complete N
  have u := congrArg actualStockExtension source
  have v := congrArg (actualStockExtension.comp T) source
  rw [map_add] at u v
  change Response.wholeU = actualUStock N + actualStockExtension (actualSourceTail N) at u
  change Response.wholeV = actualVStock N + actualStockExtension (T (actualSourceTail N)) at v
  unfold OriginalKBoundarySourceAction.Source.velocity
    actualVelocityStock actualVelocityTail
  dsimp only
  rw [u,v,map_add,map_add]
  module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
