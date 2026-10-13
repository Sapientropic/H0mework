import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.DivisorPrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory
open scoped InnerProductSpace BigOperators ArithmeticFunction

def finiteResponsePrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  -(2:ℂ)*(Real.exp (-h/2):ℂ)*∑ n ∈ burnolCenteredMobiusCutoffFinset 4,
    if n=1 then 0 else (ArithmeticFunction.moebius (n:ℕ):ℂ)*responseEndpointPrice coordinate h n

-- No response field price remains: the complete literal finite word reads b endpoints and b moments.
theorem original_response_complete_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (Paid.pairedColumn coordinate h) (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))=
      finiteResponsePrice coordinate h := by
  rw [original_response_mu_word coordinate h nonnegative bounded]
  unfold finiteResponsePrice
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases unit : n=1
  · subst n
    have same : F.fullPullback 1 (wholeContactResponse coordinate)=wholeContactResponse coordinate := by
      unfold F.fullPullback
      simp only [PNat.val_ofNat,Nat.cast_one,Real.log_one,zero_div,Real.exp_zero,Complex.ofReal_one,one_smul,neg_zero,
        burnolMultiplicativeDilation_zero,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
    rw [same,unit_response_column_zero coordinate h nonnegative,if_pos rfl,mul_zero,mul_zero]
  · rw [original_response_divisor_price coordinate h nonnegative bounded n unit,if_neg unit]
    unfold FiniteMobiusResolventFlux.coefficient
    have nonzero : ((n:ℕ):ℂ)≠0 := by exact_mod_cast n.ne_zero
    field_simp

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
