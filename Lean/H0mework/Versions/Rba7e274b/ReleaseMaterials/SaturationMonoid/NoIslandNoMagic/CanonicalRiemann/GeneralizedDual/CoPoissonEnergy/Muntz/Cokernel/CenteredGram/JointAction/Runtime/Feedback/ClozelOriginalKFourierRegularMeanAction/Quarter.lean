import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierRegularMeanAction.Source
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierRegularMeanAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- Actual R quarter field is constant, so the source mean-zero column pays its own R price. -/
theorem actual_mean_zero_column_R_price (h : ℝ) (column : BurnolQuarterMeanZeroCarrier) :
 inner ℂ (burnolQuarterZeroExtension (column : BurnolQuarterIntervalL2))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt
       (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=0 := by
 have read:=(burnolRadiusRestriction q).adjoint_inner_left
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt
       (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))
   (column : BurnolQuarterIntervalL2)
 change inner ℂ (burnolQuarterZeroExtension (column : BurnolQuarterIntervalL2)) _=
   inner ℂ (column : BurnolQuarterIntervalL2) (burnolRadiusRestriction q _) at read
 rw [read,OriginalKGapMeanRSourceAction.actual_two_mean_debt_quarter_R_field,
   inner_smul_right]
 have zero : inner ℂ (intervalConstant q) (column : BurnolQuarterIntervalL2)=0 :=
   (Submodule.mem_orthogonal _ _).mp column.property _ (Submodule.mem_span_singleton_self _)
 rw [inner_eq_zero_symm.mp zero,mul_zero]

theorem actual_original_UV_R_prices (h : ℝ) :
 inner ℂ OriginalRieszSource.Response.wholeU
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt
       (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=0 ∧
 inner ℂ OriginalRieszSource.Response.wholeV
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt
       (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=0 :=
 ⟨actual_mean_zero_column_R_price observation nontrivial half h OriginalRieszSource.Response.u,
  actual_mean_zero_column_R_price observation nontrivial half h OriginalRieszSource.Response.v⟩

/-- Resonant Fourier compatibility preserves the source A/beta matrix and generates its actual coupling. -/
theorem actual_Fourier_regular_mean_coupling (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=(OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 star (OriginalRieszSource.Kernel.A coordinate)*
   inner ℂ (fourierL2 OriginalRieszSource.Response.wholeV) acted-
 star (OriginalRieszSource.Kernel.beta coordinate)*
   inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU) acted+
 star (2*(star coordinate.value-1/2)*OriginalRieszSource.Kernel.beta coordinate)*
   inner ℂ (fourierL2 (OriginalRieszFiniteSource.fourierPrimitive coordinate)) acted=
 (2:ℂ)*inner ℂ (fourierL2 (OriginalKSourceBalance.correctedField coordinate)) material := by
 dsimp only
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=(OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 have source:=actual_Fourier_regular_R_source observation nontrivial half material
 have prices:=actual_original_UV_R_prices observation nontrivial half h
 unfold OriginalKSourceBalance.regularSource at source
 rw [map_sub,map_add,map_smul,map_smul,map_smul,map_sub,map_sub,
   fourierL2_fourierL2,fourierL2_fourierL2,
   OriginalRieszSource.Response.wholeU_reflection,OriginalRieszSource.Response.wholeV_reflection] at source
 simp only [inner_sub_left,inner_add_left,inner_smul_left,starRingEnd_apply] at source
 rw [prices.1,prices.2] at source
 change _=_ at source
 linear_combination -source



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierRegularMeanAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
