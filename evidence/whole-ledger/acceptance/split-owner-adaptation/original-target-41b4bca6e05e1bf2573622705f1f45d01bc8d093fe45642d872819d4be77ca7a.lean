import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantContactSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
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



elab "paid170TateSupport" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKInsideDebtRAction.Qualification".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKInsideDebtRSource.tate_quarter_four_zero".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

elab "paid170QuarterSplit" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKInsideDebtRAction.Action".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKInsideDebtRSource.reciprocal_four_quarter_split".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

/-- The actual negative and positive source dilation integrals generate the adjoint direction with its true star parameter. -/
theorem actual_original_R_adjoint (z : ℂ) (right : 1/4<z.re) (left value : BurnolL2) :
 inner ℂ left (burnolDirectRightResolvent z value)=inner ℂ (Paid.Rplus (star z) left) value := by
 have starRight : 1/4<(star z).re := by simpa only [Complex.star_def,Complex.conj_re] using right
 unfold burnolDirectRightResolvent Paid.Rplus
 rw [inner_neg_right,inner_neg_left]
 have rightRead:=(innerSL ℂ left).integral_comp_comm
   (burnolDirectRightResolventIntegrand_integrableOn z right value)
 let reverseRead : BurnolL2→L[ℝ]ℂ:=Complex.conjCLE.toContinuousLinearMap.comp
   ((innerSL ℂ value).restrictScalars ℝ)
 have leftRead:=reverseRead.integral_comp_comm (Paid.Rplus_integrable (star z) starRight left)
 change (∫ tau : ℝ in Ioi 0,inner ℂ left (burnolDirectRightResolventIntegrand z value tau))=
   inner ℂ left (∫ tau : ℝ in Ioi 0,burnolDirectRightResolventIntegrand z value tau) at rightRead
 have actualReverse (source : BurnolL2) : reverseRead source=inner ℂ source value :=
   inner_conj_symm source value
 simp only [actualReverse] at leftRead
 rw [←rightRead,←leftRead]
 congr 1
 apply setIntegral_congr_fun measurableSet_Ioi
 intro tau _
 unfold burnolDirectRightResolventIntegrand Paid.RplusIntegrand
 dsimp only
 rw [inner_smul_right,inner_smul_left]
 have moved:=(burnolMultiplicativeDilation (tau/2)).inner_map_eq_flip left value
 rw [←burnolMultiplicativeDilation_neg_eq_symm] at moved
 rw [show -(tau/2)= -tau/2 by ring] at moved
 rw [moved]
 congr 1
 unfold positiveMellinQuarterRightResolventWeight
 rw [←Complex.exp_conj]
 congr 1
 simp
 exact Or.inl (by rw [map_ofNat])


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
