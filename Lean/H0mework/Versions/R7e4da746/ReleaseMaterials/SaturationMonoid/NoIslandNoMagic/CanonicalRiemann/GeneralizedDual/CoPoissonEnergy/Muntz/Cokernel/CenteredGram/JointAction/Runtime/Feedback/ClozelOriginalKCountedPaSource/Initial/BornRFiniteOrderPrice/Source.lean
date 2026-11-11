import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRSourcePrice.Source
import H0mework.Versions.R7e4da746.Arithmetic.RiemannBandResponse.Algebra

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRFiniteOrderPrice
open Complex MeasureTheory Set
open CenteredGram.IntegralGraphJointAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace BigOperators
namespace Prior
export BornRSourcePrice (originalK originalFK counted generatedBill price_generated_bill)
end Prior
namespace UnitSource
export OriginalKFiniteOrderRelease.UnitPowerSource (fulladjointPowerZ actual_full_power_read)
end UnitSource
namespace Prices
export OriginalKFiniteOrderRelease.UnitPowerJordanMaterialConsumer
 (actualQPrice actualOutsidePrice completePrice source_prices_generated complete_price_generated)
end Prices
namespace OldPrices
export OriginalKFiniteOrderRelease.UnitPowerMaterialConsumer (actualPaFee completePrice)
end OldPrices
open private source_complete_price from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerMaterialConsumer
open private combo_anchor_from from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKLossFreeAdjointMaterial.Consumer
local notation "R"=>burnolDirectRightResolventCLM

theorem R_channel (c:BurnolCompletedMellinCoordinate) (direction radius:ℝ) (value:BurnolL2) :
 R c (ContinuousChannels.channel direction radius value)=
  ContinuousChannels.channel direction radius (R c value) := by
 unfold ContinuousChannels.channel
 rw [map_smul]
 exact congrArg (fun field:BurnolL2=>(Real.sqrt radius:ℂ)⁻¹ • field)
  (burnolDirectRightResolvent_dilation (c.value/2) (direction*Real.log radius) value)

-- This keeps the original finite sum and its entire (0,N] Bochner normalization.
theorem R_dual_source (c:BurnolCompletedMellinCoordinate) (N:Nat) (value:BurnolL2) :
 R c (DualSource.source N value)=DualSource.source N (R c value) := by
 unfold DualSource.source
 rw [map_sub,map_sum,←(R c).integral_comp_comm (ContinuousChannels.channel_integrable 1 N value)]
 simp_rw [R_channel]

theorem R_dual_commute (c:BurnolCompletedMellinCoordinate) (N:Nat) :
 Commute (R c) (CountingDual.sourceCLM N).adjoint := by
 apply ContinuousLinearMap.ext
 intro value
 change R c ((CountingDual.sourceCLM N).adjoint value)=
  (CountingDual.sourceCLM N).adjoint (R c value)
 rw [←CountingDual.dual_eq_adjoint,←CountingDual.dual_eq_adjoint]
 exact R_dual_source c N value

theorem R_power_dual (c:BurnolCompletedMellinCoordinate) (N steps:Nat) (value:BurnolL2) :
 ((R c)^steps) (DualSource.source N value)=DualSource.source N (((R c)^steps) value) := by
 induction steps with
 | zero=>simp only [pow_zero,one_apply_eq_self]
 | succ steps previous=>
  rw [pow_succ',mul_apply_eq_comp,previous,R_dual_source]
  rfl

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m"=>generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "Z"=>OriginalKLossFreeAdjointMaterial.installedKernelCombo observation nontrivial half
local notation "aJ"=>OriginalKCrossParameterRAdjointSource.SharedOutsideSource.jQuarterAmplitude c
local notation "aH"=>OriginalKDirectRCofinalOutsideVolterraSource.hQuarterAmplitude c

private theorem installed_combo_anchor :
 Z=OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c := by
 simpa only [OriginalKCombCofinalTwoDirection.coordinate,originalKCoordinate,
  burnolDivisionZeroCompletedMellinCoordinate] using
  combo_anchor_from observation nontrivial half
   (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)

theorem original_heads (value:BurnolL2) :
 inner ℂ Z value=star aJ*inner ℂ (Prior.originalK observation nontrivial half) value-
  star aH*inner ℂ (Prior.originalFK observation nontrivial half) value := by
 simp only [OriginalKLossFreeAdjointMaterial.installedKernelCombo,Prior.originalK,Prior.originalFK,
  BornRSourcePrice.receipt,inner_sub_left,inner_smul_left,starRingEnd_apply,
  OriginalKCombCofinalTwoDirection.coordinate,originalKCoordinate,
  burnolDivisionZeroCompletedMellinCoordinate]

-- The old terminal consumer is forall L2; no old D occurrence or physical gap is used.
theorem original_power_complete (value:BurnolL2) :
 inner ℂ Z (((R c)^m) value)=Prices.completePrice observation half value := by
 have fullRead:=UnitSource.actual_full_power_read observation half value
 have complete:=source_complete_price observation nontrivial half value
 change inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
  (((R c)^m) value)=_ at fullRead complete
 have generated:=Prices.complete_price_generated observation nontrivial half value
 have headPrice:=fullRead.symm.trans (complete.trans generated)
 calc
  _=inner ℂ (UnitSource.fulladjointPowerZ observation half) value := by
   rw [installed_combo_anchor observation nontrivial half]
   exact fullRead
  _=Prices.completePrice observation half value:=headPrice

theorem counted_Q_bill (N:Nat) (value:BurnolL2) :
 Prices.actualQPrice observation half (DualSource.source N (R c value-value))=
  Prior.generatedBill observation nontrivial half N value := by
 calc
  _=inner ℂ (FiniteForcing.source N (OriginalKFiniteOrderRelease.UnitPowerJordanSource.sourceQ observation half))
    (R c value-value) := (CountingDual.source_pairing N _ _).symm
  _=CofinalQSource.priceCLM observation half N (R c value)-
    CofinalQSource.priceCLM observation half N value := by
   rw [inner_sub_right]
   rfl
  _=Prior.generatedBill observation nontrivial half N value := by
   simpa only [OriginalKCombCofinalTwoDirection.coordinate,originalKCoordinate,
    burnolDivisionZeroCompletedMellinCoordinate] using
    Prior.price_generated_bill observation nontrivial half N value

theorem full_order_feedback (N:Nat) (value:BurnolL2) :
 inner ℂ Z (((R c)^m) (DualSource.source N (R c value-value)))=
  OldPrices.actualPaFee observation half (DualSource.source N (R c value-value))+
   Prior.generatedBill observation nontrivial half N value+
    Prices.actualOutsidePrice observation half (DualSource.source N (R c value-value)) := by
 rw [original_power_complete,Prices.completePrice,counted_Q_bill]

end CountedPaInitial.BornRFiniteOrderPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
