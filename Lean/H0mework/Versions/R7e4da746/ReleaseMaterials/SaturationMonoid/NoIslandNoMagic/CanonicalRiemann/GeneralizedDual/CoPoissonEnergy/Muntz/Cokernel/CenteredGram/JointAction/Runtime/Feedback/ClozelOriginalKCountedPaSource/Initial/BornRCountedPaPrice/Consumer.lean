import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCountedPaPrice.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRFiniteOrderPrice.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe uParent
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRCountedPaPrice
open CenteredGram.IntegralGraphJointAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
namespace M
export BornRSealedMethodHistory (actualStock physical_step)
end M
namespace O
export BornRFiniteOrderPrice
 (R_dual_source countedIncrement actual_two_head_feedback actual_source_finite_order_price_feedback)
end O
namespace NPrice
export BornRSourcePrice (actualPriceAnswer)
end NPrice
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "c"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R"=>burnolDirectRightResolventCLM c
local notation "bc"=>burnolPaResolventSourceCoefficient c
local notation "m"=>generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "current"=>M.actualStock observation nontrivial half depth ordinal
local notation "aJ"=>OriginalKCrossParameterRAdjointSource.SharedOutsideSource.jQuarterAmplitude c
local notation "aH"=>OriginalKDirectRCofinalOutsideVolterraSource.hQuarterAmplitude c

def countedStock (update cutoff:Nat):BurnolL2:=DualSource.source cutoff (current update).1.1

theorem counted_stock_next (update cutoff:Nat):
 countedStock observation nontrivial half depth ordinal (update+1) cutoff=
 R (countedStock observation nontrivial half depth ordinal update cutoff):=by
 unfold countedStock
 rw [M.physical_step,O.R_dual_source]

theorem counted_increment (update cutoff:Nat):
 countedStock observation nontrivial half depth ordinal (update+1) cutoff-
 countedStock observation nontrivial half depth ordinal update cutoff=
 O.countedIncrement observation nontrivial half depth ordinal update cutoff:=by
 unfold countedStock O.countedIncrement BornRFiniteOrderPrice.increment
 simp only [CountingDual.dual_eq_adjoint,map_sub]

theorem actual_whole_update (update cutoff:Nat):
 wholeNext observation nontrivial half (countedStock observation nontrivial half depth ordinal update cutoff)=
 countedStock observation nontrivial half depth ordinal (update+1) cutoff:=
 (whole_next_actual observation nontrivial half _).trans
  (counted_stock_next observation nontrivial half depth ordinal update cutoff).symm

theorem actual_pa_update (update cutoff:Nat):
 paNext observation nontrivial half (countedStock observation nontrivial half depth ordinal update cutoff)=
 PA.E (countedStock observation nontrivial half depth ordinal (update+1) cutoff):=by
 rw [counted_stock_next]
 exact pa_next_actual observation nontrivial half _

theorem actual_q_update (update cutoff:Nat):
 qNext observation nontrivial half (countedStock observation nontrivial half depth ordinal update cutoff)=
 PA.Q (countedStock observation nontrivial half depth ordinal (update+1) cutoff):=by
 rw [counted_stock_next]
 exact q_next_actual observation nontrivial half _

theorem actual_outside_update (update cutoff:Nat):
 outsideNext observation half (countedStock observation nontrivial half depth ordinal update cutoff)=
 outside (countedStock observation nontrivial half depth ordinal (update+1) cutoff):=by
 rw [counted_stock_next]
 exact outside_next_actual observation nontrivial half _

theorem actual_tate_update (update cutoff:Nat):
 tateNext observation nontrivial half (countedStock observation nontrivial half depth ordinal update cutoff)=
 burnolTateReciprocalL2 (burnolMobiusSourceL2
  (PA.E (countedStock observation nontrivial half depth ordinal (update+1) cutoff))):=by
 rw [counted_stock_next]
 exact tate_next_actual observation nontrivial half _

theorem actual_coefficient_next (update cutoff:Nat):
 alpha observation half (countedStock observation nontrivial half depth ordinal (update+1) cutoff)=
 bc (correction observation half (countedStock observation nontrivial half depth ordinal update cutoff))+
 alpha observation half (countedStock observation nontrivial half depth ordinal update cutoff)*bc (PA.E (unit observation nontrivial half:BurnolL2))+
 eta observation half (countedStock observation nontrivial half depth ordinal update cutoff)*bc (returning observation half):=by
 have read:=congrArg bc (actual_pa_update observation nontrivial half depth ordinal update cutoff)
 rw [paNext,map_add,map_add,map_smul,map_smul] at read
 exact read.symm

theorem actual_source_fee (update cutoff:Nat):
 sourceFee observation nontrivial half (countedStock observation nontrivial half depth ordinal update cutoff)=
 OldPrices.actualPaFee observation half (O.countedIncrement observation nontrivial half depth ordinal update cutoff):=by
 rw [←counted_increment observation nontrivial half depth ordinal update cutoff,counted_stock_next]
 exact source_fee_actual observation nontrivial half _

theorem actual_counted_Pa_price (update cutoff:Nat):
 star aJ*(NPrice.actualPriceAnswer observation nontrivial half depth ordinal (update+m) cutoff).originalKDelta-
 star aH*(NPrice.actualPriceAnswer observation nontrivial half depth ordinal (update+m) cutoff).originalFKDelta=
 sourceFee observation nontrivial half (countedStock observation nontrivial half depth ordinal update cutoff)+
 (NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).bill+
 BornRFiniteOrderPrice.Prices.actualOutsidePrice observation half
  (O.countedIncrement observation nontrivial half depth ordinal update cutoff):=by
 have feedback:=O.actual_two_head_feedback observation nontrivial half depth ordinal update cutoff
 rw [←actual_source_fee] at feedback
 exact feedback

structure CountedPaPriceReceipt {Parent:Sort uParent} (update cutoff:Nat) where
 source:BurnolL2
 source_literal:source=countedStock observation nontrivial half depth ordinal update cutoff
 qualified:pa source∈burnolCompactCoPoissonClosedRange
 generated_whole:BurnolL2
 generated_literal:generated_whole=wholeNext observation nontrivial half source
 actual_whole:generated_whole=countedStock observation nontrivial half depth ordinal (update+1) cutoff
 Pa_update:type_of% (actual_pa_update observation nontrivial half depth ordinal update cutoff)
 Q_update:type_of% (actual_q_update observation nontrivial half depth ordinal update cutoff)
 outside_update:type_of% (actual_outside_update observation nontrivial half depth ordinal update cutoff)
 Tate_update:type_of% (actual_tate_update observation nontrivial half depth ordinal update cutoff)
 full_invisible:type_of% (eta_inventory observation half source)
 unit_Q:type_of% (pa_response_unit_rank observation nontrivial half source)
 source_coefficient:type_of% (actual_coefficient_next observation nontrivial half depth ordinal update cutoff)
 source_fee:type_of% (actual_source_fee observation nontrivial half depth ordinal update cutoff)
 price_feedback:type_of% (actual_counted_Pa_price observation nontrivial half depth ordinal update cutoff)
 original_order_receipt:Parent

private def assemble_feedback {Parent:Sort uParent} (update cutoff:Nat) (parent:Parent):
 CountedPaPriceReceipt (Parent:=Parent) observation nontrivial half depth ordinal update cutoff where
 source:=countedStock observation nontrivial half depth ordinal update cutoff
 source_literal:=rfl
 qualified:=pa_member _
 generated_whole:=wholeNext observation nontrivial half (countedStock observation nontrivial half depth ordinal update cutoff)
 generated_literal:=rfl
 actual_whole:=actual_whole_update observation nontrivial half depth ordinal update cutoff
 Pa_update:=actual_pa_update observation nontrivial half depth ordinal update cutoff
 Q_update:=actual_q_update observation nontrivial half depth ordinal update cutoff
 outside_update:=actual_outside_update observation nontrivial half depth ordinal update cutoff
 Tate_update:=actual_tate_update observation nontrivial half depth ordinal update cutoff
 full_invisible:=eta_inventory observation half _
 unit_Q:=pa_response_unit_rank observation nontrivial half _
 source_coefficient:=actual_coefficient_next observation nontrivial half depth ordinal update cutoff
 source_fee:=actual_source_fee observation nontrivial half depth ordinal update cutoff
 price_feedback:=actual_counted_Pa_price observation nontrivial half depth ordinal update cutoff
 original_order_receipt:=parent

def actual_source_counted_Pa_price_feedback (update cutoff:Nat):=
 assemble_feedback observation nontrivial half depth ordinal update cutoff
  (O.actual_source_finite_order_price_feedback observation nontrivial half depth ordinal update cutoff)

end CountedPaInitial.BornRCountedPaPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
