import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRFiniteOrderPrice.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRSourcePrice.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe uStart uTerminal uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRFiniteOrderPrice
open RootInquiryCompletion
open CenteredGram.IntegralGraphJointAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
namespace M
export BornRSealedMethodHistory (actualStock physical_step finite_source_method_history)
end M
namespace NPrice
export BornRSourcePrice (sourceInput actual_input_source actualPriceAnswer actual_kernel_action actual_source_price_method)
end NPrice
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "c"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m"=>generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "R"=>burnolDirectRightResolventCLM
local notation "current"=>M.actualStock observation nontrivial half depth ordinal
local notation "Z"=>OriginalKLossFreeAdjointMaterial.installedKernelCombo observation nontrivial half
local notation "aJ"=>OriginalKCrossParameterRAdjointSource.SharedOutsideSource.jQuarterAmplitude c
local notation "aH"=>OriginalKDirectRCofinalOutsideVolterraSource.hQuarterAmplitude c

def increment (update:Nat) : BurnolL2 := (current (update+1)).1.1-(current update).1.1

def countedIncrement (update cutoff:Nat) : BurnolL2 :=
 DualSource.source cutoff (increment observation nontrivial half depth ordinal update)

theorem actual_power (update steps:Nat) :
 (current (update+steps)).1.1=((R c)^steps) (current update).1.1 := by
 induction steps with
 | zero=>simp only [Nat.add_zero,pow_zero,one_apply_eq_self]
 | succ steps previous=>
  rw [Nat.add_succ,M.physical_step,previous,pow_succ',mul_apply_eq_comp]

theorem actual_increment_power (update steps:Nat) :
 ((R c)^steps) (increment observation nontrivial half depth ordinal update)=
 increment observation nontrivial half depth ordinal (update+steps) := by
 unfold increment
 rw [map_sub,←actual_power observation nontrivial half depth ordinal (update+1) steps,
  ←actual_power observation nontrivial half depth ordinal update steps]
 exact congrArg (fun index:Nat=>(current index).1.1-(current (update+steps)).1.1)
  (by omega:(update+1)+steps=(update+steps)+1)

theorem actual_counted_increment_power (update cutoff steps:Nat) :
 ((R c)^steps) (countedIncrement observation nontrivial half depth ordinal update cutoff)=
 countedIncrement observation nontrivial half depth ordinal (update+steps) cutoff := by
 unfold countedIncrement
 rw [R_power_dual,actual_increment_power]

theorem actual_bill_source (update cutoff:Nat) :
 (NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).bill=
 Prior.generatedBill observation nontrivial half cutoff (current update).1.1 := by
 change Prior.generatedBill observation nontrivial half cutoff
  (NPrice.sourceInput observation nontrivial half depth ordinal update)=_
 unfold NPrice.sourceInput
 rw [NPrice.actual_input_source]

theorem actual_original_channel (kernel:BurnolL2) (update cutoff:Nat) :
 inner ℂ kernel (countedIncrement observation nontrivial half depth ordinal update cutoff)=
  inner ℂ (Prior.counted cutoff kernel) (current (update+1)).1.1-
   inner ℂ (Prior.counted cutoff kernel) (current update).1.1 := by
 unfold countedIncrement increment
 rw [←CountingDual.source_pairing,inner_sub_right]
 rfl

theorem actual_K_read (update cutoff:Nat) :
 inner ℂ (Prior.originalK observation nontrivial half)
  (countedIncrement observation nontrivial half depth ordinal update cutoff)=
  (NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).originalKDelta := by
 rw [actual_original_channel]
 have read:=(NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).K_read
 rw [NPrice.actual_input_source] at read
 exact read

theorem actual_FK_read (update cutoff:Nat) :
 inner ℂ (Prior.originalFK observation nontrivial half)
  (countedIncrement observation nontrivial half depth ordinal update cutoff)=
  (NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).originalFKDelta := by
 rw [actual_original_channel]
 have read:=(NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).FK_read
 rw [NPrice.actual_input_source] at read
 exact read

theorem actual_terminal_price (update cutoff:Nat) :
 inner ℂ Z (countedIncrement observation nontrivial half depth ordinal (update+m) cutoff)=
  OldPrices.actualPaFee observation half (countedIncrement observation nontrivial half depth ordinal update cutoff)+
   (NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).bill+
    Prices.actualOutsidePrice observation half (countedIncrement observation nontrivial half depth ordinal update cutoff) := by
 have feedback:=full_order_feedback observation nontrivial half cutoff (current update).1.1
 have sameIncrement:R c (current update).1.1-(current update).1.1=
  increment observation nontrivial half depth ordinal update := by
  unfold increment
  rw [M.physical_step]
 rw [sameIncrement] at feedback
 change inner ℂ Z (((R c)^m) (countedIncrement observation nontrivial half depth ordinal update cutoff))=_ at feedback
 rw [actual_counted_increment_power,←actual_bill_source] at feedback
 exact feedback

theorem actual_two_head_feedback (update cutoff:Nat) :
 star aJ*(NPrice.actualPriceAnswer observation nontrivial half depth ordinal (update+m) cutoff).originalKDelta-
  star aH*(NPrice.actualPriceAnswer observation nontrivial half depth ordinal (update+m) cutoff).originalFKDelta=
  OldPrices.actualPaFee observation half (countedIncrement observation nontrivial half depth ordinal update cutoff)+
   (NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).bill+
    Prices.actualOutsidePrice observation half (countedIncrement observation nontrivial half depth ordinal update cutoff) := by
 have feedback:=actual_terminal_price observation nontrivial half depth ordinal update cutoff
 rw [original_heads,actual_K_read,actual_FK_read] at feedback
 exact feedback

structure FiniteOrderPriceReceipt {Start:Sort uStart} {Terminal:Sort uTerminal} {History:Sort uHistory}
 (update cutoff:Nat) where
 source_increment:BurnolL2
 source_literal:source_increment=countedIncrement observation nontrivial half depth ordinal update cutoff
 terminal_increment:BurnolL2
 terminal_literal:terminal_increment=countedIncrement observation nontrivial half depth ordinal (update+m) cutoff
 actual_action:((R c)^m) source_increment=terminal_increment
 K_read:type_of% (actual_K_read observation nontrivial half depth ordinal (update+m) cutoff)
 FK_read:type_of% (actual_FK_read observation nontrivial half depth ordinal (update+m) cutoff)
 complete_feedback:type_of% (actual_two_head_feedback observation nontrivial half depth ordinal update cutoff)
 original_receipt:type_of% (installedOriginalKReceiptAt observation nontrivial half.down)
 source_method:Start
 terminal_method:Terminal
 actual_history:History

private def assemble_feedback {Start:Sort uStart} {Terminal:Sort uTerminal} {History:Sort uHistory}
 (update cutoff:Nat) (source:Start) (terminal:Terminal) (history:History) :
 FiniteOrderPriceReceipt (Start:=Start) (Terminal:=Terminal) (History:=History)
  observation nontrivial half depth ordinal update cutoff where
 source_increment:=countedIncrement observation nontrivial half depth ordinal update cutoff
 source_literal:=rfl
 terminal_increment:=countedIncrement observation nontrivial half depth ordinal (update+m) cutoff
 terminal_literal:=rfl
 actual_action:=actual_counted_increment_power observation nontrivial half depth ordinal update cutoff m
 K_read:=actual_K_read observation nontrivial half depth ordinal (update+m) cutoff
 FK_read:=actual_FK_read observation nontrivial half depth ordinal (update+m) cutoff
 complete_feedback:=actual_two_head_feedback observation nontrivial half depth ordinal update cutoff
 original_receipt:=installedOriginalKReceiptAt observation nontrivial half.down
 source_method:=source
 terminal_method:=terminal
 actual_history:=history

def actual_source_finite_order_price_feedback (update cutoff:Nat) :=
 assemble_feedback observation nontrivial half depth ordinal update cutoff
  (NPrice.actual_source_price_method observation nontrivial half depth ordinal update cutoff)
  (NPrice.actual_source_price_method observation nontrivial half depth ordinal (update+m) cutoff)
  (M.finite_source_method_history observation nontrivial half depth ordinal (update+m))

end CountedPaInitial.BornRFiniteOrderPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
