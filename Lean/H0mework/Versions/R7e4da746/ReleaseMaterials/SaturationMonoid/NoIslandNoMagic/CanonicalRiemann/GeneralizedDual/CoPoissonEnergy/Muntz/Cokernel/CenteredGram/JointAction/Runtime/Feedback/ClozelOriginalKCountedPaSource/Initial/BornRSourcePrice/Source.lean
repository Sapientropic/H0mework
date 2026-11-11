import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.CofinalQSource.Price
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanMaterialConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRSourcePrice
open Complex RootInquiryCompletion
open CenteredGram.IntegralGraphJointAction
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace BigOperators
namespace J
export OriginalKFiniteOrderRelease.UnitPowerJordanSource
 (sourceStep sourceStep_actual sourceQ source_full_inventory sourceOutside sourceCoefficient logOutsideColumn
  actual_Q_price actual_outside_price)
end J
namespace Full
export OriginalKFiniteOrderRelease.UnitPowerSource (fulladjointPowerZ paPowerField)
end Full
namespace Prices
export OriginalKFiniteOrderRelease.UnitPowerJordanMaterialConsumer (source_prices_generated complete_price_generated)
end Prices
open private combo_anchor_from from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKLossFreeAdjointMaterial.Consumer
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "m"=>generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "r"=>burnolDirectRightResolventCLM c
local notation "aJ"=>OriginalKCrossParameterRAdjointSource.SharedOutsideSource.jQuarterAmplitude c
local notation "aH"=>OriginalKDirectRCofinalOutsideVolterraSource.hQuarterAmplitude c

abbrev receipt := installedOriginalKReceiptAt observation nontrivial half.down
def originalK : BurnolL2 := (receipt observation nontrivial half).kernel
def originalFK : BurnolL2 := fourierL2 (originalK observation nontrivial half)
def KHead : BurnolL2 := ((r^m).adjoint) (originalK observation nontrivial half)
def FKHead : BurnolL2 := ((r^m).adjoint) (originalFK observation nontrivial half)

def counted (N:Nat) (kernel:BurnolL2) : BurnolL2 := FiniteForcing.source N kernel

-- This is the paid native outward source operation, hence the full (R-id) adjoint.
def sourceDelta : BurnolL2→L[ℂ]BurnolL2 := J.sourceStep c-ContinuousLinearMap.id ℂ BurnolL2

theorem source_delta_read (kernel value:BurnolL2) :
 inner ℂ (sourceDelta observation nontrivial half kernel) value=inner ℂ kernel (r value-value) := by
 change inner ℂ (J.sourceStep c kernel-kernel) value=inner ℂ kernel (r value-value)
 rw [inner_sub_left,←J.sourceStep_actual,ContinuousLinearMap.adjoint_inner_left,inner_sub_right]

theorem head_anchor : Full.fulladjointPowerZ observation half=
 aJ • KHead observation nontrivial half-aH • FKHead observation nontrivial half := by
 have installed:=combo_anchor_from observation nontrivial half
  (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
 have acted:=congrArg ((r^m).adjoint) installed
 simpa only [OriginalKLossFreeAdjointMaterial.installedKernelCombo,map_sub,map_smul,
  KHead,FKHead,originalK,originalFK,receipt,Full.fulladjointPowerZ,
  OriginalKCombCofinalTwoDirection.coordinate,originalKCoordinate,
  burnolDivisionZeroCompletedMellinCoordinate] using acted.symm

def KHeadMoment (N:Nat) (value:BurnolL2) : ℂ :=
 inner ℂ (sourceDelta observation nontrivial half (counted N (KHead observation nontrivial half))) value

def FKHeadMoment (N:Nat) (value:BurnolL2) : ℂ :=
 inner ℂ (sourceDelta observation nontrivial half (counted N (FKHead observation nontrivial half))) value

def paFeeMoment (N:Nat) (value:BurnolL2) : ℂ :=
 inner ℂ (sourceDelta observation nontrivial half (counted N (Full.paPowerField observation half:BurnolL2))) value

def outsideMoment (N:Nat) (value:BurnolL2) : ℂ :=
 ∑ k∈Finset.range m,star (J.sourceCoefficient c m k)*
  inner ℂ (sourceDelta observation nontrivial half (counted N (J.logOutsideColumn c k))) value

-- The bill is generated from left source kernels; it never reads a target price.
def generatedBill (N:Nat) (value:BurnolL2) : ℂ :=
 star aJ*KHeadMoment observation nontrivial half N value-
 star aH*FKHeadMoment observation nontrivial half N value-
 paFeeMoment observation nontrivial half N value-outsideMoment observation nontrivial half N value

theorem head_moment (N:Nat) (value:BurnolL2) :
 inner ℂ (sourceDelta observation nontrivial half (counted N (Full.fulladjointPowerZ observation half))) value=
 star aJ*KHeadMoment observation nontrivial half N value-
 star aH*FKHeadMoment observation nontrivial half N value := by
 rw [head_anchor observation nontrivial half]
 simp only [counted,←CountingDual.sourceCLM_apply,map_sub,map_smul,inner_sub_left,inner_smul_left,
  KHeadMoment,FKHeadMoment,starRingEnd_apply]

theorem outside_moment (N:Nat) (value:BurnolL2) :
 inner ℂ (sourceDelta observation nontrivial half (counted N (J.sourceOutside c m))) value=
 outsideMoment observation nontrivial half N value := by
 simp only [outsideMoment,J.sourceOutside,counted,←CountingDual.sourceCLM_apply,map_sum,map_smul,
  sum_inner,inner_smul_left,starRingEnd_apply]

theorem price_action (N:Nat) (value:BurnolL2) :
 CofinalQSource.priceCLM observation half N (r value)-CofinalQSource.priceCLM observation half N value=
 inner ℂ (sourceDelta observation nontrivial half (counted N (J.sourceQ observation half))) value := by
 simpa only [CofinalQSource.priceCLM,innerSL_apply_apply,inner_sub_right,counted] using
  (source_delta_read observation nontrivial half (counted N (J.sourceQ observation half)) value).symm

theorem price_precompose (N:Nat) :
 (CofinalQSource.priceCLM observation half N).comp (r-ContinuousLinearMap.id ℂ BurnolL2)=
 innerSL ℂ (sourceDelta observation nontrivial half (counted N (J.sourceQ observation half))) := by
 ext value
 simpa only [ContinuousLinearMap.comp_apply,sub_apply,ContinuousLinearMap.id_apply,map_sub,
  innerSL_apply_apply] using price_action observation nontrivial half N value

theorem price_generated_bill (N:Nat) (value:BurnolL2) :
 CofinalQSource.priceCLM observation half N (r value)-CofinalQSource.priceCLM observation half N value=
 generatedBill observation nontrivial half N value := by
 have inventory:=congrArg (fun kernel:BurnolL2=>
  inner ℂ (sourceDelta observation nontrivial half (counted N kernel)) value)
  (J.source_full_inventory observation half)
 simp only [counted,←CountingDual.sourceCLM_apply,map_add,inner_add_left] at inventory
 simp only [CountingDual.sourceCLM_apply] at inventory
 have outsideRead:inner ℂ (sourceDelta observation nontrivial half
   (counted N (J.sourceOutside (burnolDivisionZeroCompletedMellinCoordinate observation half.down) m))) value=
  outsideMoment observation nontrivial half N value := by
  simpa only [OriginalKCombCofinalTwoDirection.coordinate,originalKCoordinate,
   burnolDivisionZeroCompletedMellinCoordinate] using outside_moment observation nontrivial half N value
 have headRead:=head_moment observation nontrivial half N value
 dsimp only [counted] at headRead outsideRead
 rw [headRead,outsideRead] at inventory
 rw [price_action]
 unfold generatedBill paFeeMoment
 dsimp only [counted]
 linear_combination -inventory

-- These independent consumers see exactly the counted source effect used in the bill.
def source_price_receipt (N:Nat) (value:BurnolL2) :=
 let changed:=r value-value
 let source:=DualSource.source N changed
 PProd.mk (Prices.source_prices_generated observation nontrivial half source) <|
 PProd.mk (Prices.complete_price_generated observation nontrivial half source) <|
 PProd.mk (J.actual_Q_price observation nontrivial half source)
  (J.actual_outside_price observation half source)

def source_heads (N:Nat) (value:BurnolL2) :=
 PProd.mk (receipt observation nontrivial half) <|
 PProd.mk (installedOriginalKReceiptAt_eq_source observation nontrivial half.down) <|
 PProd.mk (originalK observation nontrivial half) <|
 PProd.mk (originalFK observation nontrivial half) <|
 PProd.mk (source_delta_read observation nontrivial half (counted N (originalK observation nontrivial half)) value) <|
 PProd.mk (source_delta_read observation nontrivial half (counted N (originalFK observation nontrivial half)) value) <|
 PProd.mk (source_delta_read observation nontrivial half (counted N (KHead observation nontrivial half)) value) <|
 PProd.mk (source_delta_read observation nontrivial half (counted N (FKHead observation nontrivial half)) value) <|
 PProd.mk (head_anchor observation nontrivial half)
  (J.source_full_inventory observation half)
end CountedPaInitial.BornRSourcePrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
