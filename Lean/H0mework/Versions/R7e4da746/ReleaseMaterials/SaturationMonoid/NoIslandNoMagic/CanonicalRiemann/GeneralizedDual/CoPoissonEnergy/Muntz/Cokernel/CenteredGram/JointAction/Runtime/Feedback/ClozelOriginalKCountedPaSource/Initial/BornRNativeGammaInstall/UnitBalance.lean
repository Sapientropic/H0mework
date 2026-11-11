import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.UnitPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.SourceBalance

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.UnitBalance
open Complex RootInquiryCompletion
open CenteredGram.IntegralGraphJointAction OriginalRSourceJointContact
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCenteredMobiusRSource.UnitTailActionSource
open OriginalGamma.Source.KGamma OriginalGamma.Source.KappaConductor
open scoped InnerProductSpace BigOperators
open private combo_Pa_price from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.SourceBalance
namespace Compiled
export CountedPaInitial.BornRNativeGammaInstall.Generic (compiledGamma)
end Compiled
namespace Port
export OriginalKCrossParameterRAdjointSource.PaNativePortSource (loop)
end Port
namespace Source
export PaCoefficientSourceGram (generatedPa sourceMoment)
export PaCoefficientSourceGramConsumer (wholeProgramme whole_programme_actual returnCoefficient)
end Source
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "R" => burnolDirectRightResolventCLM c
local notation "alpha" => Source.returnCoefficient observation nontrivial half
local notation "WP" => Source.wholeProgramme c

/-- The two actual Unit source faces retain the q clock and the entire native exterior. -/
def unitSourcePrice (j : Nat) : ℂ :=
  star (jQuarterAmplitude c)*inner ℂ (originalDualLogValue c) (burnolTateReciprocalL2 (nativeUnitMuSource c j)) -
    star (hQuarterAmplitude c)*inner ℂ (originalDualLogValue c) (nativeUnitMuSource c j)

/-- Every finite coefficient is read from the original complete Pa and Unit source inventory. -/
def programmeSourcePrice (n : Nat) : ℂ :=
  SourceBalance.sourcePaPrice observation half ((Port.loop c n (Source.generatedPa c) : BurnolPaAmbientCarrier) : BurnolL2) +
    ∑ i ∈ Finset.range n, Source.sourceMoment c i * unitSourcePrice observation half (n-1-i)

private theorem unit_source_price (j : Nat) :
    inner ℂ (gammaCombo c) ((R^j) (burnolUnitTailResponse c 4)) = unitSourcePrice observation half j := by
  simp only [gammaCombo,inner_sub_left,inner_smul_left,starRingEnd_apply,
    UnitPrice.actual_original_Unit_Gamma_price c observation.mathlibZero,
    UnitPrice.actual_original_Unit_FourierGamma_price c observation.mathlibZero,unitSourcePrice]

private theorem loop_source_price (n : Nat) :
    inner ℂ (gammaCombo c) ((Port.loop c n (Source.generatedPa c) : BurnolPaAmbientCarrier) : BurnolL2) =
      SourceBalance.sourcePaPrice observation half
        ((Port.loop c n (Source.generatedPa c) : BurnolPaAmbientCarrier) : BurnolL2) := by
  let p := Port.loop c n (Source.generatedPa c)
  have exactE : OriginalKCombCofinalPaAction.E ((p : BurnolPaAmbientCarrier) : BurnolL2) =
      (p : BurnolPaAmbientCarrier) := by
    change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolEvenAmbientProjection ((p : BurnolPaAmbientCarrier) : BurnolL2)) = _
    have physical : burnolEvenAmbientProjection ((p : BurnolPaAmbientCarrier) : BurnolL2) =
        (p : BurnolPaAmbientCarrier) := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    rw [physical]
    exact Submodule.starProjection_eq_self_iff.mpr p.property
  have paid := combo_Pa_price observation half ((p : BurnolPaAmbientCarrier) : BurnolL2)
  rw [exactE] at paid
  exact paid

theorem whole_programme_source_price (n : Nat) :
    inner ℂ (gammaCombo c) (WP n) = programmeSourcePrice observation half n := by
  simp only [Source.wholeProgramme,inner_add_right,inner_sum,inner_smul_right,
    unit_source_price observation half,loop_source_price observation half,programmeSourcePrice]

private theorem programme_step (n : Nat) : R (WP n) = WP (n+1) := by
  rw [Source.whole_programme_actual,Source.whole_programme_actual,pow_succ',mul_apply_eq_comp]

variable (depth ordinal : Nat)
local notation "stock" => M.actualStock observation nontrivial half depth ordinal
attribute [local irreducible] BornRSealedMethodHistory.actualStock Compiled.compiledGamma

/-- The stock is the original complete programme, including its three already-generated R actions. -/
theorem actual_stock_programme (update : Nat) :
    (stock update).1.1 = alpha • WP (m+3+update) := by
  induction update with
  | zero =>
    have actual := congrArg (fun value : C.Value .branches => value.1.1)
      (BornRSealedMethodHistory.actualStock_zero observation nontrivial half depth ordinal)
    change (stock 0).1.1 = R (BornWholeStockRConsumer.registeredValue observation nontrivial half depth ordinal).1.1 at actual
    have current : CompletedPaEulerTateBoundary.currentSource observation nontrivial half depth =
        alpha • WP m := CompletedPaEulerTateBoundary.current_source_inventory observation nontrivial half depth
    rw [BornWholeStockRConsumer.actual_R_squared,current,map_smul,map_smul,map_smul,
      programme_step observation half,programme_step observation half,programme_step observation half] at actual
    exact actual
  | succ update previous =>
    rw [BornRSealedMethodHistory.physical_step observation nontrivial half depth ordinal update,previous,map_smul,
      programme_step observation half]
    simp only [Nat.add_assoc]

namespace Generic
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : Price.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
 (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
 observation nontrivial half depth ordinal update cutoff)

/-- The existing material's head is generated by the whole Pa-plus-Unit programme, not identified with K. -/
theorem actual_head_programme :
    SourceBalance.actionHead observation nontrivial half
      (Compiled.compiledGamma observation nontrivial half depth ordinal method) =
      alpha • (WP (2*m+update+4)-WP (2*m+update+3)) := by
  have actual := SourceBalance.Generic.actual_head_history observation nontrivial half depth ordinal method
  rw [actual_stock_programme observation nontrivial half depth ordinal,
    actual_stock_programme observation nontrivial half depth ordinal] at actual
  have upper : m+3+(update+m+1)=2*m+update+4 := by omega
  have lower : m+3+(update+m)=2*m+update+3 := by omega
  simpa only [upper,lower,smul_sub] using actual

/-- THIS compiler bill consumes both Unit Gamma heads through the actual original stock convolution. -/
theorem actual_nu_source_bill :
    (Compiled.compiledGamma observation nontrivial half depth ordinal method).bill =
      alpha * (programmeSourcePrice observation half (2*m+update+4)-
        programmeSourcePrice observation half (2*m+update+3)) := by
  have actual := (SourceBalance.bill_source_balance observation nontrivial half
    (Compiled.compiledGamma observation nontrivial half depth ordinal method)).trans
    (SourceBalance.combo_source_balance observation half (SourceBalance.actionHead observation nontrivial half
      (Compiled.compiledGamma observation nontrivial half depth ordinal method))).symm
  rw [actual_head_programme observation nontrivial half depth ordinal method,
    inner_smul_right,inner_sub_right,whole_programme_source_price observation half,
    whole_programme_source_price observation half] at actual
  exact actual
end Generic

attribute [local irreducible] Price.actual_source_price_method

set_option cleanup.letToHave false in
theorem actual_nu_source_bill (update cutoff : Nat) :
    (Compiled.compiledGamma observation nontrivial half depth ordinal
      (Price.actual_source_price_method observation nontrivial half depth ordinal update cutoff)).bill =
      alpha * (programmeSourcePrice observation half (2*m+update+4)-
        programmeSourcePrice observation half (2*m+update+3)) :=
  Generic.actual_nu_source_bill observation nontrivial half depth ordinal
    (Price.actual_source_price_method observation nontrivial half depth ordinal update cutoff)

end CountedPaInitial.BornRNativeGammaInstall.UnitBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
