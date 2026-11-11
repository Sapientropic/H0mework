import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.Nu
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PaCompressionPrice

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.SourceBalance
open Complex RootInquiryCompletion
open CenteredGram.IntegralGraphJointAction OriginalRSourceJointContact
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalGamma.Source.KGamma
open scoped InnerProductSpace
open private gammaField_power from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.CrossPrice
open private E_selfAdjoint from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PaCompressionPrice
open private source_actor fullR_actor from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.Consumer
namespace Compiled
export CountedPaInitial.BornRNativeGammaInstall.Generic (compiledGamma)
end Compiled
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "R" => burnolDirectRightResolventCLM c

/-- This head is computed from the original complete native action, before reading its bill. -/
def actionHead {input : C.Value .branches} (data : ActionMaterial observation nontrivial half input) : BurnolL2 :=
  (R^m) (data.native.fullR.1.1-data.native.source.1.1)

def sourcePaPrice (value : BurnolL2) : ℂ :=
  star (jQuarterAmplitude c)*PaCompressionPrice.sourcePaRead c value -
    star (hQuarterAmplitude c)*PaCompressionPrice.sourceInverseFourierPaRead c value

def sourceQPrice (value : BurnolL2) : ℂ :=
  star (jQuarterAmplitude c)*inner ℂ (actualGammaKernel c) (OriginalKCombCofinalPaAction.Q value : BurnolL2) -
    star (hQuarterAmplitude c)*inner ℂ (fourierL2 (actualGammaKernel c))
      (OriginalKCombCofinalPaAction.Q value : BurnolL2)

def sourceOutsidePrice (value : BurnolL2) : ℂ :=
  star (jQuarterAmplitude c)*inner ℂ (actualGammaKernel c) (BornRCountedPaPrice.outside value) -
    star (hQuarterAmplitude c)*inner ℂ (fourierL2 (actualGammaKernel c)) (BornRCountedPaPrice.outside value)

private theorem combo_Pa_price (value : BurnolL2) :
    inner ℂ (gammaCombo c) (OriginalKCombCofinalPaAction.E value : BurnolL2) =
      sourcePaPrice observation half value := by
  have paid := PaCompressionPrice.actual_gammaCombo_Pa_price c observation.mathlibZero value
  calc
    _ = inner ℂ (OriginalKCombCofinalPaAction.E (gammaCombo c) : BurnolL2) value :=
      E_selfAdjoint _ _
    _ = star (inner ℂ value (OriginalKCombCofinalPaAction.E (gammaCombo c) : BurnolL2)) :=
      (inner_conj_symm _ _).symm
    _ = star (PaCompressionPrice.compressionSourceBill c value) := congrArg star paid
    _ = _ := by
      simp only [PaCompressionPrice.compressionSourceBill,sourcePaPrice,star_sub,star_mul,star_star]
      ring

/-- The original E/Q/outside inventory pays the Pa face and preserves both remaining Gamma heads. -/
theorem combo_source_balance (value : BurnolL2) :
    inner ℂ (gammaCombo c) value = sourcePaPrice observation half value +
      sourceQPrice observation half value + sourceOutsidePrice observation half value := by
  have invisible := BornRCountedPaPrice.invisible_inventory value
  have inventory : value = (OriginalKCombCofinalPaAction.E value : BurnolL2)+
      (OriginalKCombCofinalPaAction.Q value : BurnolL2)+BornRCountedPaPrice.outside value := by
    change value-(OriginalKCombCofinalPaAction.E value : BurnolL2) = _ at invisible
    linear_combination (norm := module) invisible
  calc
    _ = inner ℂ (gammaCombo c) ((OriginalKCombCofinalPaAction.E value : BurnolL2)+
        (OriginalKCombCofinalPaAction.Q value : BurnolL2)+BornRCountedPaPrice.outside value) :=
      congrArg (fun head : BurnolL2 => inner ℂ (gammaCombo c) head) inventory
    _ = inner ℂ (gammaCombo c) (OriginalKCombCofinalPaAction.E value : BurnolL2)+
        inner ℂ (gammaCombo c) (OriginalKCombCofinalPaAction.Q value : BurnolL2)+
        inner ℂ (gammaCombo c) (BornRCountedPaPrice.outside value) := by rw [inner_add_right,inner_add_right]
    _ = _ := by
      rw [combo_Pa_price observation half value]
      simp only [sourceQPrice,sourceOutsidePrice,gammaCombo,inner_sub_left,inner_smul_left,starRingEnd_apply]

/-- The existing Gamma material generates its source balance without changing its schema. -/
theorem bill_source_balance {input : C.Value .branches}
    (data : ActionMaterial observation nontrivial half input) :
    data.bill = sourcePaPrice observation half (actionHead observation nontrivial half data) +
      sourceQPrice observation half (actionHead observation nontrivial half data) +
      sourceOutsidePrice observation half (actionHead observation nontrivial half data) := by
  have effect := data.bill_effect
  rw [data.cotest_source,gammaField_power,ContinuousLinearMap.adjoint_inner_left] at effect
  exact effect.trans (combo_source_balance observation half (actionHead observation nontrivial half data))

variable (depth ordinal : Nat)
local notation "stock" => M.actualStock observation nontrivial half depth ordinal
attribute [local irreducible] BornRSealedMethodHistory.actualStock Compiled.compiledGamma

private theorem actual_physical_power (start steps : Nat) :
    (R^steps) (stock start).1.1 = (stock (start+steps)).1.1 := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    rw [pow_succ',mul_apply_eq_comp,previous]
    exact (BornRSealedMethodHistory.physical_step observation nontrivial half depth ordinal (start+steps)).symm

namespace Generic
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : Price.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
 (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
 observation nontrivial half depth ordinal update cutoff)

/-- THIS fourth compiler leaf retains the complete original nu before the m-fold action. -/
theorem actual_head_nu :
    actionHead observation nontrivial half (Compiled.compiledGamma observation nontrivial half depth ordinal method) =
      (R^m) (Word.actualEffect observation nontrivial half depth ordinal update cutoff) := by
  unfold actionHead
  rw [fullR_actor observation nontrivial half depth ordinal method,
    source_actor observation nontrivial half depth ordinal method,
    ← actual_nu_physical observation nontrivial half depth ordinal update cutoff]

/-- The shifted jump is generated by the original actual R history, including all Unit and nonPa legs. -/
theorem actual_head_history :
    actionHead observation nontrivial half (Compiled.compiledGamma observation nontrivial half depth ordinal method) =
      (stock (update+m+1)).1.1-(stock (update+m)).1.1 := by
  have actual := actual_head_nu observation nontrivial half depth ordinal method
  rw [actual_nu_physical,map_sub,actual_physical_power,actual_physical_power] at actual
  have index : update+1+m=update+m+1 := by omega
  simpa only [index] using actual

/-- The actual compiled bill now consumes the full Pa source covector on that same generated nu history. -/
theorem actual_nu_source_balance :
    (Compiled.compiledGamma observation nontrivial half depth ordinal method).bill =
      sourcePaPrice observation half ((stock (update+m+1)).1.1-(stock (update+m)).1.1) +
      sourceQPrice observation half ((stock (update+m+1)).1.1-(stock (update+m)).1.1) +
      sourceOutsidePrice observation half ((stock (update+m+1)).1.1-(stock (update+m)).1.1) := by
  have paid := bill_source_balance observation nontrivial half
    (Compiled.compiledGamma observation nontrivial half depth ordinal method)
  rw [actual_head_history observation nontrivial half depth ordinal method] at paid
  exact paid
end Generic

attribute [local irreducible] Price.actual_source_price_method

set_option cleanup.letToHave false in
theorem actual_nu_source_balance (update cutoff : Nat) :
    (Compiled.compiledGamma observation nontrivial half depth ordinal
      (Price.actual_source_price_method observation nontrivial half depth ordinal update cutoff)).bill =
      sourcePaPrice observation half ((stock (update+m+1)).1.1-(stock (update+m)).1.1) +
      sourceQPrice observation half ((stock (update+m+1)).1.1-(stock (update+m)).1.1) +
      sourceOutsidePrice observation half ((stock (update+m+1)).1.1-(stock (update+m)).1.1) :=
  Generic.actual_nu_source_balance observation nontrivial half depth ordinal
    (Price.actual_source_price_method observation nontrivial half depth ordinal update cutoff)

end CountedPaInitial.BornRNativeGammaInstall.SourceBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
