import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextOutsideGamma
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaIterated.Kernel

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.GammaOutsideHistory.Second

open MeasureTheory BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.JointLogConductor OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.KGamma OriginalGamma.Source.KGamma.Iterated
open OriginalKCrossParameterRAdjointSource.GammaOutsideDomain
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKFullAdjointSource OriginalKSourceResolventReconstruction
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open scoped InnerProductSpace

open private columnScale adjoint_graph from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.GammaOutsideDomain
open private emitted returning from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.GammaOutsideHistory
open private gamma_pair_fourier from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource

local notation "R" => burnolDirectRightResolventCLM
local notation "F" => fourierL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

def forwardColumnSecondGamma (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (columnScale (K c : BurnolL2))⁻¹ •
    ((sourceForwardRatio c / (sourceDamping c : ℂ)) • actualSecondGammaKernel (barC c) -
      (sourceDamping c : ℂ)⁻¹ • F (actualSecondGammaKernel c) - R c (F (actualSecondGammaKernel c)))

def adjointColumnSecondGamma (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (columnScale (K (barC c) : BurnolL2))⁻¹ •
    ((sourceAdjointRatio c / (sourceDamping c : ℂ)) • F (actualSecondGammaKernel c) -
      (sourceDamping c : ℂ)⁻¹ • actualSecondGammaKernel (barC c) -
      sourceAdjoint c (actualSecondGammaKernel (barC c)))

theorem actual_forward_column_second_gamma (c : BurnolCompletedMellinCoordinate) :
    GammaPair (forwardColumnGamma c) (forwardColumnSecondGamma c) := by
  have fourier := gamma_pair_fourier _ _ (actual_second_gamma_kernel c)
  have acted := actual_Gamma_R c _ _ fourier
  intro test
  simp only [forwardColumnGamma, forwardColumnSecondGamma, inner_smul_right, inner_sub_right,
    actual_second_gamma_kernel (barC c) test, fourier test, acted test]

theorem actual_adjoint_column_second_gamma (c : BurnolCompletedMellinCoordinate) :
    GammaPair (adjointColumnGamma c) (adjointColumnSecondGamma c) := by
  have fourier := gamma_pair_fourier _ _ (actual_second_gamma_kernel c)
  have acted := adjoint_graph c (actual_second_gamma_kernel (barC c))
  intro test
  simp only [adjointColumnGamma, adjointColumnSecondGamma, inner_smul_right, inner_sub_right,
    actual_second_gamma_kernel (barC c) test, fourier test, acted test]

/-- The original outside write reads the same two stock coefficients at the second Gamma level. -/
def writeSecond (c : BurnolCompletedMellinCoordinate) : (BurnolL2 × BurnolL2) →L[ℂ] BurnolL2 :=
  (((emitted c).smulRight (forwardColumnSecondGamma c)).comp (ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2)) +
    (R c).comp (ContinuousLinearMap.snd ℂ BurnolL2 BurnolL2) -
  (((returning c).smulRight (actualSecondGammaKernel (barC c))).comp
    (ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2))

theorem write_second_graph (c : BurnolCompletedMellinCoordinate) (old first second : BurnolL2)
    (paid : GammaPair first second) :
    GammaPair (write c (old, first)) (writeSecond c (old, second)) := by
  intro test
  change inner ℂ (wholeConductorTest test)
    (emitted c old • forwardColumnGamma c + R c first - returning c old • actualGammaKernel (barC c)) =
      inner ℂ (test.toLp 2 volume)
        (emitted c old • forwardColumnSecondGamma c + R c second -
          returning c old • actualSecondGammaKernel (barC c))
  simp only [inner_add_right, inner_sub_right, inner_smul_right,
    actual_forward_column_second_gamma c test, actual_Gamma_R c _ _ paid test,
    actual_second_gamma_kernel (barC c) test]

def historySecond (c : BurnolCompletedMellinCoordinate) (stock : ℕ → BurnolL2)
    (opening : BurnolL2) (n : ℕ) : BurnolL2 :=
  Nat.rec opening (fun j previous => writeSecond c (stock j, previous)) n

theorem history_second_graph (c : BurnolCompletedMellinCoordinate) (stock : ℕ → BurnolL2)
    (first second : BurnolL2) (opening : GammaPair first second) (n : ℕ) :
    GammaPair (history c stock first n) (historySecond c stock second n) := by
  induction n with
  | zero => exact opening
  | succ n prior => exact write_second_graph c (stock n) _ _ prior

end OriginalKCrossParameterRAdjointSource.GammaOutsideHistory.Second
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.NextOutsideGamma.Second

open CenteredGram.IntegralGraphJointAction
open OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.JointLogConductor
open OriginalKCrossParameterRAdjointSource.GammaOutsideHistory.Second
open MeasureTheory
open scoped InnerProductSpace

open private openingGamma from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextOutsideGamma
open private gamma_pair_fourier from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
open private source_actor from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.Consumer

local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "seed" => Seed.currentSource observation nontrivial half depth
local notation "stock" => M.actualStock observation nontrivial half depth ordinal

private def openingSecondGamma : BurnolL2 :=
  writeSecond c (R c (R c seed), writeSecond c (R c seed, writeSecond c (seed, 0)))

private theorem opening_second_graph :
    GammaPair (openingGamma observation nontrivial half depth)
      (openingSecondGamma observation nontrivial half depth) := by
  have origin : GammaPair (0 : BurnolL2) 0 := by
    intro test
    simp only [inner_zero_right]
  exact write_second_graph c (R c (R c seed)) _ _
    (write_second_graph c (R c seed) _ _ (write_second_graph c seed _ _ origin))

/-- The second Gamma field is generated from the same complete stock history and the three opening actions. -/
def outsideSecondGamma (update : Nat) : BurnolL2 :=
  historySecond c (fun j => (stock j).1.1) (openingSecondGamma observation nontrivial half depth) update

theorem actual_outside_second_graph (update : Nat) :
    GammaPair (outsideGamma observation nontrivial half depth ordinal update)
      (outsideSecondGamma observation nontrivial half depth ordinal update) :=
  history_second_graph c (fun j => (stock j).1.1) _ _
    (opening_second_graph observation nontrivial half depth) update

section Installed
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : BornRSourcePrice.SourcePriceMethodReceipt
  (Parent := Parent) (Index := Index) (Whole := Whole) (Next := Next)
  (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)

attribute [local irreducible] Generic.compiledGamma

private abbrev material := (Generic.compiledGamma observation nontrivial half depth ordinal method).native
local notation "native" => material observation nontrivial half depth ordinal method
local notation "first" => outsideGamma observation nontrivial half depth ordinal update
local notation "second" => outsideSecondGamma observation nontrivial half depth ordinal update

/-- The same compiled jump generates both graph levels on the literal position and Fourier slots. -/
theorem actual_installed_outside_second_write :
    GammaPair (O (native).fullR.1.1) (H.write c ((native).source.1.1, first)) ∧
    GammaPair (H.write c ((native).source.1.1, first))
      (writeSecond c ((native).source.1.1, second)) ∧
    GammaPair (O (native).fullR.2.1) (fourierL2 (H.write c ((native).source.1.1, first))) ∧
    GammaPair (fourierL2 (H.write c ((native).source.1.1, first)))
      (fourierL2 (writeSecond c ((native).source.1.1, second))) ∧
    writeSecond c ((native).source.1.1, second) =
      outsideSecondGamma observation nontrivial half depth ordinal (update+1) := by
  have firstGraph := actual_installed_outside_write observation nontrivial half depth ordinal method
  have secondGraph := write_second_graph c (native).source.1.1 _ _
    (actual_outside_second_graph observation nontrivial half depth ordinal update)
  have fourierSlot : (native).fullR.2.1 = fourierL2 (native).fullR.1.1 := by
    rw [(native).fullR_source]
    rfl
  have fourierOutside : fourierL2 (O (native).fullR.1.1) = O (native).fullR.2.1 := by
    have residualEq (value : BurnolL2) :
        O value = evenBurnolPhysicalResidual burnolUnscaledCommonGapRadius value := by
      change O value = value - evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius value
      have split := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal value
      change evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius value + O value = value at split
      linear_combination (norm := module) split
    rw [fourierSlot]
    simpa only [← residualEq] using
      fourierL2_evenBurnolPhysicalResidual burnolUnscaledCommonGapRadius (native).fullR.1.1
  have fourierFirst := gamma_pair_fourier _ _ firstGraph
  rw [fourierOutside] at fourierFirst
  refine ⟨firstGraph, secondGraph, fourierFirst, gamma_pair_fourier _ _ secondGraph, ?_⟩
  have source := source_actor observation nontrivial half depth ordinal method
  change (native).source = stock update at source
  rw [source]
  rfl

end Installed

end CountedPaInitial.BornRNativeGammaInstall.NextOutsideGamma.Second
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
