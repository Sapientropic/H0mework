import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.GammaOutsideHistory
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.Consumer

set_option autoImplicit false
set_option Elab.async false
noncomputable section

universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.NextOutsideGamma

open CenteredGram.IntegralGraphJointAction
open OriginalGamma.Source.RelativeConductorGapReadback
open private source_actor fullR_actor from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.Consumer

namespace H
export OriginalKCrossParameterRAdjointSource.GammaOutsideHistory
  (write write_graph physical_start_graph history history_graph)
end H
namespace M
export BornRSealedMethodHistory (actualStock actualStock_zero physical_step)
end M
namespace Seed
export CompletedPaEulerTateBoundary (currentSource current_source_physical)
end Seed

local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "seed" => Seed.currentSource observation nontrivial half depth
local notation "stock" => M.actualStock observation nontrivial half depth ordinal

private theorem source_zero : riemannZeta (c).value = 0 := observation.mathlibZero

private def openingGamma : BurnolL2 :=
  H.write c (R c (R c seed), H.write c (R c seed, H.write c (seed, 0)))

private theorem opening_graph : GammaPair (O (stock 0).1.1)
    (openingGamma observation nontrivial half depth) := by
  rw [M.actualStock_zero]
  change GammaPair (O (R c ((BornWholeStockRConsumer.registeredValue
    observation nontrivial half depth ordinal).1.1))) _
  rw [BornWholeStockRConsumer.actual_R_squared]
  have zero := source_zero observation half
  have paid := H.physical_start_graph
    (⟨seed, Seed.current_source_physical observation nontrivial half depth⟩ : BurnolPaAmbientCarrier)
  have first := H.write_graph c zero seed 0 paid
  have second := H.write_graph c zero (R c seed) (H.write c (seed, 0)) first
  exact H.write_graph c zero (R c (R c seed))
    (H.write c (R c seed, H.write c (seed, 0))) second

/-- Every stage reads the original full cofinal stock before applying its two outside ports. -/
def outsideGamma (update : Nat) : BurnolL2 :=
  H.history c (fun n => (stock n).1.1) (openingGamma observation nontrivial half depth) update

theorem actual_outside_graph (update : Nat) :
    GammaPair (O (stock update).1.1) (outsideGamma observation nontrivial half depth ordinal update) :=
  H.history_graph c (source_zero observation half) (fun n => (stock n).1.1)
    (openingGamma observation nontrivial half depth)
    (opening_graph observation nontrivial half depth ordinal)
    (M.physical_step observation nontrivial half depth ordinal) update

section Installed
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : BornRSourcePrice.SourcePriceMethodReceipt
  (Parent := Parent) (Index := Index) (Whole := Whole) (Next := Next)
  (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)

private abbrev installedMaterial :=
  (Generic.compiledGamma observation nontrivial half depth ordinal method).native

/-- The actual compiler payload supplies both sides of the generated outside write. -/
theorem actual_installed_outside_write :
    GammaPair (O (installedMaterial observation nontrivial half depth ordinal method).fullR.1.1)
      (H.write c ((installedMaterial observation nontrivial half depth ordinal method).source.1.1,
        outsideGamma observation nontrivial half depth ordinal update)) := by
  rw [fullR_actor observation nontrivial half depth ordinal method,
    source_actor observation nontrivial half depth ordinal method]
  exact actual_outside_graph observation nontrivial half depth ordinal (update+1)

end Installed

end CountedPaInitial.BornRNativeGammaInstall.NextOutsideGamma
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
