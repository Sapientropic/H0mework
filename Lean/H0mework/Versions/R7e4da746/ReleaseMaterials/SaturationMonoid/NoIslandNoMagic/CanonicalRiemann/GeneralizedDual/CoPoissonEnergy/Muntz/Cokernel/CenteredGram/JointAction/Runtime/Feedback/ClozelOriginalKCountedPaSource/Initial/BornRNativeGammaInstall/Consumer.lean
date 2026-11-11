import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativePaInstall.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall
open Complex RootInquiryCompletion
open CenteredGram.IntegralGraphJointAction
open OriginalRSourceJointContact
open scoped InnerProductSpace
open private compiled_payload from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativePaInstall.Consumer
open private read_price_payload_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRSourcePrice.Consumer
namespace A
export BornRCanonicalMethodRuntime (nativeStock)
end A
namespace M
export BornRSealedMethodHistory (actualStock actualStock_step)
end M
namespace Price
export BornRSourcePrice (SourcePriceMethodReceipt actual_source_price_method native_input_source)
end Price
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "current" => M.actualStock observation nontrivial half depth ordinal
namespace Generic
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : Price.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
 (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
 observation nontrivial half depth ordinal update cutoff)

def compiledGamma : ActionMaterial observation nontrivial half
    (A.nativeStock method.source.1 method.source.2.1.1) :=
  (compiled_payload observation nontrivial half depth ordinal method).2.2.2

/-- The value is extracted from THIS compiler payload and this installed source face. -/
theorem compiledGamma_source :
    compiledGamma observation nontrivial half depth ordinal method = method.gammaNative.read := by
  exact congrArg (fun payload => payload.2.2.2)
    (read_price_payload_source method.price_method.2.1)

attribute [local irreducible] compiledGamma

private theorem same_native :
    (compiledGamma observation nontrivial half depth ordinal method).native = method.native.read :=
  (compiledGamma observation nontrivial half depth ordinal method).native_source.trans
    (BornRNativePaInstall.Installed.read_source observation nontrivial half method.native).symm

private theorem source_actor :
    (compiledGamma observation nontrivial half depth ordinal method).native.source = current update := by
  rw [same_native observation nontrivial half depth ordinal method]
  exact (Price.native_input_source observation nontrivial half method.source method.native).trans
    method.source_input

private theorem fullR_actor :
    (compiledGamma observation nontrivial half depth ordinal method).native.fullR = current (update+1) :=
  (compiledGamma observation nontrivial half depth ordinal method).native.fullR_source.trans
    ((congrArg (OriginalKFullSourceRAction.variableAction observation nontrivial half)
      (source_actor observation nontrivial half depth ordinal method)).trans
        (M.actualStock_step observation nontrivial half depth ordinal update).symm)

/-- The installed source equation is consumed on the original actor's actual jump. -/
theorem actual_stock_bill :
    (compiledGamma observation nontrivial half depth ordinal method).bill =
      inner ℂ (gammaField c m) ((current (update+1)).1.1 - (current update).1.1) := by
  exact (compiledGamma observation nontrivial half depth ordinal method).bill_effect.trans
    (congrArg₂ (fun head difference : BurnolL2 => inner ℂ head difference)
      (compiledGamma observation nontrivial half depth ordinal method).cotest_source
      (congrArg₂ (fun left right : CompletedSourceRCalculation.Value .branches => left.1.1-right.1.1)
        (fullR_actor observation nontrivial half depth ordinal method)
        (source_actor observation nontrivial half depth ordinal method)))
end Generic

end CountedPaInitial.BornRNativeGammaInstall
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
