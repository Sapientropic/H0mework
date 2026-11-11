import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativePaInstall.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.CrossPrice

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall
open Complex RootInquiryCompletion
open CenteredGram.IntegralGraphJointAction
open OriginalRSourceJointContact OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.RelativeConductorGapReadback
open scoped InnerProductSpace
namespace C
export CompletedSourceRCalculation (Value Slot)
end C
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate

/-- This calculation takes the same native material; no Gamma domain is imposed on its stock. -/
structure ActionMaterial (input : C.Value .branches) where
  native : BornRNativePaInstall.Material observation nontrivial half input
  native_source : native = BornRNativePaInstall.material observation nontrivial half input
  cotest : BurnolL2
  cotest_source : cotest = gammaField c m
  nextCotest : BurnolL2
  next_source : nextCotest = gammaField c (m+1)
  complete_graph : GammaPair (sourceField c m) cotest
  positionLog : BurnolL2
  position_source : LogPair (sourceField c m) positionLog
  frequencyLog : BurnolL2
  frequency_source : LogPair (fourierL2.symm (sourceField c m)) frequencyLog
  bill : ℂ
  bill_source : bill = inner ℂ (nextCotest - cotest) native.source.1.1
  bill_effect : bill = inner ℂ cotest (native.fullR.1.1 - native.source.1.1)

def gammaBill (input : C.Value .branches) : ℂ :=
  inner ℂ (gammaField c (m+1) - gammaField c m) input.1.1

private theorem actual_bill_effect (input : C.Value .branches) :
    gammaBill observation half input = inner ℂ (gammaField c m)
      ((BornRNativePaInstall.material observation nontrivial half input).fullR.1.1 - input.1.1) := by
  have actual := (BornRNativePaInstall.material observation nontrivial half input).physical_R.symm.trans
    (BornRNativePaInstall.material observation nontrivial half input).physical.whole_actual
  rw [(BornRNativePaInstall.material observation nontrivial half input).source_read] at actual
  rw [actual]
  unfold gammaBill
  rw [gammaField, inner_sub_left, ←sourceStep_actual,
    ContinuousLinearMap.adjoint_inner_left, inner_sub_right]

def actionMaterial (input : C.Value .branches) : ActionMaterial observation nontrivial half input where
  native := BornRNativePaInstall.material observation nontrivial half input
  native_source := rfl
  cotest := gammaField c m
  cotest_source := rfl
  nextCotest := gammaField c (m+1)
  next_source := rfl
  complete_graph := actual_source_graph c m
  positionLog := positionLogField c m
  position_source := (actual_source_two_logs c m).1
  frequencyLog := frequencyLogField c m
  frequency_source := (actual_source_two_logs c m).2
  bill := gammaBill observation half input
  bill_source := rfl
  bill_effect := actual_bill_effect observation nontrivial half input

section Native
variable {Sorts : Type} {U Y : Sorts → Type} [∀ target, AddCommGroup (U target)] {s : Sorts}
variable (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
  (Value := U) (Var := Y) (sort := s))
variable (input : C.Value .branches)

def component : SourceNativeProjectionLaw
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => ActionMaterial observation nontrivial half input
  project := fun _ {_current} _ _ => actionMaterial observation nontrivial half input
end Native

end CountedPaInitial.BornRNativeGammaInstall
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
