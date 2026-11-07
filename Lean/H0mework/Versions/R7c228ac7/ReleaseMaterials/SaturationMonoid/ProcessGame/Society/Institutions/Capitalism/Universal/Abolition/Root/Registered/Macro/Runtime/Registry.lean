import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Erasure
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Successor
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Successor
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Continuation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.InputRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

abbrev batchFrame (tick : Nat) := frames (nativeOrigin := datum.nativeOrigin) (review := review) input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit
  depth (Ingress.cut input depth sourceStart) Physical.initial
  (Ingress.proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0 reader tick

abbrev actualFrame (tick : Nat) := activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick

inductive Stage
  | input | account (tick : Nat)

def registryPresentation : Stage → RootInquiryStatePresentation
  | .input => Ingress.presentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
  | .account tick => (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).presentation

private theorem original_input_projection_mod :
    erasedProjectionCard (Ingress.presentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).erase % 4 = 1 := by
  let original := Ingress.frame input depth sourceStart
  have oldFinite : Finite original.native.root.toAuthoritativeRoot.source.projectionLaw.Projection := original.projectionFinite
  have addedFinite : Finite Ingress.Projection := ingress_projection_finite
  change Nat.card (SourceNativeProjectionCoface original.native.root.toAuthoritativeRoot.source.projectionLaw.Projection Ingress.Projection) % 4 = 1
  rw [Nat.card_congr (cofaceEquiv _ _), Nat.card_sum, ingress_projection_card]
  have oldMod := original_frames_projection_mod input depth (Ingress.cut input depth sourceStart)
  change Nat.card original.native.root.toAuthoritativeRoot.source.projectionLaw.Projection % 4 = 2 at oldMod
  omega

theorem input_ne_account (tick : Nat) :
    (Ingress.presentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).erase ≠
      (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).presentation.erase := by
  intro same
  have projections := congrArg erasedProjectionCard same
  have original := original_input_projection_mod (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
  have later := activated_frames_projection_mod (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick
  rw [projections] at original
  dsimp only [actualFrame] at original
  omega

theorem input_successor_valid (query : (Ingress.presentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).Query) :
    (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader 0).presentation.erase =
        (RootInquiryProcessNode.answered (Ingress.presentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader) query).erase ∧
      (RootInquiryProcessNode.active (Ingress.presentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)).PreservesGeneratedLivingLawAt
        query (.active (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader 0).presentation) := by
  apply RootInquiryProcessNode.active_actualAction_successor_valid
    (Ingress.presentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)
    (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader 0).presentation query
    (Ingress.generated (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)
  · exact Ingress.registered_input_compiles_the_same_source_action (review := review) input depth sourceStart datum prefixLimit renewalLimit reader query
  · exact (congrArg (fun current =>
      (⟨(Ingress.generated (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).target.TargetN, current⟩ : AnyAuthoritativeRootCurrent))
      (Ingress.actual_action_returns_the_literal_next_visit (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)).symm
  · exact HEq.rfl

def process : SourceNativeInquiryEngineProcess where
  State := Stage
  stateAt := fun stage => .active (registryPresentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader stage)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive same
    cases leftActive
    cases rightActive
    cases left with
    | input => cases right with
        | input => rfl
        | account tick => exact (input_ne_account (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick same).elim
    | account first => cases right with
        | input => exact (input_ne_account (review := review) input depth sourceStart datum prefixLimit renewalLimit reader first same.symm).elim
        | account second =>
            apply congrArg Stage.account
            exact activated_frames_erase_injective (review := review) input depth sourceStart datum prefixLimit renewalLimit reader same

  initial := .input
  successorAt := by
    intro stage query
    cases stage with
    | input => exact ⟨.account 0, input_successor_valid (review := review) input depth sourceStart datum prefixLimit renewalLimit reader query⟩
    | account tick => exact ⟨.account (tick + 1), (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).successor_valid query⟩

def initialInput : Engine.SourceNativeInquiryRegisteredInputAt
    (Engine.initial (process (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)) :=
  Ingress.registeredInput (review := review) input depth sourceStart datum prefixLimit renewalLimit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.process
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.input_successor_valid
