import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Receipts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Runtime

open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)

inductive Projection where | synthesis | opponentKeys | receipts

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource source.input).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .synthesis => Outcome source.code source.reference
    | .opponentKeys => List (Key source.code)
    | .receipts => current = (ProgrammeHistory.visitAt source.input (source.history.length + 1)).current →
        Metric Party Good Instrument → ℚ
  project := fun projection {_} _ _ => match projection with
    | .synthesis => source.answer
    | .opponentKeys => keys source.code
    | .receipts => fun _canonical => source.actualScore

def root := (ProgrammeLiving.livingRoot source.input).withProjectionCoface (projectionLaw source)

theorem original_root_is_preserved : (root source).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N source.input) :=
  ⟨ProgrammeSource.V source.input, root source, ProgrammeHistory.temporalVisit source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N source.input) where
  State := Nat
  stateAt := stateAt source
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N source.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt source.input first).current =
        (ProgrammeHistory.visitAt source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective source.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (projection : ProgrammeLiving.Projection)
  | synthesis | opponentKeys | receipts

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N source.input) where
  process := process source
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw source.input
    | .synthesis | .opponentKeys | .receipts => projectionLaw source
  installationAt := by
    intro _ face
    cases face with
    | previous _ =>
      exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot source.input).toAuthoritativeRoot.source (projectionLaw source)
    | synthesis | opponentKeys | receipts =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.livingRoot source.input).toAuthoritativeRoot.source (projectionLaw source)
  projectionAt := fun _ face => match face with
    | .previous projection => projection
    | .synthesis => .synthesis
    | .opponentKeys => .opponentKeys
    | .receipts => .receipts

def activated (ordinal : Nat) : LivingRuntimeState (process source) := (facade source).seed.advance ordinal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Runtime
