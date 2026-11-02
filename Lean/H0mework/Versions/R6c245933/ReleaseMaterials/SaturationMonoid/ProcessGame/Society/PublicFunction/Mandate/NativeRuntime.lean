import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate

open Institutions.Capitalism.Universal.Source.Program

structure BoundSource {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port)) where
  source : OutstandingSource Party Good Port (State Party Technology) Instrument
  law_exact : source.seed.law = law base scope

namespace NativeRuntime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (input : BoundSource base scope)

abbrev previousRoot := OutstandingSource.NativeService.Runtime.root input.source
abbrev previousFacade := OutstandingSource.NativeService.Runtime.facade input.source

def actualGrants (depth : Nat) :=
  grantsAt base scope (input.source.currentAt (depth + 1)) (input.source.actualExecution depth).submitted

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource input.source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (depth : Nat) → current = (ProgrammeHistory.visitAt input.source.input (depth + 1)).current →
      List (AdmittedGrant base scope (input.source.currentAt (depth + 1)) (input.source.actualExecution depth).submitted)
  project := fun _ {_} _ _ depth _canonical => (actualGrants input depth).map (admitGrant base scope _ _)

def root := (previousRoot input).withProjectionCoface (projectionLaw input)

theorem original_root_is_preserved :
    (root input).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot input.source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N input.source.input) :=
  ⟨ProgrammeSource.V input.source.input, root input, ProgrammeHistory.temporalVisit input.source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N input.source.input) where
  State := Nat
  stateAt := stateAt input
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N input.source.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt input.source.input first).current =
        (ProgrammeHistory.visitAt input.source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective input.source.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : OutstandingSource.NativeService.Runtime.Face input.source)
  | mandate

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N input.source.input) where
  process := process input
  FaceAt := fun _ => Face input
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade input).componentAt (previousFacade input).seed previous
    | .mandate => projectionLaw input
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade input).installationAt (previousFacade input).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (previousRoot input).toAuthoritativeRoot.source (projectionLaw input))
    | mandate =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface (previousRoot input).toAuthoritativeRoot.source (projectionLaw input)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade input).projectionAt (previousFacade input).seed previous
    | .mandate => ()

def activated (ordinal : Nat) : LivingRuntimeState (process input) := (facade input).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated input ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

end NativeRuntime
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

/-- Read the original grant event from its complete source-owned frame. -/
def actualGrantsFromFrame (input : BoundSource base scope) (depth : Nat) :
    List (Grant base scope (input.source.currentAt (depth + 1))
      (input.source.actualExecution depth).submitted) :=
  let frame := input.source.frameAt (depth + 1)
  let currentEq := (input.source.canonical_frame (depth + 1)).1
  let wordEq := input.source.actual_execution_word depth
  let typesEq := congrArg₂ (fun current word => List (Grant base scope current word)) currentEq wordEq
  cast typesEq.symm (grantsAt base scope frame.raw (input.source.frameWord (depth + 1) frame))

@[csimp] theorem actualGrants_eq_frame : @actualGrants = @actualGrantsFromFrame := by
  funext Party Good Port Technology Instrument decParty decGood decPort decTechnology decInstrument base scope input depth
  have grantsCongr (first last : RawCurrent Party Good (State Party Technology) Instrument)
      (word other : RawEvent Party Good Port (State Party Technology) Instrument)
      (currentEq : first = last) (wordEq : word = other) :
      HEq (grantsAt base scope first word) (grantsAt base scope last other) := by
    cases currentEq
    cases wordEq
    rfl
  apply eq_of_heq
  unfold actualGrants actualGrantsFromFrame
  exact (grantsCongr _ _ _ _ (input.source.canonical_frame (depth + 1)).1
    (input.source.actual_execution_word depth)).trans (cast_heq _ _).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime
