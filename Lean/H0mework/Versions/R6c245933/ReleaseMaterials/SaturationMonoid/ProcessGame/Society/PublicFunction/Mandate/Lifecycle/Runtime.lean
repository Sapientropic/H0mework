import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (input : BoundSource base scope)

def currentAt (visit : Nat) := input.source.currentAt (visit + 1)
def wordAt (visit : Nat) := (input.source.actualExecution visit).submitted

def frameCurrentAt (visit : Nat) := (input.source.frameAt (visit+1)).raw

def frameWordAt (visit : Nat) :=
  input.source.frameWord (visit+1) (input.source.frameAt (visit+1))

@[csimp] theorem currentAt_eq_frame : @currentAt = @frameCurrentAt := by
  funext
  exact (OutstandingSource.canonical_frame _ _).1

@[csimp] theorem wordAt_eq_frame : @wordAt = @frameWordAt := by
  funext
  exact OutstandingSource.actual_execution_word _ _

structure TracedGrant (birth last : Nat) where
  private mk ::
  admission : AdmittedGrant base scope (currentAt input birth) (wordAt input birth)
  continuation : History base scope (currentAt input) (wordAt input) birth admission.grant
  exact : continuation = through last

def traceGrant (birth last : Nat)
    (grant : Grant base scope (currentAt input birth) (wordAt input birth)) :
    TracedGrant input birth last :=
  ⟨admitGrant base scope _ _ grant, through last, rfl⟩

def recordsAt (last : Nat) : List (Sigma fun birth : Fin (last + 1) => TracedGrant input birth.val last) :=
  (List.finRange (last + 1)).flatMap fun birth =>
    (grantsAt base scope (currentAt input birth.val) (wordAt input birth.val)).map fun grant =>
      ⟨birth, traceGrant input birth.val last grant⟩

abbrev previousRoot := NativeRuntime.root input
abbrev previousFacade := NativeRuntime.facade input

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource input.source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (last : Nat) → current = (ProgrammeHistory.visitAt input.source.input (last + 1)).current →
      List (Sigma fun birth : Fin (last + 1) => TracedGrant input birth.val last)
  project := fun _ {_} _ _ last _canonical => recordsAt input last

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
  | previous (face : NativeRuntime.Face input)
  | lifecycle

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N input.source.input) where
  process := process input
  FaceAt := fun _ => Face input
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade input).componentAt (previousFacade input).seed previous
    | .lifecycle => projectionLaw input
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade input).installationAt (previousFacade input).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (previousRoot input).toAuthoritativeRoot.source (projectionLaw input))
    | lifecycle =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface (previousRoot input).toAuthoritativeRoot.source (projectionLaw input)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade input).projectionAt (previousFacade input).seed previous
    | .lifecycle => ()

def activated (ordinal : Nat) : LivingRuntimeState (process input) := (facade input).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated input ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem grant_is_in_payload (last : Nat) (birth : Fin (last + 1))
    (grant : Grant base scope (currentAt input birth.val) (wordAt input birth.val))
    (member : grant ∈ NativeRuntime.actualGrants input birth.val) :
    (⟨birth, traceGrant input birth.val last grant⟩ : Sigma fun birth : Fin (last + 1) => TracedGrant input birth.val last) ∈
      (projectionLaw input).project ()
        (ProgrammeSource.emitted input.source.input (ProgrammeHistory.visitAt input.source.input (last + 1)).current)
        () last rfl := by
  apply List.mem_flatMap.mpr
  refine ⟨birth, List.mem_finRange _, ?_⟩
  exact List.mem_map.mpr ⟨grant, member, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime
