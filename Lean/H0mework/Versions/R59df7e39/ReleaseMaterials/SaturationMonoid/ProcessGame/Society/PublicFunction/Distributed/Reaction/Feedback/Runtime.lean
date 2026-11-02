import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Source
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Runtime

open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code)
  (active : source.feedback? = some input) (empty : source.continuation = [])

structure Disposition (index : Nat) where
  state : State source.code
  state_exact : state = source.feedbackState input index
  current_exact : state.current = (source.actualExecution (source.history.length + 1 + index)).before
  word_exact : (source.actualExecution (source.history.length + 1 + index)).submitted =
    word source.code (source.feedbackPolicy index) input state
  history_exact : state.history = source.history ++ [source.responseFrame.word] ++ source.feedbackWords index
  residual : Residual.Disposition source input index
  residual_exact : residual = Residual.generate source input index
  executions : (term : {term : List (Option source.code.Policy) // term ∈ Residual.scheduleTerms source input index}) →
    Execution.Disposition source input index term.val
  joint_executions : (term : {term : List (Option source.code.Policy) // term ∈ Residual.scheduleTerms source input index}) →
    ∀ n ≤ (source.feedbackState input index).remaining,
      (Execution.target source index term.val).feedbackState input (index + n) =
        Residual.run source.code (Residual.scheduleAt source index term.val)
          ⟨Residual.respond source.code (Residual.seed source input index) (Residual.schedules source input index)
            residual.table, input.budget⟩ (Residual.seed source input index) n
  future : (opponent : Opponent source.code) → Future.Disposition source input index opponent
  settlement : Cut.Disposition source input index
  native : Native.Disposition source (source.history.length + 1 + index)
  native_exact : native = Native.generate source (source.history.length + 1 + index)

def generate (index : Nat) : Disposition source input index :=
  ⟨source.feedbackState input index, rfl, source.feedback_body_reads_the_actual_local_current input active empty index,
    source.feedback_word_is_actual input active empty index,
    source.feedback_keeps_the_complete_actual_history input active empty index,
    Residual.generate source input index, rfl,
    (fun term => Execution.generate source input index term.val active empty),
    (fun term n bounded =>
      (Execution.the_whole_scheduled_run_is_the_actual_state source input index term.val n).trans
        (((Residual.generate source input index).whole_runs _
          (List.mem_map.mpr ⟨term.val, term.property, rfl⟩) n bounded).symm)),
    (fun opponent => Future.generate source input index opponent active empty),
    Cut.generate source input index active empty, Native.generate source _, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (index : Nat) →
    current = (ProgrammeHistory.visitAt source.input (source.history.length + 2 + index)).current →
      Disposition source input index
  project := fun _ {_} _ _ index _own => generate source input active empty index

def root := (Native.Runtime.root source).withProjectionCoface (projectionLaw source input active empty)

theorem original_emitter_root_is_preserved :
    (root source input active empty).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N source.input) :=
  ⟨ProgrammeSource.V source.input, root source input active empty, ProgrammeHistory.temporalVisit source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N source.input) where
  State := Nat
  stateAt := stateAt source input active empty
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
  | previous (face : Native.Runtime.Face)
  | feedback

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N source.input) where
  process := process source input active empty
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.Runtime.facade source).componentAt (Native.Runtime.facade source).seed previous
    | .feedback => projectionLaw source input active empty
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Native.Runtime.facade source).installationAt (Native.Runtime.facade source).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Native.Runtime.root source).toAuthoritativeRoot.source (projectionLaw source input active empty))
    | feedback =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Native.Runtime.root source).toAuthoritativeRoot.source (projectionLaw source input active empty)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.Runtime.facade source).projectionAt (Native.Runtime.facade source).seed previous
    | .feedback => ()

def activated (ordinal : Nat) : LivingRuntimeState (process source input active empty) :=
  (facade source input active empty).seed.advance ordinal

theorem activated_state_is_the_generated_ordinal (ordinal : Nat) :
    (activated source input active empty ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated source input active empty ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Runtime
