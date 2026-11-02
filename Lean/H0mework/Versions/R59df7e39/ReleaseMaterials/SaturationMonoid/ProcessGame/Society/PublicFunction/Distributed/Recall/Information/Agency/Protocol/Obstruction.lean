import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Synthesis

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]



namespace Obstruction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (budget : Nat) (reference : Rule model.source.code)

def scan (rows : Rule model.source.code → Synthesis.Row model budget) : Bool :=
  (rules model.source.code).all fun protocol => !decide (Synthesis.holds model budget reference protocol (rows protocol))

theorem scan_iff (rows : Rule model.source.code → Synthesis.Row model budget) :
    scan model budget reference rows = true ↔
      ∀ protocol : Rule model.source.code, ¬ Synthesis.holds model budget reference protocol (rows protocol) := by
  simp only [scan,List.all_eq_true,Bool.not_eq_true',decide_eq_false_iff_not]
  exact ⟨fun checked protocol => checked protocol (every_rule_is_source_generated _ _),
    fun checked protocol _ => checked protocol⟩

structure Context where
  rejected : ∀ protocol : Rule model.source.code, Synthesis.Rejection model budget reference protocol
  generated : Synthesis.compile model budget reference = .blocked rejected

variable (world : World model budget) (context : Context model budget reference)

def rows : Rule model.source.code → Synthesis.Row model budget := fun protocol => (context.rejected protocol).row

theorem independently_replayed_failures : scan model budget reference (rows model budget reference context) = true :=
  (scan_iff model budget reference _).mpr fun protocol => (context.rejected protocol).broken

include context in
theorem no_protocol_passes_the_original_domain (protocol : Rule model.source.code) :
    ¬ Synthesis.acceptable model budget reference protocol := by
  intro accepted
  exact (context.rejected protocol).broken (accepted _ (context.rejected protocol).original)

structure Disposition (n : Nat) where
  origin : Context model budget reference
  origin_exact : origin = context
  source_generated : world ∈ worlds model budget
  independently_checked : scan model budget reference (rows model budget reference origin) = true
  native : Authority.Disposition (world.native model budget) (world.input model budget) (world.phase.val+n) rfl rfl
  native_exact : native = Authority.generate (world.native model budget) (world.input model budget) (world.phase.val+n) rfl rfl

def generate (n : Nat) : Disposition model budget reference world context n where
  origin := context
  origin_exact := rfl
  source_generated := every_world_is_generated _ _ _
  independently_checked := independently_replayed_failures model budget reference context
  native := Authority.generate (world.native model budget) (world.input model budget) (world.phase.val+n) rfl rfl
  native_exact := rfl

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (world.source model budget).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (n : Nat) →
    current = (ProgrammeHistory.visitAt (world.source model budget).input
      ((world.source model budget).history.length+2+(world.phase.val+n))).current →
      Disposition model budget reference world context n
  project := fun _ {_} _ _ n _ => generate model budget reference world context n

def root := (Authority.Runtime.root (world.native model budget) (world.input model budget) rfl rfl).withProjectionCoface
  (projectionLaw model budget reference world context)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (world.source model budget).input) :=
  ⟨ProgrammeSource.V (world.source model budget).input, root model budget reference world context,
    ProgrammeHistory.temporalVisit (world.source model budget).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (world.source model budget).input) where
  State := Nat
  stateAt := stateAt model budget reference world context
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (world.source model budget).input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (world.source model budget).input first).current =
        (ProgrammeHistory.visitAt (world.source model budget).input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Authority.Runtime.Face)
  | obstruction

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (world.source model budget).input) where
  process := process model budget reference world context
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Authority.Runtime.facade (world.native model budget) (world.input model budget) rfl rfl).componentAt
        (Authority.Runtime.facade (world.native model budget) (world.input model budget) rfl rfl).seed previous
    | .obstruction => projectionLaw model budget reference world context
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Authority.Runtime.facade (world.native model budget) (world.input model budget) rfl rfl).installationAt
        (Authority.Runtime.facade (world.native model budget) (world.input model budget) rfl rfl).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Authority.Runtime.root (world.native model budget) (world.input model budget) rfl rfl).toAuthoritativeRoot.source
            (projectionLaw model budget reference world context))
    | obstruction =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Authority.Runtime.root (world.native model budget) (world.input model budget) rfl rfl).toAuthoritativeRoot.source
        (projectionLaw model budget reference world context)
  projectionAt := fun _ face => match face with
    | .previous previous => (Authority.Runtime.facade (world.native model budget) (world.input model budget) rfl rfl).projectionAt
        (Authority.Runtime.facade (world.native model budget) (world.input model budget) rfl rfl).seed previous
    | .obstruction => ()

abbrev activated (ordinal : Nat) := (facade model budget reference world context).seed.advance ordinal

theorem activated_state_is_ordinal (ordinal : Nat) :
    (activated model budget reference world context ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated model budget reference world context ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

def atCut (n : Nat) : Disposition model budget reference world context n :=
  match (facade model budget reference world context).readoutAt
    (activated model budget reference world context ((world.source model budget).history.length+2+(world.phase.val+n))) .obstruction with
  | .inl actual => actual.2 n (by
      change (ProgrammeHistory.visitAt (world.source model budget).input
        (activated model budget reference world context ((world.source model budget).history.length+2+(world.phase.val+n))).state).current = _
      exact congrArg (fun ordinal => (ProgrammeHistory.visitAt (world.source model budget).input ordinal).current)
        (activated_state_is_ordinal model budget reference world context _))
  | .inr impossible => nomatch impossible

theorem same_actual_root_consumes_failure_native_ledger_and_open_next (n : Nat) :
    let actual := activated model budget reference world context ((world.source model budget).history.length+2+(world.phase.val+n))
    (atCut model budget reference world context n).origin = context ∧
      Synthesis.compile model budget reference = .blocked (atCut model budget reference world context n).origin.rejected ∧
      scan model budget reference (rows model budget reference (atCut model budget reference world context n).origin) = true ∧
      (atCut model budget reference world context n).native.current =
        Native.Authority.fullGenerate (world.native model budget) ((world.source model budget).history.length+1+(world.phase.val+n)) ∧
      HEq ((facade model budget reference world context).readoutAt actual .obstruction)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model budget reference world context).process.stateAt
        ((facade model budget reference world context).process.successor actual.state) := by
  have rooted := (facade model budget reference world context).readoutAt_factorizes
    (activated model budget reference world context ((world.source model budget).history.length+2+(world.phase.val+n))) .obstruction
  exact ⟨(atCut model budget reference world context n).origin_exact,
    (atCut model budget reference world context n).origin.generated,
    (atCut model budget reference world context n).independently_checked,
    (atCut model budget reference world context n).native.current_exact,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end Obstruction
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol
