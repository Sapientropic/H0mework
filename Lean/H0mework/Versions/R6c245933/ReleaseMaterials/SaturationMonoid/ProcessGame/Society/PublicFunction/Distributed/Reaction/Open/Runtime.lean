import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference)

structure Extension where
  reserve : Party → Good → ℚ
  nonnegative : ∀ party good, 0 ≤ reserve party good
  full_carrier : ((replacement seed feasible).actualExecution seed.history.length).after =
    ((original seed).actualExecution seed.history.length).after.addReserve reserve
  replay : ∀ words : List (RawEvent Party Good Port Technology Instrument),
    LegalHistory seed.code.law ((original seed).actualExecution seed.history.length).after words →
    LegalHistory seed.code.law ((replacement seed feasible).actualExecution seed.history.length).after words ∧
      words.foldl seed.code.law.next ((replacement seed feasible).actualExecution seed.history.length).after =
        (words.foldl seed.code.law.next ((original seed).actualExecution seed.history.length).after).addReserve reserve

def generateExtension (stable : Stable seed.code.law) : Extension seed feasible :=
  ⟨reserve seed.code (selection seed feasible).policy.policy seed.reference seed.history seed.opponent,
    (actual_full_carrier_extension seed feasible).1, (actual_full_carrier_extension seed feasible).2,
    all_old_legal_histories_remain_actually_open seed feasible stable⟩

variable (stable : Stable seed.code.law)

inductive Projection where | search | continuation

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (replacement seed feasible).input).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .search => Outcome seed.code seed.reference
    | .continuation => current = (ProgrammeHistory.visitAt (replacement seed feasible).input (seed.history.length + 1)).current →
        Extension seed feasible
  project := fun projection {_} _ _ => match projection with
    | .search => compile seed.code seed.reference seed.reference_generated
    | .continuation => fun _own => generateExtension seed feasible stable

def root := (Native.Runtime.root (replacement seed feasible)).withProjectionCoface (projectionLaw seed feasible stable)

theorem original_emitter_root_is_preserved : (root seed feasible stable).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (replacement seed feasible).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (replacement seed feasible).input) :=
  ⟨ProgrammeSource.V (replacement seed feasible).input, root seed feasible stable,
    ProgrammeHistory.temporalVisit (replacement seed feasible).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (replacement seed feasible).input) where
  State := Nat
  stateAt := stateAt seed feasible stable
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (replacement seed feasible).input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (replacement seed feasible).input first).current =
        (ProgrammeHistory.visitAt (replacement seed feasible).input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (replacement seed feasible).input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Native.Runtime.Face)
  | search | continuation

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (replacement seed feasible).input) where
  process := process seed feasible stable
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.Runtime.facade (replacement seed feasible)).componentAt
        (Native.Runtime.facade (replacement seed feasible)).seed previous
    | .search | .continuation => projectionLaw seed feasible stable
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Native.Runtime.facade (replacement seed feasible)).installationAt
        (Native.Runtime.facade (replacement seed feasible)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Native.Runtime.root (replacement seed feasible)).toAuthoritativeRoot.source (projectionLaw seed feasible stable))
    | search | continuation =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Native.Runtime.root (replacement seed feasible)).toAuthoritativeRoot.source (projectionLaw seed feasible stable)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.Runtime.facade (replacement seed feasible)).projectionAt
        (Native.Runtime.facade (replacement seed feasible)).seed previous
    | .search => .search
    | .continuation => .continuation

def activated (ordinal : Nat) : LivingRuntimeState (process seed feasible stable) :=
  (facade seed feasible stable).seed.advance ordinal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Runtime
