import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference)

structure Disposition where
  newNative : Native.Disposition (replacement seed feasible) seed.history.length
  new_exact : newNative = Native.generate (replacement seed feasible) seed.history.length
  oldNative : Native.Disposition (original seed) seed.history.length
  old_exact : oldNative = Native.generate (original seed) seed.history.length
  profiles : profile seed.code (selection seed feasible).policy.policy (history seed) (table seed) =
    profile seed.code (reference seed) (history seed) (table seed)
  debts : ∀ index (inside : index < (before seed.code (reference seed) (history seed) (table seed)).current.slots.length),
    ∃ new ∈ (before seed.code (selection seed feasible).policy.policy (history seed) (table seed)).current.slots,
      Identity.DebtCorrespondence seed.code (original seed).input (replacement seed feasible).input
        (before seed.code (reference seed) (history seed) (table seed)).current.slots[index] new
  values : ValuesNoWorse seed.code (selection seed feasible).policy.policy (reference seed)
  payments : ∀ index (_inside : index < (before seed.code (reference seed) (history seed) (table seed)).current.slots.length),
    ∀ holder, received seed.code (reference seed) (history seed) (table seed) index holder ≤
      received seed.code (selection seed feasible).policy.policy (history seed) (table seed) index holder

def generate : Disposition seed feasible :=
  ⟨Native.generate (replacement seed feasible) _, rfl, Native.generate (original seed) _, rfl,
    actual_native_profiles_preserve_realized_rights seed feasible,
    actual_old_debts_keep_their_original_native_admission seed feasible,
    ((comparison_iff seed.code _ _).mp (selection seed feasible).policy.no_regression).1,
    actual_payment_receipts_do_not_regress seed feasible⟩

inductive Projection where | search | settlement

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (replacement seed feasible).input).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .search => Outcome seed.code (reference seed)
    | .settlement => current = (ProgrammeHistory.visitAt (replacement seed feasible).input (seed.history.length + 1)).current →
        Disposition seed feasible
  project := fun projection {_} _ _ => match projection with
    | .search => compile seed.code (reference seed)
    | .settlement => fun _own => generate seed feasible

def root := (Native.Runtime.root (replacement seed feasible)).withProjectionCoface (projectionLaw seed feasible)

theorem original_emitter_root_is_preserved : (root seed feasible).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (replacement seed feasible).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (replacement seed feasible).input) :=
  ⟨ProgrammeSource.V (replacement seed feasible).input, root seed feasible,
    ProgrammeHistory.temporalVisit (replacement seed feasible).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (replacement seed feasible).input) where
  State := Nat
  stateAt := stateAt seed feasible
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
  | search | settlement

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (replacement seed feasible).input) where
  process := process seed feasible
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.Runtime.facade (replacement seed feasible)).componentAt
        (Native.Runtime.facade (replacement seed feasible)).seed previous
    | .search | .settlement => projectionLaw seed feasible
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Native.Runtime.facade (replacement seed feasible)).installationAt
        (Native.Runtime.facade (replacement seed feasible)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Native.Runtime.root (replacement seed feasible)).toAuthoritativeRoot.source (projectionLaw seed feasible))
    | search | settlement =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Native.Runtime.root (replacement seed feasible)).toAuthoritativeRoot.source (projectionLaw seed feasible)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.Runtime.facade (replacement seed feasible)).projectionAt
        (Native.Runtime.facade (replacement seed feasible)).seed previous
    | .search => .search
    | .settlement => .settlement

def activated (ordinal : Nat) : LivingRuntimeState (process seed feasible) :=
  (facade seed feasible).seed.advance ordinal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Runtime
