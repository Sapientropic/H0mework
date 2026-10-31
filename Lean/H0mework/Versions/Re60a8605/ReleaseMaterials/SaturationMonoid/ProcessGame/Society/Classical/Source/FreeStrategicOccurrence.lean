import H0mework.Foundation.Agency.Lineage
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Source.FreeStrategicSyntax

/-!
# Free strategic occurrence and exact restrictions

The decoded syntax generates one occurrence containing actor, participation,
action, terminal-settlement, authority-residual, and cutoff atoms.  This
module owns their exact restriction mouths; M0/M2 generation remains in
`FreeStrategicProgram`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical
namespace Source

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

namespace FreeStrategicSyntax

inductive FreeClassicalAtom where
  | origin
  | actorEmission (player : Nat)
  | participationRelation (player : Nat)
  | actionContinuation (player strategy : Nat)
  | worldTerminal (profile : Nat)
  | worldTerminalSettlement (profile player : Nat) (value : ℚ)
  | authorityResidual (profile base : Nat) (value : ℚ)
  | cutoff (profile : Nat)
  deriving DecidableEq, Repr

def actorEvents (program : FreeStrategicSyntax) : List FreeClassicalAtom :=
  (List.finRange program.actorCount).map fun actor =>
    .actorEmission actor.val

def actorBoundaryAtom (program : FreeStrategicSyntax) : FreeClassicalAtom :=
  .actorEmission program.firstActorIndex.val

theorem actorBoundaryAtom_mem_actorEvents (program : FreeStrategicSyntax) :
    program.actorBoundaryAtom ∈ program.actorEvents := by
  unfold actorEvents actorBoundaryAtom
  apply List.mem_map.mpr
  exact ⟨program.firstActorIndex, by simp, rfl⟩

def participationEvents
    (program : FreeStrategicSyntax) : List FreeClassicalAtom :=
  (List.finRange program.playerCount).map fun player =>
    .participationRelation player.val

noncomputable def actionEvents
    (program : FreeStrategicSyntax) : List FreeClassicalAtom :=
  (Finset.univ : Finset program.FutureCode).toList.map fun action =>
    .actionContinuation action.1.val action.2.val

def actionAtom (program : FreeStrategicSyntax)
    (action : program.FutureCode) : FreeClassicalAtom :=
  .actionContinuation action.1.val action.2.val

theorem actionAtom_mem_actionEvents (program : FreeStrategicSyntax)
    (action : program.FutureCode) :
    program.actionAtom action ∈ program.actionEvents := by
  unfold actionEvents actionAtom
  apply List.mem_map.mpr
  exact ⟨action, by simp, rfl⟩

noncomputable def outcomeEvents
    (program : FreeStrategicSyntax) : List FreeClassicalAtom :=
  (Finset.univ : Finset program.CanonicalProfile).toList.flatMap fun profile =>
    if program.isWorldTerminal profile then
      .worldTerminal (program.profileIndex profile) ::
        (List.finRange program.playerCount).map fun player =>
          .worldTerminalSettlement (program.profileIndex profile) player.val
            (program.settlementValue profile player)
    else
      [.cutoff (program.profileIndex profile)]

def authorityAtom (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile)
    (base : program.AuthorityBase) : FreeClassicalAtom :=
  .authorityResidual (program.profileIndex profile) base.val
    (program.authorityResidual profile base)

noncomputable def authorityEvents
    (program : FreeStrategicSyntax) : List FreeClassicalAtom :=
  (Finset.univ : Finset program.CanonicalProfile).toList.flatMap fun profile =>
    if program.isWorldTerminal profile then
      (List.finRange (max program.playerCount 1)).map fun base =>
        program.authorityAtom profile base
    else
      []

theorem authorityAtom_mem_authorityEvents
    (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile)
    (base : program.AuthorityBase)
    (terminal : program.isWorldTerminal profile = true) :
    program.authorityAtom profile base ∈ program.authorityEvents := by
  unfold authorityEvents
  apply List.mem_flatMap.mpr
  refine ⟨profile, by simp, ?_⟩
  rw [terminal]
  apply List.mem_map.mpr
  exact ⟨base, by simp, rfl⟩

def worldTerminalAtom (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile) : FreeClassicalAtom :=
  .worldTerminal (program.profileIndex profile)

def cutoffAtom (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile) : FreeClassicalAtom :=
  .cutoff (program.profileIndex profile)

theorem worldTerminalAtom_mem_outcomeEvents
    (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile)
    (terminal : program.isWorldTerminal profile = true) :
    program.worldTerminalAtom profile ∈ program.outcomeEvents := by
  unfold outcomeEvents
  apply List.mem_flatMap.mpr
  refine ⟨profile, by simp, ?_⟩
  rw [terminal]
  exact List.mem_cons_self

theorem cutoffAtom_mem_outcomeEvents
    (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile)
    (cutoff : program.isWorldTerminal profile = false) :
    program.cutoffAtom profile ∈ program.outcomeEvents := by
  unfold outcomeEvents
  apply List.mem_flatMap.mpr
  refine ⟨profile, by simp, ?_⟩
  simp [cutoffAtom, cutoff]

noncomputable def programEvents
    (program : FreeStrategicSyntax) : List FreeClassicalAtom :=
  program.actorEvents ++ program.participationEvents ++
    program.actionEvents ++ program.outcomeEvents ++ program.authorityEvents

def branchesOfList : List FreeClassicalAtom →
    AccountedBranches FreeClassicalAtom
  | [] => .nil
  | event :: remaining =>
      .cons (.zero event) (branchesOfList remaining)

@[simp] theorem traceBranches_branchesOfList
    (events : List FreeClassicalAtom) :
    RootedAccountedUnfolding.traceBranches (branchesOfList events) =
      events := by
  induction events with
  | nil => rfl
  | cons event remaining ih =>
      change event ::
        RootedAccountedUnfolding.traceBranches
          (branchesOfList remaining) = event :: remaining
      rw [ih]

noncomputable def occurrence (program : FreeStrategicSyntax) :
    RootedAccountedUnfolding FreeClassicalAtom :=
  .occur .origin (branchesOfList program.programEvents)

@[simp] theorem occurrence_trace (program : FreeStrategicSyntax) :
    program.occurrence.trace = .origin :: program.programEvents := by
  change FreeClassicalAtom.origin ::
      RootedAccountedUnfolding.traceBranches
        (branchesOfList program.programEvents) =
    FreeClassicalAtom.origin :: program.programEvents
  rw [traceBranches_branchesOfList]

@[simp] theorem occurrence_trace_getElem?_zero
    (program : FreeStrategicSyntax) :
    program.occurrence.trace[0]? = some .origin := by
  rw [program.occurrence_trace]
  rfl

@[simp] theorem occurrence_trace_getElem?_one
    (program : FreeStrategicSyntax) :
    program.occurrence.trace[1]? = some program.actorBoundaryAtom := by
  rw [program.occurrence_trace]
  have oneLe : 1 ≤ program.actorCount :=
    (by decide : 1 ≤ 2).trans (Nat.le_max_right _ _)
  have countEq : program.actorCount = program.actorCount - 1 + 1 :=
    (Nat.sub_add_cancel oneLe).symm
  unfold programEvents actorEvents
  rw [countEq, List.finRange_succ]
  rfl

theorem event_mem_trace (program : FreeStrategicSyntax)
    {event : FreeClassicalAtom} (member : event ∈ program.programEvents) :
    event ∈ program.occurrence.trace := by
  rw [program.occurrence_trace]
  exact List.mem_cons_of_mem _ member

theorem actionAtom_mem_trace (program : FreeStrategicSyntax)
    (action : program.FutureCode) :
    program.actionAtom action ∈ program.occurrence.trace := by
  apply program.event_mem_trace
  simp only [programEvents, List.mem_append]
  exact Or.inl (Or.inl (Or.inr
    (program.actionAtom_mem_actionEvents action)))

theorem actorBoundaryAtom_mem_trace (program : FreeStrategicSyntax) :
    program.actorBoundaryAtom ∈ program.occurrence.trace := by
  apply program.event_mem_trace
  simp only [programEvents, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl
    (program.actorBoundaryAtom_mem_actorEvents))))

theorem worldTerminalAtom_mem_trace
    (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile)
    (terminal : program.isWorldTerminal profile = true) :
    program.worldTerminalAtom profile ∈ program.occurrence.trace := by
  apply program.event_mem_trace
  simp only [programEvents, List.mem_append]
  exact Or.inl (Or.inr
    (program.worldTerminalAtom_mem_outcomeEvents profile terminal))

theorem cutoffAtom_mem_trace
    (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile)
    (cutoff : program.isWorldTerminal profile = false) :
    program.cutoffAtom profile ∈ program.occurrence.trace := by
  apply program.event_mem_trace
  simp only [programEvents, List.mem_append]
  exact Or.inl (Or.inr
    (program.cutoffAtom_mem_outcomeEvents profile cutoff))

theorem authorityAtom_mem_trace
    (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile)
    (base : program.AuthorityBase)
    (terminal : program.isWorldTerminal profile = true) :
    program.authorityAtom profile base ∈ program.occurrence.trace := by
  apply program.event_mem_trace
  simp only [programEvents, List.mem_append]
  exact Or.inr
    (program.authorityAtom_mem_authorityEvents profile base terminal)

def occurrenceOf (program : FreeStrategicSyntax) :
    Unit → RootedAccountedUnfolding FreeClassicalAtom :=
  fun _ => program.occurrence

def processGame (program : FreeStrategicSyntax) :
    SaturationMonoid.ProcessGame program.occurrenceOf :=
  ⟨()⟩

theorem occurrence_root (program : FreeStrategicSyntax) :
    program.occurrence.root = .origin :=
  rfl

theorem origin_mem_trace (program : FreeStrategicSyntax) :
    FreeClassicalAtom.origin ∈ program.occurrence.trace := by
  exact RootedAccountedUnfolding.root_mem_trace program.occurrence

def actionSeedAt (program : FreeStrategicSyntax)
    (_source : Unit) (state : FreeClassicalAtom)
    (action : program.FutureCode) : Prop :=
  state = program.actionAtom action

abbrev ExactActionRestriction (program : FreeStrategicSyntax) :=
  SourceSeed program.occurrenceOf program.FutureCode
    (program.actionSeedAt) ()

def exactActionRestriction (program : FreeStrategicSyntax)
    (action : program.FutureCode) : program.ExactActionRestriction :=
  ⟨action, program.actionAtom action, program.actionAtom_mem_trace action, rfl⟩

@[simp] theorem exactActionRestriction_value
    (program : FreeStrategicSyntax) (action : program.FutureCode) :
    (program.exactActionRestriction action).1 = action :=
  rfl

def WorldTerminalProfile (program : FreeStrategicSyntax) :=
  { profile : program.CanonicalProfile //
    program.isWorldTerminal profile = true }

def CutoffProfile (program : FreeStrategicSyntax) :=
  { profile : program.CanonicalProfile //
    program.isWorldTerminal profile = false }

def worldTerminalSeedAt (program : FreeStrategicSyntax)
    (_source : Unit) (state : FreeClassicalAtom)
    (profile : program.WorldTerminalProfile) : Prop :=
  state = program.worldTerminalAtom profile.1

def cutoffSeedAt (program : FreeStrategicSyntax)
    (_source : Unit) (state : FreeClassicalAtom)
    (profile : program.CutoffProfile) : Prop :=
  state = program.cutoffAtom profile.1

abbrev ExactWorldTerminalRestriction (program : FreeStrategicSyntax) :=
  SourceSeed program.occurrenceOf program.WorldTerminalProfile
    program.worldTerminalSeedAt ()

abbrev ExactCutoffRestriction (program : FreeStrategicSyntax) :=
  SourceSeed program.occurrenceOf program.CutoffProfile
    program.cutoffSeedAt ()

def exactWorldTerminalRestriction (program : FreeStrategicSyntax)
    (profile : program.WorldTerminalProfile) :
    program.ExactWorldTerminalRestriction :=
  ⟨profile, program.worldTerminalAtom profile.1,
    program.worldTerminalAtom_mem_trace profile.1 profile.2, rfl⟩

def exactCutoffRestriction (program : FreeStrategicSyntax)
    (profile : program.CutoffProfile) : program.ExactCutoffRestriction :=
  ⟨profile, program.cutoffAtom profile.1,
    program.cutoffAtom_mem_trace profile.1 profile.2, rfl⟩

end FreeStrategicSyntax
end
end Source
end Classical
end Society
end ProcessGame
end SaturationMonoid
