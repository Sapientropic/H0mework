import H0mework.Realization.Relations.FintypeDerivation
import Mathlib

/-!
# Raw source dynamics and a first physical failure basis

This module deliberately stays below `SU7ActiveCell` and
`SU7ThinSourceFeasibleDatum`.  Those types already contain post-P950 witness
data and therefore cannot serve as a pre-holonomy source producer.

`RawSourceDynamics` stores only finite root/successor operations, a selected
current state, and two readouts.  Reachability, energy monotonicity, graph
confluence, and handle faithfulness are computed laws.  A local admissibility
slice and its four-coordinate failure classification are then derived from
those laws, followed by concrete only-one-fails graph models.

The energy law is intentionally called source-energy monotonicity.  No theorem
currently identifies it with the target phrase "authority monotonicity".
Likewise, this generic raw carrier is not yet the missing concrete SU(7)
representation/crystal/incidence producer.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uState uHandle uEnergy

/-- Operations available before any source-discipline certificate is proved. -/
structure RawSourceDynamics
    (State : Type uState) (Handle : Type uHandle) (Energy : Type uEnergy) where
  roots : List State
  successors : State → List State
  current : Option State
  handleOf : State → Handle
  energyOf : State → Energy

namespace RawSourceDynamics

variable {State : Type uState} {Handle : Type uHandle} {Energy : Type uEnergy}

def Step (S : RawSourceDynamics State Handle Energy) (x y : State) : Prop :=
  y ∈ S.successors x

def ReachableFrom
    (S : RawSourceDynamics State Handle Energy) (x y : State) : Prop :=
  Relation.ReflTransGen S.Step x y

def Reachable
    (S : RawSourceDynamics State Handle Energy) (y : State) : Prop :=
  ∃ root : State, root ∈ S.roots ∧ S.ReachableFrom root y

/-- The current selector returned an actual state reachable from a raw root. -/
def CurrentSourceReachable
    (S : RawSourceDynamics State Handle Energy) : Prop :=
  ∃ current : State, S.current = some current ∧ S.Reachable current

/-- Every native source step is non-increasing in its own energy readout. -/
def SourceEnergyMonotone
    [Preorder Energy]
    (S : RawSourceDynamics State Handle Energy) : Prop :=
  ∀ x y : State, S.Step x y → S.energyOf y ≤ S.energyOf x

def Joinable
    (S : RawSourceDynamics State Handle Energy) (x y : State) : Prop :=
  ∃ z : State, S.ReachableFrom x z ∧ S.ReachableFrom y z

/-- Any two states produced from the same declared root can be joined by the
same successor dynamics. -/
def GraphConfluent
    (S : RawSourceDynamics State Handle Energy) : Prop :=
  ∀ root : State, root ∈ S.roots →
    ∀ x y : State,
      S.ReachableFrom root x → S.ReachableFrom root y → S.Joinable x y

/-- Distinct reachable source states retain distinct physical handles. -/
def HandleFaithfulOnReachable
    (S : RawSourceDynamics State Handle Energy) : Prop :=
  ∀ x y : State,
    S.Reachable x → S.Reachable y → S.handleOf x = S.handleOf y → x = y

/-- A local source-dynamics admissibility slice derived only from raw
operations.  This is not the final cross-subsystem `PhysicalAdmissibility`. -/
def SourceDynamicsAdmissible
    [Preorder Energy]
    (S : RawSourceDynamics State Handle Energy) : Prop :=
  S.CurrentSourceReachable ∧
    S.SourceEnergyMonotone ∧
      S.GraphConfluent ∧
        S.HandleFaithfulOnReachable

/-- Coordinates discovered by normalizing the four native source laws above;
they are not fields of `RawSourceDynamics`. -/
inductive SourceDynamicsCoordinate where
  | currentReachability
  | sourceEnergyMonotonicity
  | graphConfluence
  | handleFaithfulness
  deriving DecidableEq, Repr, FintypeViaProxy

def CoordinateHolds
    [Preorder Energy]
    (S : RawSourceDynamics State Handle Energy) :
    SourceDynamicsCoordinate → Prop
  | .currentReachability => S.CurrentSourceReachable
  | .sourceEnergyMonotonicity => S.SourceEnergyMonotone
  | .graphConfluence => S.GraphConfluent
  | .handleFaithfulness => S.HandleFaithfulOnReachable

theorem sourceDynamicsAdmissible_iff_all_coordinates
    [Preorder Energy]
    (S : RawSourceDynamics State Handle Energy) :
    S.SourceDynamicsAdmissible ↔ ∀ c, S.CoordinateHolds c := by
  constructor
  · rintro ⟨hcurrent, henergy, hconfluent, hfaithful⟩ c
    cases c with
    | currentReachability => exact hcurrent
    | sourceEnergyMonotonicity => exact henergy
    | graphConfluence => exact hconfluent
    | handleFaithfulness => exact hfaithful
  · intro hall
    exact ⟨hall .currentReachability, hall .sourceEnergyMonotonicity,
      hall .graphConfluence, hall .handleFaithfulness⟩

/-- Local soundness/completeness: failure of the raw source slice is exactly
failure of at least one derived coordinate. -/
theorem not_sourceDynamicsAdmissible_iff_exists_failed_coordinate
    [Preorder Energy]
    (S : RawSourceDynamics State Handle Energy) :
    ¬ S.SourceDynamicsAdmissible ↔ ∃ c, ¬ S.CoordinateHolds c := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    push Not at hnone
    exact hnot (S.sourceDynamicsAdmissible_iff_all_coordinates.mpr hnone)
  · rintro ⟨c, hc⟩ hadmissible
    exact hc (S.sourceDynamicsAdmissible_iff_all_coordinates.mp hadmissible c)

def OnlyFails
    [Preorder Energy]
    (S : RawSourceDynamics State Handle Energy)
    (failed : SourceDynamicsCoordinate) : Prop :=
  ¬ S.CoordinateHolds failed ∧
    ∀ c, c ≠ failed → S.CoordinateHolds c

theorem reachableFrom_eq_of_no_steps
    (S : RawSourceDynamics State Handle Energy)
    (hno : ∀ x y : State, ¬ S.Step x y)
    {x y : State} (hxy : S.ReachableFrom x y) : x = y := by
  induction hxy with
  | refl => rfl
  | tail _ hstep _ => exact (hno _ _ hstep).elim

theorem reachableFrom_eq_of_no_outgoing
    (S : RawSourceDynamics State Handle Energy)
    {x y : State} (hno : ∀ z : State, ¬ S.Step x z)
    (hxy : S.ReachableFrom x y) : x = y := by
  induction hxy with
  | refl => rfl
  | tail _ hstep ih =>
      subst_vars
      exact (hno _ hstep).elim

/-! ## Singleton-carrier collapse boundary -/

/-- A one-state carrier makes source-energy monotonicity automatic.  This is
why wrapping one already-produced current-shell datum as the entire source
state cannot test the energy coordinate. -/
theorem sourceEnergyMonotone_of_subsingleton
    [Preorder Energy] [Subsingleton State]
    (S : RawSourceDynamics State Handle Energy) :
    S.SourceEnergyMonotone := by
  intro x y hstep
  have hxy : x = y := Subsingleton.elim x y
  subst y
  exact le_rfl

/-- A one-state carrier also makes every source fork trivially joinable. -/
theorem graphConfluent_of_subsingleton
    [Subsingleton State]
    (S : RawSourceDynamics State Handle Energy) :
    S.GraphConfluent := by
  intro root hroot x y hx hy
  have hxy : x = y := Subsingleton.elim x y
  subst y
  exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- Handle faithfulness has no separating content on a one-state carrier. -/
theorem handleFaithfulOnReachable_of_subsingleton
    [Subsingleton State]
    (S : RawSourceDynamics State Handle Energy) :
    S.HandleFaithfulOnReachable := by
  intro x y hx hy hhandle
  exact Subsingleton.elim x y

/-- On a subsingleton source carrier, the nominal four-law admissibility
predicate collapses exactly to current reachability.  In particular, a
singleton wrapper around one `SU7ThinSourceFeasibleDatum` cannot be used to
discover or validate the other three source-dynamics coordinates. -/
theorem sourceDynamicsAdmissible_iff_currentReachable_of_subsingleton
    [Preorder Energy] [Subsingleton State]
    (S : RawSourceDynamics State Handle Energy) :
    S.SourceDynamicsAdmissible ↔ S.CurrentSourceReachable := by
  constructor
  · exact fun hadmissible => hadmissible.1
  · intro hcurrent
    exact ⟨hcurrent, S.sourceEnergyMonotone_of_subsingleton,
      S.graphConfluent_of_subsingleton,
      S.handleFaithfulOnReachable_of_subsingleton⟩

/-! ## Concrete only-one-fails source graphs -/

namespace RawSourceDynamicsToy

inductive ToyState where
  | root
  | left
  | right
  | join
  | isolated
  deriving DecidableEq, Repr

open ToyState

def allStates : List ToyState :=
  [root, left, right, join, isolated]

def noSuccessors : ToyState → List ToyState :=
  fun _ => []

def universalSuccessors : ToyState → List ToyState :=
  fun _ => allStates

abbrev System := RawSourceDynamics ToyState ToyState Nat

/-- A nontrivial positive reference: every state is a declared root, the
dynamics is stationary, and handles are identity readouts. -/
def admissibleSystem : System where
  roots := allStates
  successors := noSuccessors
  current := some root
  handleOf := id
  energyOf := fun _ => 0

/-- The selected state is isolated from the only root. -/
def reachabilityFailureSystem : System where
  roots := [root]
  successors := noSuccessors
  current := some isolated
  handleOf := id
  energyOf := fun _ => 0

/-- Universal transitions are confluent, but one step raises source energy. -/
def energyFailureSystem : System where
  roots := [root]
  successors := universalSuccessors
  current := some root
  handleOf := id
  energyOf
    | root => 0
    | _ => 1

/-- A genuine fork with two terminal, non-joinable descendants. -/
def confluenceFailureSystem : System where
  roots := [root]
  successors
    | root => [left, right]
    | _ => []
  current := some root
  handleOf := id
  energyOf := fun _ => 0

/-- Every state exists as a root, but all physical handles collapse. -/
def handleFailureSystem : System where
  roots := allStates
  successors := noSuccessors
  current := some root
  handleOf := fun _ => root
  energyOf := fun _ => 0

theorem noSuccessors_has_no_steps
    (S : System) (hsuccessors : S.successors = noSuccessors) :
    ∀ x y : ToyState, ¬ S.Step x y := by
  intro x y
  simp [Step, hsuccessors, noSuccessors]

theorem admissibleSystem_current :
    admissibleSystem.CurrentSourceReachable := by
  exact ⟨root, rfl, root, by simp [admissibleSystem, allStates],
    Relation.ReflTransGen.refl⟩

theorem admissibleSystem_energy :
    admissibleSystem.SourceEnergyMonotone := by
  intro x y hstep
  simp [Step, admissibleSystem, noSuccessors] at hstep

theorem admissibleSystem_confluent :
    admissibleSystem.GraphConfluent := by
  intro declaredRoot hroot x y hx hy
  have hno := noSuccessors_has_no_steps admissibleSystem rfl
  have hx' := admissibleSystem.reachableFrom_eq_of_no_steps hno hx
  have hy' := admissibleSystem.reachableFrom_eq_of_no_steps hno hy
  subst x
  subst y
  exact ⟨declaredRoot, Relation.ReflTransGen.refl,
    Relation.ReflTransGen.refl⟩

theorem admissibleSystem_faithful :
    admissibleSystem.HandleFaithfulOnReachable := by
  intro x y hx hy hhandle
  exact hhandle

theorem admissibleSystem_admissible :
    admissibleSystem.SourceDynamicsAdmissible :=
  ⟨admissibleSystem_current, admissibleSystem_energy,
    admissibleSystem_confluent, admissibleSystem_faithful⟩

theorem reachabilityFailureSystem_not_current :
    ¬ reachabilityFailureSystem.CurrentSourceReachable := by
  rintro ⟨current, hcurrent, declaredRoot, hroot, hreach⟩
  have hcurrent' : current = isolated := by
    simpa [reachabilityFailureSystem] using Option.some.inj hcurrent.symm
  have hroot' : declaredRoot = root := by
    simpa [reachabilityFailureSystem] using hroot
  subst current
  subst declaredRoot
  have hno := noSuccessors_has_no_steps reachabilityFailureSystem rfl
  have : root = isolated :=
    reachabilityFailureSystem.reachableFrom_eq_of_no_steps hno hreach
  cases this

theorem reachabilityFailureSystem_energy :
    reachabilityFailureSystem.SourceEnergyMonotone := by
  intro x y hstep
  simp [Step, reachabilityFailureSystem, noSuccessors] at hstep

theorem reachabilityFailureSystem_confluent :
    reachabilityFailureSystem.GraphConfluent := by
  intro declaredRoot hroot x y hx hy
  have hno := noSuccessors_has_no_steps reachabilityFailureSystem rfl
  have hx' :=
    reachabilityFailureSystem.reachableFrom_eq_of_no_steps hno hx
  have hy' :=
    reachabilityFailureSystem.reachableFrom_eq_of_no_steps hno hy
  subst x
  subst y
  exact ⟨declaredRoot, Relation.ReflTransGen.refl,
    Relation.ReflTransGen.refl⟩

theorem reachabilityFailureSystem_faithful :
    reachabilityFailureSystem.HandleFaithfulOnReachable := by
  intro x y hx hy hhandle
  exact hhandle

theorem energyFailureSystem_current :
    energyFailureSystem.CurrentSourceReachable := by
  exact ⟨root, rfl, root, by simp [energyFailureSystem],
    Relation.ReflTransGen.refl⟩

theorem energyFailureSystem_not_energy :
    ¬ energyFailureSystem.SourceEnergyMonotone := by
  intro hmonotone
  have hstep : energyFailureSystem.Step root left := by
    simp [Step, energyFailureSystem, universalSuccessors, allStates]
  have hle := hmonotone root left hstep
  norm_num [energyFailureSystem] at hle

theorem energyFailureSystem_confluent :
    energyFailureSystem.GraphConfluent := by
  intro declaredRoot hroot x y hx hy
  refine ⟨root, ?_, ?_⟩
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (by
      simp [Step, energyFailureSystem, universalSuccessors, allStates])
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (by
      simp [Step, energyFailureSystem, universalSuccessors, allStates])

theorem energyFailureSystem_faithful :
    energyFailureSystem.HandleFaithfulOnReachable := by
  intro x y hx hy hhandle
  exact hhandle

theorem confluenceFailureSystem_current :
    confluenceFailureSystem.CurrentSourceReachable := by
  exact ⟨root, rfl, root, by simp [confluenceFailureSystem],
    Relation.ReflTransGen.refl⟩

theorem confluenceFailureSystem_energy :
    confluenceFailureSystem.SourceEnergyMonotone := by
  intro x y hstep
  simp [confluenceFailureSystem]

theorem confluenceFailureSystem_not_confluent :
    ¬ confluenceFailureSystem.GraphConfluent := by
  intro hconfluent
  have hroot : root ∈ confluenceFailureSystem.roots := by
    simp [confluenceFailureSystem]
  have hleft : confluenceFailureSystem.ReachableFrom root left :=
    Relation.ReflTransGen.tail Relation.ReflTransGen.refl (by
      simp [Step, confluenceFailureSystem])
  have hright : confluenceFailureSystem.ReachableFrom root right :=
    Relation.ReflTransGen.tail Relation.ReflTransGen.refl (by
      simp [Step, confluenceFailureSystem])
  rcases hconfluent root hroot left right hleft hright with
    ⟨z, hleftZ, hrightZ⟩
  have hnoLeft : ∀ z, ¬ confluenceFailureSystem.Step left z := by
    intro next
    simp [Step, confluenceFailureSystem]
  have hnoRight : ∀ z, ¬ confluenceFailureSystem.Step right z := by
    intro next
    simp [Step, confluenceFailureSystem]
  have hzLeft : z = left :=
    (confluenceFailureSystem.reachableFrom_eq_of_no_outgoing
      hnoLeft hleftZ).symm
  have hzRight : z = right :=
    (confluenceFailureSystem.reachableFrom_eq_of_no_outgoing
      hnoRight hrightZ).symm
  have : left = right := hzLeft.symm.trans hzRight
  cases this

theorem confluenceFailureSystem_faithful :
    confluenceFailureSystem.HandleFaithfulOnReachable := by
  intro x y hx hy hhandle
  exact hhandle

theorem handleFailureSystem_current :
    handleFailureSystem.CurrentSourceReachable := by
  exact ⟨root, rfl, root, by simp [handleFailureSystem, allStates],
    Relation.ReflTransGen.refl⟩

theorem handleFailureSystem_energy :
    handleFailureSystem.SourceEnergyMonotone := by
  intro x y hstep
  simp [Step, handleFailureSystem, noSuccessors] at hstep

theorem handleFailureSystem_confluent :
    handleFailureSystem.GraphConfluent := by
  intro declaredRoot hroot x y hx hy
  have hno := noSuccessors_has_no_steps handleFailureSystem rfl
  have hx' := handleFailureSystem.reachableFrom_eq_of_no_steps hno hx
  have hy' := handleFailureSystem.reachableFrom_eq_of_no_steps hno hy
  subst x
  subst y
  exact ⟨declaredRoot, Relation.ReflTransGen.refl,
    Relation.ReflTransGen.refl⟩

theorem handleFailureSystem_not_faithful :
    ¬ handleFailureSystem.HandleFaithfulOnReachable := by
  intro hfaithful
  have hroot : handleFailureSystem.Reachable root :=
    ⟨root, by simp [handleFailureSystem, allStates],
      Relation.ReflTransGen.refl⟩
  have hleft : handleFailureSystem.Reachable left :=
    ⟨left, by simp [handleFailureSystem, allStates],
      Relation.ReflTransGen.refl⟩
  have : root = left := hfaithful root left hroot hleft rfl
  cases this

theorem reachabilityFailureSystem_onlyFails :
    reachabilityFailureSystem.OnlyFails .currentReachability := by
  refine ⟨reachabilityFailureSystem_not_current, ?_⟩
  intro c hc
  cases c with
  | currentReachability => exact (hc rfl).elim
  | sourceEnergyMonotonicity => exact reachabilityFailureSystem_energy
  | graphConfluence => exact reachabilityFailureSystem_confluent
  | handleFaithfulness => exact reachabilityFailureSystem_faithful

theorem energyFailureSystem_onlyFails :
    energyFailureSystem.OnlyFails .sourceEnergyMonotonicity := by
  refine ⟨energyFailureSystem_not_energy, ?_⟩
  intro c hc
  cases c with
  | currentReachability => exact energyFailureSystem_current
  | sourceEnergyMonotonicity => exact (hc rfl).elim
  | graphConfluence => exact energyFailureSystem_confluent
  | handleFaithfulness => exact energyFailureSystem_faithful

theorem confluenceFailureSystem_onlyFails :
    confluenceFailureSystem.OnlyFails .graphConfluence := by
  refine ⟨confluenceFailureSystem_not_confluent, ?_⟩
  intro c hc
  cases c with
  | currentReachability => exact confluenceFailureSystem_current
  | sourceEnergyMonotonicity => exact confluenceFailureSystem_energy
  | graphConfluence => exact (hc rfl).elim
  | handleFaithfulness => exact confluenceFailureSystem_faithful

theorem handleFailureSystem_onlyFails :
    handleFailureSystem.OnlyFails .handleFaithfulness := by
  refine ⟨handleFailureSystem_not_faithful, ?_⟩
  intro c hc
  cases c with
  | currentReachability => exact handleFailureSystem_current
  | sourceEnergyMonotonicity => exact handleFailureSystem_energy
  | graphConfluence => exact handleFailureSystem_confluent
  | handleFaithfulness => exact (hc rfl).elim

/-- Local irreducibility: every derived source coordinate has a concrete
finite graph that fails it and satisfies the other three. -/
theorem every_sourceDynamicsCoordinate_has_only_one_failure_model
    (c : SourceDynamicsCoordinate) :
    ∃ S : System, S.OnlyFails c := by
  cases c with
  | currentReachability =>
      exact ⟨reachabilityFailureSystem,
        reachabilityFailureSystem_onlyFails⟩
  | sourceEnergyMonotonicity =>
      exact ⟨energyFailureSystem, energyFailureSystem_onlyFails⟩
  | graphConfluence =>
      exact ⟨confluenceFailureSystem, confluenceFailureSystem_onlyFails⟩
  | handleFaithfulness =>
      exact ⟨handleFailureSystem, handleFailureSystem_onlyFails⟩

end RawSourceDynamicsToy

end RawSourceDynamics
end PhysicsCore
end SaturationMonoid
