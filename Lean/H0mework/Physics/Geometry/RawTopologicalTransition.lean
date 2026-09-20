import H0mework.Realization.Relations.FintypeDerivation
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Order
import H0mework.Realization.Descent.P260

/-!
# Raw topological transition operations

`TopologicalPrincipalCover` is already proof-carrying: its chart family is
accompanied by openness and coverage fields.  That is useful downstream, but
it cannot be the raw producer surface for a reconstruction of physical
admissibility.

This module therefore starts with only a chart-family operation and a
group-valued transition operation.  Chart openness, cover completeness,
continuity on overlaps, and flatness on triple overlaps are four computed
laws.  No cover, cocycle, compatibility, or final-admissibility proof is stored
in the raw state.

Four systems on one fixed carrier isolate the four failures.  The continuity
countermodel uses the Sierpinski topology on `Prop`, so it is a genuinely
topological failure rather than a truth-field assignment.  Finally, an adapter
shows that P260 exact transitions from continuous potentials land in the
positive region.
-/

namespace SaturationMonoid
namespace PhysicsCore

open AffineRelaxation

universe uBase uIndex uGroup

/-- Operations available before any topological-cover or cocycle certificate
has been proved. -/
structure RawTopologicalTransition
    (Base : Type uBase) (Index : Type uIndex) (Gauge : Type uGroup)
    [TopologicalSpace Base] [TopologicalSpace Gauge] [Group Gauge] where
  chart : Index → Set Base
  transition : Index → Index → Base → Gauge

namespace RawTopologicalTransition

variable {Base : Type uBase} {Index : Type uIndex} {Gauge : Type uGroup}
variable [TopologicalSpace Base] [TopologicalSpace Gauge] [Group Gauge]

def overlap
    (S : RawTopologicalTransition Base Index Gauge) (i j : Index) :
    Set Base :=
  S.chart i ∩ S.chart j

def tripleOverlap
    (S : RawTopologicalTransition Base Index Gauge) (i j k : Index) :
    Set Base :=
  S.chart i ∩ (S.chart j ∩ S.chart k)

/-- Every raw chart is open. -/
def ChartsOpen (S : RawTopologicalTransition Base Index Gauge) : Prop :=
  ∀ i, IsOpen (S.chart i)

/-- The raw chart family actually covers the base. -/
def ChartsCover (S : RawTopologicalTransition Base Index Gauge) : Prop :=
  ∀ x, ∃ i, x ∈ S.chart i

/-- Every transition operation is continuous on its pairwise overlap. -/
def TransitionsContinuous
    (S : RawTopologicalTransition Base Index Gauge) : Prop :=
  ∀ i j, ContinuousOn (S.transition i j) (S.overlap i j)

/-- Transition composition is path-independent on triple overlaps. -/
def TransitionFlat
    (S : RawTopologicalTransition Base Index Gauge) : Prop :=
  ∀ i j k x, x ∈ S.tripleOverlap i j k →
    S.transition j k x * S.transition i j x = S.transition i k x

def TopologicalTransitionAdmissible
    (S : RawTopologicalTransition Base Index Gauge) : Prop :=
  S.ChartsOpen ∧ S.ChartsCover ∧
    S.TransitionsContinuous ∧ S.TransitionFlat

inductive TopologicalTransitionCoordinate where
  | chartOpenness
  | coverCompleteness
  | transitionContinuity
  | transitionFlatness
  deriving DecidableEq, Repr, FintypeViaProxy

def CoordinateHolds
    (S : RawTopologicalTransition Base Index Gauge) :
    TopologicalTransitionCoordinate → Prop
  | .chartOpenness => S.ChartsOpen
  | .coverCompleteness => S.ChartsCover
  | .transitionContinuity => S.TransitionsContinuous
  | .transitionFlatness => S.TransitionFlat

theorem topologicalTransitionAdmissible_iff_all_coordinates
    (S : RawTopologicalTransition Base Index Gauge) :
    S.TopologicalTransitionAdmissible ↔ ∀ c, S.CoordinateHolds c := by
  constructor
  · rintro ⟨hopen, hcover, hcontinuous, hflat⟩ c
    cases c with
    | chartOpenness => exact hopen
    | coverCompleteness => exact hcover
    | transitionContinuity => exact hcontinuous
    | transitionFlatness => exact hflat
  · intro hall
    exact ⟨hall .chartOpenness, hall .coverCompleteness,
      hall .transitionContinuity, hall .transitionFlatness⟩

theorem not_topologicalTransitionAdmissible_iff_exists_failed_coordinate
    (S : RawTopologicalTransition Base Index Gauge) :
    ¬ S.TopologicalTransitionAdmissible ↔
      ∃ c, ¬ S.CoordinateHolds c := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    push Not at hnone
    exact hnot
      (S.topologicalTransitionAdmissible_iff_all_coordinates.mpr hnone)
  · rintro ⟨c, hc⟩ hadmissible
    exact hc
      (S.topologicalTransitionAdmissible_iff_all_coordinates.mp
        hadmissible c)

def OnlyFails
    (S : RawTopologicalTransition Base Index Gauge)
    (failed : TopologicalTransitionCoordinate) : Prop :=
  ¬ S.CoordinateHolds failed ∧
    ∀ c, c ≠ failed → S.CoordinateHolds c

/-! ## P260 theorem-producing adapter -/

/-- Forget the proof fields of a P260 cover after using its operations to
build a raw transition system. -/
def ofTopologicalPrincipalCover
    (C : TopologicalPrincipalCover Base Index)
    (g : Index → Index → Base → Gauge) :
    RawTopologicalTransition Base Index Gauge where
  chart := C.U
  transition := g

theorem ofTopologicalPrincipalCover_chartsOpen
    (C : TopologicalPrincipalCover Base Index)
    (g : Index → Index → Base → Gauge) :
    (ofTopologicalPrincipalCover C g).ChartsOpen :=
  C.isOpen_U

theorem ofTopologicalPrincipalCover_chartsCover
    (C : TopologicalPrincipalCover Base Index)
    (g : Index → Index → Base → Gauge) :
    (ofTopologicalPrincipalCover C g).ChartsCover :=
  C.covers

theorem ofTopologicalPrincipalCover_transitionsContinuous
    (C : TopologicalPrincipalCover Base Index)
    (g : Index → Index → Base → Gauge)
    (hcontinuous : ContinuousOnPrincipalTransitions C g) :
    (ofTopologicalPrincipalCover C g).TransitionsContinuous :=
  hcontinuous

theorem ofTopologicalPrincipalCover_transitionFlat
    (C : TopologicalPrincipalCover Base Index)
    (g : Index → Index → Base → Gauge)
    (hflat : TopologicalPrincipalFlatOn C g) :
    (ofTopologicalPrincipalCover C g).TransitionFlat :=
  hflat

variable [ContinuousMul Gauge] [ContinuousInv Gauge]

/-- P260 exact transitions from continuous local potentials satisfy all four
raw topological-transition laws. -/
theorem exactTransition_admissible
    (C : TopologicalPrincipalCover Base Index)
    (potential : Index → Base → Gauge)
    (hpotential : ∀ i, Continuous (potential i)) :
    (ofTopologicalPrincipalCover C
      (topologicalPrincipalExactTransition potential)).TopologicalTransitionAdmissible :=
  ⟨ofTopologicalPrincipalCover_chartsOpen C _,
    ofTopologicalPrincipalCover_chartsCover C _,
    ofTopologicalPrincipalCover_transitionsContinuous C _
      (topologicalPrincipalExactTransition_continuousOn
        C potential hpotential),
    ofTopologicalPrincipalCover_transitionFlat C _
      (topologicalPrincipalExactTransition_flatOn C potential)⟩

end RawTopologicalTransition

/-! ## Same-carrier independence models -/

namespace RawTopologicalTransitionToy

open RawTopologicalTransition

abbrev Gauge := Multiplicative (ZMod 2)
abbrev System := RawTopologicalTransition Prop Bool Gauge

/-- The nonidentity element of the two-element multiplicative wrapper. -/
def flip : Gauge := Multiplicative.ofAdd 1

theorem flip_ne_one : flip ≠ 1 := by
  decide

theorem one_ne_flip : (1 : Gauge) ≠ flip :=
  Ne.symm flip_ne_one

theorem flip_mul_self : flip * flip = 1 := by
  decide

theorem singleton_false_not_open :
    ¬ IsOpen ({False} : Set Prop) := by
  intro hopen
  have hmem : ({False} : Set Prop) ∈ nhds False :=
    hopen.mem_nhds (by simp)
  simp at hmem

noncomputable def discontinuousValue (p : Prop) : Gauge := by
  classical
  exact if p then 1 else flip

theorem discontinuousValue_not_continuous :
    ¬ Continuous discontinuousValue := by
  classical
  intro hcontinuous
  have hopen : IsOpen (discontinuousValue ⁻¹' ({flip} : Set Gauge)) :=
    (isOpen_discrete {flip}).preimage hcontinuous
  have heq :
      discontinuousValue ⁻¹' ({flip} : Set Gauge) =
        ({False} : Set Prop) := by
    ext p
    by_cases hp : p
    · simp [discontinuousValue, hp, one_ne_flip]
    · have hpFalse : p = False := propext ⟨fun h => (hp h).elim, False.elim⟩
      subst p
      simp [discontinuousValue]
  rw [heq] at hopen
  exact singleton_false_not_open hopen

noncomputable def discontinuousPotential : Bool → Prop → Gauge
  | false, _ => 1
  | true, p => discontinuousValue p

noncomputable def admissibleSystem : System where
  chart := fun _ => Set.univ
  transition := fun _ _ _ => 1

noncomputable def opennessFailureSystem : System where
  chart := fun i => if i then {False} else Set.univ
  transition := fun _ _ _ => 1

noncomputable def coverageFailureSystem : System where
  chart := fun _ => ∅
  transition := fun _ _ _ => 1

noncomputable def continuityFailureSystem : System where
  chart := fun _ => Set.univ
  transition :=
    topologicalPrincipalExactTransition discontinuousPotential

noncomputable def flatnessFailureSystem : System where
  chart := fun _ => Set.univ
  transition := fun _ _ _ => flip

theorem admissibleSystem_open : admissibleSystem.ChartsOpen := by
  intro i
  simp [admissibleSystem]

theorem admissibleSystem_cover : admissibleSystem.ChartsCover := by
  intro x
  exact ⟨false, by simp [admissibleSystem]⟩

theorem admissibleSystem_continuous :
    admissibleSystem.TransitionsContinuous := by
  intro i j
  exact continuousOn_const

theorem admissibleSystem_flat : admissibleSystem.TransitionFlat := by
  intro i j k x hx
  simp [admissibleSystem]

theorem admissibleSystem_admissible :
    admissibleSystem.TopologicalTransitionAdmissible :=
  ⟨admissibleSystem_open, admissibleSystem_cover,
    admissibleSystem_continuous, admissibleSystem_flat⟩

theorem opennessFailureSystem_not_open :
    ¬ opennessFailureSystem.ChartsOpen := by
  intro hopen
  have htrue := hopen true
  simp only [opennessFailureSystem, if_true] at htrue
  exact singleton_false_not_open htrue

theorem opennessFailureSystem_cover :
    opennessFailureSystem.ChartsCover := by
  intro x
  exact ⟨false, by simp [opennessFailureSystem]⟩

theorem opennessFailureSystem_continuous :
    opennessFailureSystem.TransitionsContinuous := by
  intro i j
  exact continuousOn_const

theorem opennessFailureSystem_flat :
    opennessFailureSystem.TransitionFlat := by
  intro i j k x hx
  simp [opennessFailureSystem]

theorem coverageFailureSystem_open :
    coverageFailureSystem.ChartsOpen := by
  intro i
  simp [coverageFailureSystem]

theorem coverageFailureSystem_not_cover :
    ¬ coverageFailureSystem.ChartsCover := by
  intro hcover
  rcases hcover False with ⟨i, hi⟩
  simp [coverageFailureSystem] at hi

theorem coverageFailureSystem_continuous :
    coverageFailureSystem.TransitionsContinuous := by
  intro i j
  exact continuousOn_const

theorem coverageFailureSystem_flat :
    coverageFailureSystem.TransitionFlat := by
  intro i j k x hx
  simp [tripleOverlap, coverageFailureSystem] at hx

theorem continuityFailureSystem_open :
    continuityFailureSystem.ChartsOpen := by
  intro i
  simp [continuityFailureSystem]

theorem continuityFailureSystem_cover :
    continuityFailureSystem.ChartsCover := by
  intro x
  exact ⟨false, by simp [continuityFailureSystem]⟩

theorem continuityFailureSystem_not_continuous :
    ¬ continuityFailureSystem.TransitionsContinuous := by
  intro hcontinuous
  have hfalseTrue := hcontinuous false true
  have hglobal :
      Continuous (continuityFailureSystem.transition false true) := by
    rw [← continuousOn_univ]
    simpa [overlap, continuityFailureSystem] using hfalseTrue
  have heq :
      continuityFailureSystem.transition false true =
        discontinuousValue := by
    funext p
    simp [continuityFailureSystem, discontinuousPotential,
      topologicalPrincipalExactTransition]
  rw [heq] at hglobal
  exact discontinuousValue_not_continuous hglobal

theorem continuityFailureSystem_flat :
    continuityFailureSystem.TransitionFlat := by
  intro i j k x hx
  simp [continuityFailureSystem, topologicalPrincipalExactTransition,
    mul_assoc]

theorem flatnessFailureSystem_open :
    flatnessFailureSystem.ChartsOpen := by
  intro i
  simp [flatnessFailureSystem]

theorem flatnessFailureSystem_cover :
    flatnessFailureSystem.ChartsCover := by
  intro x
  exact ⟨false, by simp [flatnessFailureSystem]⟩

theorem flatnessFailureSystem_continuous :
    flatnessFailureSystem.TransitionsContinuous := by
  intro i j
  exact continuousOn_const

theorem flatnessFailureSystem_not_flat :
    ¬ flatnessFailureSystem.TransitionFlat := by
  intro hflat
  have hvalue := hflat false false false True
    (by simp [tripleOverlap, flatnessFailureSystem])
  exact flip_ne_one (hvalue.symm.trans flip_mul_self)

theorem opennessFailureSystem_onlyFails :
    opennessFailureSystem.OnlyFails .chartOpenness := by
  refine ⟨opennessFailureSystem_not_open, ?_⟩
  intro c hc
  cases c with
  | chartOpenness => exact (hc rfl).elim
  | coverCompleteness => exact opennessFailureSystem_cover
  | transitionContinuity => exact opennessFailureSystem_continuous
  | transitionFlatness => exact opennessFailureSystem_flat

theorem coverageFailureSystem_onlyFails :
    coverageFailureSystem.OnlyFails .coverCompleteness := by
  refine ⟨coverageFailureSystem_not_cover, ?_⟩
  intro c hc
  cases c with
  | chartOpenness => exact coverageFailureSystem_open
  | coverCompleteness => exact (hc rfl).elim
  | transitionContinuity => exact coverageFailureSystem_continuous
  | transitionFlatness => exact coverageFailureSystem_flat

theorem continuityFailureSystem_onlyFails :
    continuityFailureSystem.OnlyFails .transitionContinuity := by
  refine ⟨continuityFailureSystem_not_continuous, ?_⟩
  intro c hc
  cases c with
  | chartOpenness => exact continuityFailureSystem_open
  | coverCompleteness => exact continuityFailureSystem_cover
  | transitionContinuity => exact (hc rfl).elim
  | transitionFlatness => exact continuityFailureSystem_flat

theorem flatnessFailureSystem_onlyFails :
    flatnessFailureSystem.OnlyFails .transitionFlatness := by
  refine ⟨flatnessFailureSystem_not_flat, ?_⟩
  intro c hc
  cases c with
  | chartOpenness => exact flatnessFailureSystem_open
  | coverCompleteness => exact flatnessFailureSystem_cover
  | transitionContinuity => exact flatnessFailureSystem_continuous
  | transitionFlatness => exact (hc rfl).elim

theorem every_coordinate_has_only_one_failure_model
    (c : TopologicalTransitionCoordinate) :
    ∃ S : System, S.OnlyFails c := by
  cases c with
  | chartOpenness =>
      exact ⟨opennessFailureSystem, opennessFailureSystem_onlyFails⟩
  | coverCompleteness =>
      exact ⟨coverageFailureSystem, coverageFailureSystem_onlyFails⟩
  | transitionContinuity =>
      exact ⟨continuityFailureSystem, continuityFailureSystem_onlyFails⟩
  | transitionFlatness =>
      exact ⟨flatnessFailureSystem, flatnessFailureSystem_onlyFails⟩

theorem coordinate_cardinality :
    Fintype.card TopologicalTransitionCoordinate = 4 := by
  decide

end RawTopologicalTransitionToy

end PhysicsCore
end SaturationMonoid
