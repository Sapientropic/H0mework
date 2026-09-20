/-
  Proposition 116: minimal sociality and asymmetric interaction.

  Proposition 114 proved the finite-cycle obstruction theorem: a noncancelled
  accumulated phase residual cannot be explained by a global potential.  This
  file pins down the sharper algebraic criterion behind the slogan:

      symmetric / path-additive interaction  <-> exact;
      asymmetric / non-additive interaction <-> nontrivial H¹.

  The important modeling boundary for the "N >= 3" claim is explicit here.
  A two-agent *linear* interaction has one overlap, represented by one phase
  value and its reverse.  That line phase is exact.  If one instead allows two
  independent directed phases between the same two agents, one has already put
  a directed cycle into the model; that is not the two-open Čech line.
-/

import H0mework.Realization.CyclicMemory.P114

/-! ## Path additivity is exactness -/

/-- A phase cochain is path-additive when every two-hop phase equals the direct
phase.  This is the algebraic form of "symmetric / globally explainable"
interaction. -/
def PathAdditive {Index A : Type*} [AddCommGroup A]
    (c : Index -> Index -> A) : Prop :=
  forall i j k, c i j + c j k = c i k

/-- THEOREM 1: every global-potential coboundary is path-additive. -/
theorem coboundary_pathAdditive
    {Index A : Type*} [AddCommGroup A]
    (p : Index -> A) :
    PathAdditive
      (CechAdditiveCover.d0
        (identityPairZeroTripleCover Index A) p) := by
  intro i j k
  simp [CechAdditiveCover.d0, identityPairZeroTripleCover]

/-- THEOREM 2: a path-additive cochain on a nonempty index set is a
coboundary.  The potential is obtained by choosing one base point and reading
all phases from that base point. -/
theorem oneCoboundary_of_pathAdditive
    {Index A : Type*} [Inhabited Index] [AddCommGroup A]
    (c : Index -> Index -> A)
    (hadd : PathAdditive c) :
    CechAdditiveCover.OneCoboundary
      (identityPairZeroTripleCover Index A) c := by
  let base : Index := default
  let p : Index -> A := fun i => c base i
  refine ⟨p, ?_⟩
  funext i j
  have hbij : c base i + c i j = c base j := hadd base i j
  simp [CechAdditiveCover.d0, identityPairZeroTripleCover, p]
  calc
    c base j - c base i = c i j := by
      rw [← hbij]
      abel

/-- THEOREM 3: on the identity-pair / zero-triple cover, exactness is
equivalent to path additivity. -/
theorem oneCoboundary_iff_pathAdditive
    {Index A : Type*} [Inhabited Index] [AddCommGroup A]
    (c : Index -> Index -> A) :
    CechAdditiveCover.OneCoboundary
        (identityPairZeroTripleCover Index A) c <->
      PathAdditive c := by
  constructor
  · intro hb
    rcases hb with ⟨p, hp⟩
    rw [← hp]
    exact coboundary_pathAdditive p
  · exact oneCoboundary_of_pathAdditive c

/-- THEOREM 4: in this cover skeleton, nontrivial H¹ is exactly non-additive
interaction.  This is the formal version of the asymmetric-interaction
criterion. -/
theorem h1Obstruction_iff_not_pathAdditive
    {Index A : Type*} [Inhabited Index] [AddCommGroup A]
    (c : Index -> Index -> A) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index A) c <->
      Not (PathAdditive c) := by
  constructor
  · intro h hp
    exact h.2 ((oneCoboundary_iff_pathAdditive c).mpr hp)
  · intro hnonadd
    exact
      ⟨identityPairZeroTripleCover_all_cochains_cocycle c,
        fun hb => hnonadd ((oneCoboundary_iff_pathAdditive c).mp hb)⟩

/-! ## Two-agent linear interaction is exact -/

/-- The two-agent linear index.  The valid two-agent line has one overlap; its
two directed readings are the same phase with opposite signs. -/
inductive TwoAgentLine where
  | left
  | right
  deriving DecidableEq, Repr

instance : Inhabited TwoAgentLine := ⟨TwoAgentLine.left⟩

/-- A two-agent linear phase has one independent value and its reverse. -/
def twoAgentLinePhase {A : Type*} [AddCommGroup A] (phase : A) :
    TwoAgentLine -> TwoAgentLine -> A
  | TwoAgentLine.left, TwoAgentLine.right => phase
  | TwoAgentLine.right, TwoAgentLine.left => -phase
  | _, _ => 0

/-- THEOREM 5: every valid two-agent line phase is path-additive. -/
theorem twoAgentLinePhase_pathAdditive
    {A : Type*} [AddCommGroup A] (phase : A) :
    PathAdditive (twoAgentLinePhase phase) := by
  intro i j k
  cases i <;> cases j <;> cases k <;>
    simp [twoAgentLinePhase]

/-- THEOREM 6: every valid two-agent line phase is a coboundary. -/
theorem twoAgentLinePhase_is_coboundary
    {A : Type*} [AddCommGroup A] (phase : A) :
    CechAdditiveCover.OneCoboundary
      (identityPairZeroTripleCover TwoAgentLine A)
      (twoAgentLinePhase phase) :=
  (oneCoboundary_iff_pathAdditive (twoAgentLinePhase phase)).mpr
    (twoAgentLinePhase_pathAdditive phase)

/-- THEOREM 7: a valid two-agent line phase cannot be a nontrivial H¹
obstruction.  This is the precise N=2 exactness boundary. -/
theorem twoAgentLinePhase_not_h1
    {A : Type*} [AddCommGroup A] (phase : A) :
    Not (CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover TwoAgentLine A)
      (twoAgentLinePhase phase)) := by
  intro h
  exact h.2 (twoAgentLinePhase_is_coboundary phase)

/-! ## Three-agent witness: the lower bound is sharp -/

instance : Inhabited ThreeCycleTime := ⟨ThreeCycleTime.t0⟩

/-- THEOREM 8: three agents already support a non-exact phase configuration.
This re-exports the P102/P108 witness as the sharpness half of the minimal
sociality boundary. -/
theorem threeAgent_nontrivial_h1_witness :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime Int)
      threeCyclePhaseCochain :=
  threeCyclePhase_h1Obstruction

/-- THEOREM 9: the three-agent witness is non-additive / asymmetric. -/
theorem threeAgent_witness_not_pathAdditive :
    Not (PathAdditive threeCyclePhaseCochain) :=
  (h1Obstruction_iff_not_pathAdditive threeCyclePhaseCochain).mp
    threeAgent_nontrivial_h1_witness

/-!
  Summary:
  - Path-additive interaction is exactly coboundary/exact.
  - Non-additive interaction is exactly nontrivial H¹ in this skeleton.
  - A valid two-agent line phase is path-additive, hence exact.
  - A three-agent configuration already has a non-additive witness, so the
    `N >= 3` lower bound is sharp under the two-open-line modeling discipline.

  Boundary:
  - If a two-agent model allows two independent directed phases on the same
    overlap, it has inserted a directed cycle by hand.  P116's N=2 exactness
    theorem applies to the Čech two-open line / antisymmetric representation.
-/
