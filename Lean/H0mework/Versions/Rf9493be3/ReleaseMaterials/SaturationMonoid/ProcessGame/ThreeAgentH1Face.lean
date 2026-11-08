import H0mework.Versions.Rf9493be3.Foundation.Agency.Game
import H0mework.Realization.Relations.P121

/-!
# Three-agent H1 process face

One fixed rooted exposure carries the three selected ring edges.  Folding an
interaction cochain over that occurrence generates its ring residual; the
residual is not accepted as input.  P116, P117 and P121 then read exactness,
H1 obstruction and cohomology invariance from the same generated value.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootedAccountedUnfolding

universe u

inductive ThreeAgentFoldPoint
  | anchor
  | edge01
  | edge12
  | edge20
  deriving DecidableEq

/-- The sole rooted occurrence for the three selected interaction edges. -/
def threeAgentExposure : RootedAccountedUnfolding ThreeAgentFoldPoint :=
  .occur .anchor <|
    .cons (zero .edge01) <|
      .cons (zero .edge12) <|
        .singleton (zero .edge20)

/-- Algebra reading each exact edge and summing only at the generated root. -/
def threeAgentAlgebra
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A)
    (point : ThreeAgentFoldPoint) (children : List A) : A :=
  match point with
  | .anchor => children.foldr (· + ·) 0
  | .edge01 => cochain ThreeCycleTime.t0 ThreeCycleTime.t1
  | .edge12 => cochain ThreeCycleTime.t1 ThreeCycleTime.t2
  | .edge20 => cochain ThreeCycleTime.t2 ThreeCycleTime.t0

/-- Source-generated fold value; there is no residual field. -/
def threeAgentFold
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A) : A :=
  threeAgentExposure.fold (threeAgentAlgebra cochain)

/-! ## Source-indexed ProcessGame mouth -/

/-- Fixed compiler from the zero-choice source to the existing exposure. -/
def threeAgentOccurrenceOf : Unit → RootedAccountedUnfolding ThreeAgentFoldPoint :=
  fun _ => threeAgentExposure

/-- The three-agent process stores only its source; the occurrence is compiled. -/
def threeAgentProcessGame :
    _root_.SaturationMonoid.ProcessGame threeAgentOccurrenceOf where
  source := ()

theorem threeAgentProcessGame_occurrence_eq_exposure :
    threeAgentProcessGame.occurrence = threeAgentExposure :=
  rfl

/-- Closed core fold readout generated at the same exact exposure. -/
def threeAgentFoldReadout
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A) :
    FoldReadout threeAgentProcessGame (threeAgentAlgebra cochain) :=
  foldReadout threeAgentProcessGame (threeAgentAlgebra cochain)

theorem threeAgentFoldReadout_value_eq_fold
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A) :
    (threeAgentFoldReadout cochain).value = threeAgentFold cochain :=
  rfl

theorem threeAgentFold_eq_ringResidual
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A) :
    threeAgentFold cochain = threeAgentRingResidual cochain := by
  simp [threeAgentFold, threeAgentExposure, threeAgentAlgebra,
    RootedAccountedUnfolding.fold, RootedAccountedUnfolding.foldBranches,
    RootedAccountedUnfolding.zero, AccountedBranches.singleton,
    threeAgentRingResidual, add_assoc]

theorem threeAgentFoldReadout_value_eq_ringResidual
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A) :
    (threeAgentFoldReadout cochain).value =
      threeAgentRingResidual cochain := by
  rw [threeAgentFoldReadout_value_eq_fold,
    threeAgentFold_eq_ringResidual]

/-- Direct shared-core uniqueness consumer. -/
theorem threeAgentFoldReadout_candidate_unique
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A)
    (candidate : RootedAccountedUnfolding ThreeAgentFoldPoint → A)
    (commutes : ∀ origin branches,
      candidate (.occur origin branches) =
        threeAgentAlgebra cochain origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate threeAgentExposure = (threeAgentFoldReadout cochain).value := by
  simpa [threeAgentProcessGame, threeAgentOccurrenceOf] using
    (threeAgentFoldReadout cochain).candidate_eq_value candidate commutes

/-- Direct P117 consumer: nonzero generated fold value yields H1. -/
theorem threeAgentFold_nonzero_h1
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A)
    (nonzero : threeAgentFold cochain ≠ 0) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime A) cochain :=
  threeAgentRingResidual_nonzero_h1 cochain <| by
    rwa [← threeAgentFold_eq_ringResidual]

theorem threeAgentFoldReadout_nonzero_h1
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A)
    (nonzero : (threeAgentFoldReadout cochain).value ≠ 0) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime A) cochain :=
  threeAgentFold_nonzero_h1 cochain <| by
    rwa [← threeAgentFoldReadout_value_eq_fold]

theorem threeAgentFoldReadout_nonzero_not_pathAdditive
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A)
    (nonzero : (threeAgentFoldReadout cochain).value ≠ 0) :
    ¬ PathAdditive cochain :=
  (h1Obstruction_iff_not_pathAdditive cochain).mp
    (threeAgentFoldReadout_nonzero_h1 cochain nonzero)

/-- Direct P116 consumer of the same generated H1 face. -/
theorem threeAgentFold_nonzero_not_pathAdditive
    {A : Type u} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A)
    (nonzero : threeAgentFold cochain ≠ 0) :
    ¬ PathAdditive cochain :=
  (h1Obstruction_iff_not_pathAdditive cochain).mp
    (threeAgentFold_nonzero_h1 cochain nonzero)

/-- Direct P121 consumer: cohomologous cochains have the same generated fold
value on the fixed exposure. -/
theorem threeAgentFold_eq_of_cohomologous
    {A : Type u} [AddCommGroup A]
    {first last : ThreeCycleTime → ThreeCycleTime → A}
    (cohomologous : ThreeAgentRingCohomologous first last) :
    threeAgentFold last = threeAgentFold first := by
  rw [threeAgentFold_eq_ringResidual, threeAgentFold_eq_ringResidual]
  exact threeAgentRingResidual_eq_of_cohomologous cohomologous

theorem threeAgentFoldReadout_eq_of_cohomologous
    {A : Type u} [AddCommGroup A]
    {first last : ThreeCycleTime → ThreeCycleTime → A}
    (cohomologous : ThreeAgentRingCohomologous first last) :
    (threeAgentFoldReadout last).value =
      (threeAgentFoldReadout first).value := by
  rw [threeAgentFoldReadout_value_eq_fold,
    threeAgentFoldReadout_value_eq_fold]
  exact threeAgentFold_eq_of_cohomologous cohomologous

end ProcessGame
end SaturationMonoid
