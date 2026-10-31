import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.Universal.FixedFixtureCore
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Relations.ThreeAgentRoleCohomology

/-!
# Three exact generated roles produce nontrivial H¹

The existing two-state lifecycle occurrence supplies three distinct generated
actors and three exact relation-beneficiary seeds.  Their local phase readouts
are `1, 1, 0`; the existing three-agent ProcessGame fold therefore generates
the nonzero residual.  No residual, H¹ certificate or target role is a premise
of the closed consumer theorems below.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M2ThreeAgentRoleCohomologyRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle
open Lifecycle.Universal.FixedAdapter

/-- Three closed relation occurrences anchored at the exact source boundary. -/
def relationSeedAt (_source : Unit) (state : EventState)
    (_seed : ThreeCycleTime) : Prop :=
  state = .before

def beneficiary : ThreeCycleTime → SourceToken
  | .t0 => .s0
  | .t1 => .s1
  | .t2 => .s2

/-- The local cochain values are source law, not a submitted ring residual. -/
def localPhase : ThreeCycleTime → Int
  | .t0 => 1
  | .t1 => 1
  | .t2 => 0

abbrev compiler : SourceOwnedRelationRoleCompiler actualEventOccurrenceOf
    actualEventGame FixedAdapter.sourceFace where
  RelationSeed := ThreeCycleTime
  RelationLineage := fun _ => ThreeCycleTime
  relationSeedAt := relationSeedAt
  relationLineageOf := fun _ seed => seed.1
  beneficiaryActorSeed := beneficiary
  beneficiaryActor_active := by
    intro source state seed active
    exact active
  Role := fun _ => Int
  Phase := fun _ => Int
  sourceRoleOf := fun _ _ => 0
  phaseStepOf := fun _ lineage => localPhase lineage
  advanceRole := fun _ phase role => role + phase
  FutureCode := Empty
  futureCodeDecidableEq := inferInstance
  futureCodeCarrier := ∅
  futureIdle := fun code => nomatch code
  FutureContinuationAt := fun _ _ _ => Empty
  futureBoundaryState := fun _ _ => .before
  futureBoundaryState_mem := by
    intro lineage side
    simp [actualEventOccurrenceOf]
  FutureContinuationWitnessAt := fun _ _ _ _ => False
  futureContinuation_witnessed := by
    intro lineage side code continuation
    exact nomatch continuation

def exactRelationSeed (index : ThreeCycleTime) :
    compiler.ExactRelationSeed :=
  ⟨index, .before, by simp [actualEventOccurrenceOf], rfl⟩

def generatedRelation (index : ThreeCycleTime) :
    compiler.GeneratedRelation :=
  compiler.relationOf (exactRelationSeed index)

def generatedActor (index : ThreeCycleTime) : compiler.Actor :=
  (exactRelationSeed index).actor compiler

@[simp] theorem generatedActor_value (index : ThreeCycleTime) :
    (generatedActor index).1 = beneficiary index :=
  rfl

theorem generatedActor_injective : Function.Injective generatedActor := by
  intro first last equal
  have values := congrArg Subtype.val equal
  change beneficiary first = beneficiary last at values
  cases first <;> cases last <;>
    simp [beneficiary] at values ⊢

local instance : AddCommGroup (compiler.Phase actualEventGame.source) := by
  change AddCommGroup Int
  infer_instance

def roleCycle : ThreeAgentGeneratedRoleCycle compiler where
  actor := generatedActor
  actor_injective := generatedActor_injective
  relation := generatedRelation
  interest := fun index => ⟨exactRelationSeed index, rfl, rfl⟩

@[simp] theorem generated_phaseStep (index : ThreeCycleTime) :
    compiler.phaseStep (roleCycle.relation index) = localPhase index :=
  rfl

/-- The generated role cochain is exactly the established three-cycle
cochain; this is an output equality, not an input normalizer. -/
theorem roleCycle_cochain_eq_threeCyclePhaseCochain :
    roleCycle.cochain = threeCyclePhaseCochain := by
  funext source target
  cases source <;> cases target <;>
    decide

theorem roleCycle_phaseSum_eq_two : roleCycle.phaseSum = (2 : Int) :=
  rfl

/-- Closed P117 consumer: exact generated relation phases produce H¹ without
a residual or nonzero premise in the theorem mouth. -/
theorem generated_relation_roles_nonzero_h1 :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime Int)
      roleCycle.cochain :=
  roleCycle.nonzero_h1 (by rw [roleCycle_phaseSum_eq_two]; norm_num)

/-- Closed P116 consumer of the same fold value. -/
theorem generated_relation_roles_not_pathAdditive :
    ¬ PathAdditive roleCycle.cochain :=
  roleCycle.nonzero_not_pathAdditive
    (by rw [roleCycle_phaseSum_eq_two]; norm_num)

theorem generated_role_fold_value_eq_two :
    roleCycle.foldReadout.value = 2 := by
  rw [roleCycle.foldReadout_value_eq_phaseSum,
    roleCycle_phaseSum_eq_two]

/-- P121 invariance stays attached to the generated fold value. -/
theorem generated_role_fold_cohomology_invariant
    {other : ThreeCycleTime → ThreeCycleTime → Int}
    (cohomologous : ThreeAgentRingCohomologous roleCycle.cochain other) :
    (threeAgentFoldReadout other).value = 2 := by
  rw [roleCycle.foldReadout_eq_of_cohomologous cohomologous,
    generated_role_fold_value_eq_two]

/-- The P116 two-agent boundary remains exact; inserting three generated
actors is what makes the above obstruction possible. -/
theorem two_agent_line_cannot_carry_this_h1 (phase : Int) :
    ¬ CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover TwoAgentLine Int)
      (twoAgentLinePhase phase) :=
  twoAgentLinePhase_not_h1 phase

end M2ThreeAgentRoleCohomologyRegression
end Society
end ProcessGame
end SaturationMonoid
