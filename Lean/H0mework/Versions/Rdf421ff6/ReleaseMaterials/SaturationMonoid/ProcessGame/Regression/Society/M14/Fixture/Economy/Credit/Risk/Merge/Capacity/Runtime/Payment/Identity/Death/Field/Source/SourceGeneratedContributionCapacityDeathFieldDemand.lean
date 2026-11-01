import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.LivingLawAtomFieldSeparation
import H0mework.Foundation.Source.AccountedUnfolding
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Handoff.Compiler.SourceGeneratedContributionCapacitySettlementSurvivorCompiler

/-!
# Source-generated contribution-capacity death-field demand

The survivor source owns a two-section publication demand before its root is
emitted.  P98/P99 generate the finite `false -> true` field readout; the sole
`RootedAccountedUnfolding` constructor exposes the same two sections and its
unique fold computes the local first hit at one step.

This module grants no update authority.  The demand is a zero-field dependent
payload of one existing survivor occurrence.  Only a downstream exact action
Payment at that same occurrence may consume it and generate a target current.
No date, death registry, clock ontology, history table, target or completed
future is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityDeathFieldDemand

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RootedAccountedUnfolding
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14UBIPeriodicActualServiceCapacity

/-! ## P68/P98/P99 finite death field -/

/-- Pointwise presentation of the derived death field.  Finite restrictions
expose only the generated coordinates in scope. -/
def contributionCapacityDeathFieldCover :
    SectionIndexedCover Nat (Nat → Bool) (fun _ => Bool)
      (fun _ _ => PUnit) where
  toLocal := fun index field => field index
  leftToOverlap := fun _ _ _ => PUnit.unit
  rightToOverlap := fun _ _ _ => PUnit.unit
  glue := fun family index => family index

theorem contributionCapacityDeathFieldDescent :
    SectionDescentCertificate contributionCapacityDeathFieldCover where
  globalCompatible := by
    intro field left right
    rfl
  glueRestricts := by
    intro family compatible index
    rfl
  glueUnique := by
    intro family compatible field restricts
    funext index
    exact restricts index

def contributionCapacityDeathFieldPresentation :
    AtomFieldPresentation (Nat → Bool) where
  Local := fun _ => Bool
  Overlap := fun _ _ => PUnit
  cover := contributionCapacityDeathFieldCover
  descent := contributionCapacityDeathFieldDescent

/-- The generated query advances from a nonterminal section to the terminal
section and then remains terminal. -/
def contributionCapacityDeathFieldQuery : ReflexiveQuery Bool Bool where
  read := id
  write := fun _ => true

def contributionCapacityDeathField : Nat → Bool :=
  (reflexiveQueryIteratedTimeField contributionCapacityDeathFieldQuery false
    ).stateAt

def contributionCapacityDeathFiniteSectionAt (scope : Nat) :
    contributionCapacityDeathFieldPresentation.FiniteSection scope :=
  contributionCapacityDeathFieldPresentation.restrict
    contributionCapacityDeathField scope

@[simp] theorem contributionCapacityDeathField_zero :
    contributionCapacityDeathField 0 = false :=
  rfl

@[simp] theorem contributionCapacityDeathField_one :
    contributionCapacityDeathField 1 = true :=
  rfl

@[simp] theorem contributionCapacityDeathFiniteSection_zero :
    contributionCapacityDeathFiniteSectionAt 1 ⟨0, by decide⟩ = false :=
  rfl

@[simp] theorem contributionCapacityDeathFiniteSection_one :
    contributionCapacityDeathFiniteSectionAt 1 ⟨1, by decide⟩ = true :=
  rfl

/-- P99 execution is exactly the one generated read/write edge. -/
theorem contributionCapacityDeathField_repeat_one :
    StatefulGenAlg.repeatEval
        (reflexiveQueryPrimitive contributionCapacityDeathFieldQuery)
        (reflexiveQueryStatefulPlan contributionCapacityDeathFieldQuery)
        1 false [false] true := by
  exact
    reflexiveStatefulPlan_repeatEval_canonical
      contributionCapacityDeathFieldQuery false 1

def contributionCapacityDeathChangedAfter (scope : Nat) : Nat → Bool :=
  fun index => if index = scope + 1 then true else false

/-- No finite section decodes the completed ambient field. -/
def contributionCapacityDeathFieldProper :
    contributionCapacityDeathFieldPresentation.ProperFiniteSections where
  noCompletedAmbient := by
    intro scope
    constructor
    intro completed
    let left : Nat → Bool := fun _ => false
    let right : Nat → Bool := contributionCapacityDeathChangedAfter scope
    have restrict_eq :
        contributionCapacityDeathFieldPresentation.restrict left scope =
          contributionCapacityDeathFieldPresentation.restrict right scope := by
      funext index
      rcases index with ⟨index, index_lt⟩
      change left index = right index
      simp only [left, right, contributionCapacityDeathChangedAfter]
      split
      · rename_i equality
        omega
      · rfl
    have ambient_eq : left = right := by
      calc
        left = completed.recover
            (contributionCapacityDeathFieldPresentation.restrict left scope) :=
          (completed.recover_restrict left).symm
        _ = completed.recover
            (contributionCapacityDeathFieldPresentation.restrict right scope) := by
          rw [restrict_eq]
        _ = right := completed.recover_restrict right
    have coordinate_eq := congrFun ambient_eq (scope + 1)
    simp [left, right, contributionCapacityDeathChangedAfter] at coordinate_eq

/-! ## Sole occurrence and unique minimal-locus fold -/

def contributionCapacityDeathFieldExposure :
    RootedAccountedUnfolding Bool :=
  (RootedAccountedUnfolding.zero false).advance
    (fun _ => RootedAccountedUnfolding.zero true)

def contributionCapacityDeathLocusAlgebra
    (terminal : Bool) (children : List (Option Nat)) : Option Nat :=
  if terminal then some 0 else
    match children with
    | [] => none
    | child :: _ => child.map Nat.succ

def contributionCapacityDeathLocusReadout : Option Nat :=
  contributionCapacityDeathFieldExposure.fold
    contributionCapacityDeathLocusAlgebra

@[simp] theorem contributionCapacityDeathLocusReadout_eq_one :
    contributionCapacityDeathLocusReadout = some 1 :=
  rfl

/-- Any evaluator commuting with the sole occurrence constructor computes the
same local first hit.  The fold is the readout; it is not a second evaluator
or publication authority. -/
theorem contributionCapacityDeathLocus_fold_unique
    (candidate : RootedAccountedUnfolding Bool → Option Nat)
    (commutes : ∀ (origin : Bool) (branches : AccountedBranches Bool),
      candidate (RootedAccountedUnfolding.occur origin branches) =
        contributionCapacityDeathLocusAlgebra origin
          (candidateValues candidate branches)) :
    candidate contributionCapacityDeathFieldExposure = some 1 := by
  rw [RootedAccountedUnfolding.fold_unique
    contributionCapacityDeathLocusAlgebra candidate commutes]
  rfl

/-! ## Pre-emitter source payload -/

/-- Zero-field publication demand indexed by one exact survivor occurrence.
It contains no result, locus, Payment, target or next. -/
structure SourceGeneratedContributionCapacityDeathFieldDemandAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current) : Type where
  private mk ::

def SourceGeneratedContributionCapacityDeathFieldDemandAt.generate
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current) :
    SourceGeneratedContributionCapacityDeathFieldDemandAt oldVisit sourceIndex
      settlementSource occurrence :=
  ⟨⟩

namespace SourceGeneratedContributionCapacityDeathFieldDemandAt

variable {oldVisit : OldVisit} {sourceIndex : Nat}
variable {settlementSource :
  ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex}
variable {current : Nat}
variable {occurrence :
  (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
    settlementSource).toRootSource.actual.OccurrenceAt current}

/-- The source occurrence itself regenerates the rich actual-service
authority. -/
theorem actualService
    (_demand : SourceGeneratedContributionCapacityDeathFieldDemandAt oldVisit
      sourceIndex settlementSource occurrence) :
    Nonempty (PeriodicActualServiceExitAt
      (contributionCapacitySettlementSurvivorDepthAt sourceIndex current)) :=
  occurrence.2.periodicExitGenerated

/-- The finite section is a pure readout of the P98 field. -/
def finiteSection
    (_demand : SourceGeneratedContributionCapacityDeathFieldDemandAt oldVisit
      sourceIndex settlementSource occurrence) :=
  contributionCapacityDeathFiniteSectionAt 1

@[simp] theorem sourceRead_eq_false
    (demand : SourceGeneratedContributionCapacityDeathFieldDemandAt oldVisit
      sourceIndex settlementSource occurrence) :
    demand.finiteSection ⟨0, by decide⟩ = false :=
  contributionCapacityDeathFiniteSection_zero

@[simp] theorem targetRead_eq_true
    (demand : SourceGeneratedContributionCapacityDeathFieldDemandAt oldVisit
      sourceIndex settlementSource occurrence) :
    demand.finiteSection ⟨1, by decide⟩ = true :=
  contributionCapacityDeathFiniteSection_one

def localMinimalLocus
    (_demand : SourceGeneratedContributionCapacityDeathFieldDemandAt oldVisit
      sourceIndex settlementSource occurrence) : Option Nat :=
  contributionCapacityDeathLocusReadout

@[simp] theorem localMinimalLocus_eq_one
    (demand : SourceGeneratedContributionCapacityDeathFieldDemandAt oldVisit
      sourceIndex settlementSource occurrence) :
    demand.localMinimalLocus = some 1 :=
  contributionCapacityDeathLocusReadout_eq_one

end SourceGeneratedContributionCapacityDeathFieldDemandAt

end
end M14SourceGeneratedContributionCapacityDeathFieldDemand
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityDeathFieldDemand.contributionCapacityDeathField_repeat_one
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityDeathFieldDemand.contributionCapacityDeathLocus_fold_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityDeathFieldDemand.contributionCapacityDeathFieldProper
