import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyWriteback
import H0mework.Versions.Rac9f88e1.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.LinearCochain

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 160000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCayleyRelations

open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open CategoryTheory CofinalHistorySettlement CofinalRelationGeneratedComplex
open SourceOperationPaidRelations SourceOperationScalarRelations
open RootGeneratedDebtActivationJointSource.OwnerFree

open private tally tallyReceipt from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyProgramme

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "authority" => CountedFiniteNative.root observation nontrivial half depth ordinal
local notation "origin" => CountedFiniteNative.current observation nontrivial half depth ordinal
local notation "termTrace" => CountedCayleyProgramme.terminalTrace observation nontrivial half depth ordinal
local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "V" => CountedCellHistory.CellValue
local notation "X" => CountedCellHistory.Var

local notation "H" "[" root "," trace "]" => prefixHistory root (exposure trace)

private def tallyContext {Root : Type} (root : RootedAccountedUnfolding Root)
    (coordinate : BurnolCompletedMellinCoordinate) (seed : Expr V X ()) {environment : Env V X} :
    (n : Nat) → {result : V ()} →
    (actual : Trace environment (tally coordinate seed n) (.const result)) →
    let child := (tallyReceipt coordinate seed n actual).trace
    Σ forward : H[root,child].relationClosure →ₗ[ℤ] H[root,actual].relationClosure,
      {back : H[root,actual].relationClosure →ₗ[ℤ] H[root,child].relationClosure //
        Function.LeftInverse back forward}
  | 0, _, _ => ⟨LinearMap.id, ⟨LinearMap.id, fun _ => rfl⟩⟩
  | n+1, _, actual =>
    let cut := actual.splitLinear
    let inner := tallyContext root coordinate seed n cut.trace
    let outer := linearRelation root root cut.interleaving
    let back := linearRelationBack root root cut.interleaving
    ⟨outer.comp inner.1, ⟨inner.2.val.comp back, fun word =>
      (congrArg inner.2.val (linear_relation_recover root root cut.interleaving (inner.1 word))).trans
        (inner.2.property word)⟩⟩

/-- The child relation writes into the actual terminal and recovers its full integer coefficients. -/
def countedRelationFibre (N : Nat) (positive : 0 < N) (n : Nat) :
    let actual := termTrace N positive n
    let child := CountedCayleyProgramme.countChild observation nontrivial half depth ordinal N positive n
    let root := RootedAccountedUnfolding.zero ((authority).emitted origin)
    Σ forward : H[root,child.trace].relationClosure →ₗ[ℤ] H[root,actual].relationClosure,
      {back : H[root,actual].relationClosure →ₗ[ℤ] H[root,child.trace].relationClosure //
        Function.LeftInverse back forward} := by
  let actual := termTrace N positive n
  let root := RootedAccountedUnfolding.zero ((authority).emitted origin)
  let seed := CountedCayleyProgramme.readBank observation nontrivial half depth ordinal N positive
    ((authority).emitted origin)
  let finishCut := actual.splitLinear
  let tallyCut := tallyReceipt coord seed.expression n finishCut.trace
  let countCut := tallyCut.trace.splitLinear
  let decoded := linearRelation root root countCut.interleaving
  let executed := tallyContext root coord seed.expression n finishCut.trace
  let terminal := linearRelation root root finishCut.interleaving
  let decodeBack := linearRelationBack root root countCut.interleaving
  let finishBack := linearRelationBack root root finishCut.interleaving
  refine ⟨terminal.comp (executed.1.comp decoded), ⟨decodeBack.comp (executed.2.val.comp finishBack), ?_⟩⟩
  intro word
  change decodeBack (executed.2.val (finishBack (terminal (executed.1 (decoded word))))) = word
  have outer := linear_relation_recover root root finishCut.interleaving (executed.1 (decoded word))
  have middle := executed.2.property (decoded word)
  have inner := linear_relation_recover root root countCut.interleaving word
  exact (congrArg (fun relation => decodeBack (executed.2.val relation)) outer).trans
    ((congrArg decodeBack middle).trans inner)

private def tallyCochain {Root : Type} (root : RootedAccountedUnfolding Root)
    (coordinate : BurnolCompletedMellinCoordinate) (seed : Expr V X ()) {environment : Env V X} :
    (n : Nat) → {result : V ()} →
    (actual : Trace environment (tally coordinate seed n) (.const result)) →
    natComplex H[root,(tallyReceipt coordinate seed n actual).trace] ⟶ natComplex H[root,actual]
  | 0, _, _ => 𝟙 _
  | n+1, _, actual =>
    let cut := actual.splitLinear
    tallyCochain root coordinate seed n cut.trace ≫ linearCochain root root cut.interleaving

/-- The counted child's cochain map is the composition of the actual contexts in the parent. -/
def countedCochain (N : Nat) (positive : 0 < N) (n : Nat) :
    let actual := termTrace N positive n
    let child := CountedCayleyProgramme.countChild observation nontrivial half depth ordinal N positive n
    let root := RootedAccountedUnfolding.zero ((authority).emitted origin)
    natComplex H[root,child.trace] ⟶ natComplex H[root,actual] := by
  let actual := termTrace N positive n
  let root := RootedAccountedUnfolding.zero ((authority).emitted origin)
  let seed := CountedCayleyProgramme.readBank observation nontrivial half depth ordinal N positive
    ((authority).emitted origin)
  let outer := actual.splitLinear
  let middle := tallyReceipt coord seed.expression n outer.trace
  let inner := middle.trace.splitLinear
  exact linearCochain root root inner.interleaving ≫
    tallyCochain root coord seed.expression n outer.trace ≫ linearCochain root root outer.interleaving

theorem terminal_boundary_effect (N : Nat) (positive : 0 < N) (n : Nat) (increment : Env V X) :
    let actual := termTrace N positive n
    let cut := actual.splitLinear
    type_of% (linear_boundary_effect actual cut.trace increment) :=
  linear_boundary_effect (termTrace N positive n) (termTrace N positive n).splitLinear.trace increment

end CountedCayleyRelations
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
