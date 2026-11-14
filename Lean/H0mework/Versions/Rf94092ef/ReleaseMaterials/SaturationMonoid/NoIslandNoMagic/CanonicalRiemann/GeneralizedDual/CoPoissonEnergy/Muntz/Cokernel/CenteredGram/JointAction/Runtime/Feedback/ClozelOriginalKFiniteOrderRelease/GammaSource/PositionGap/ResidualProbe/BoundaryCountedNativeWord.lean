import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedNativeBeta
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Scalar.InventoryLift.Rechart
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Consumer

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

open BurnolPhysicalState SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
open SourceGeneratedScalarDifferentialResidual

namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeWord

open OriginalKCofinalFullBranchFibre.KernelWrite

namespace BD
export NativeDelta.BetaDecoder (nextNative admittedBeta old increment actual_decoder_inverse original_action)
end BD
namespace Rec
export NativeDelta.BetaDecoder.Recurrence (retained actualUpdatedValue original_old)
end Rec
namespace WB
export NativeSigma.Writeback (nativeTrace nativeInverseValue)
end WB

local instance groups (grade : Nat) (slot : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade slot) := L.groups (PairValue C.Value) grade slot

/-- Apply the same finite word independently on every leaf of the original inventory grade. -/
def gradeChart (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
    (grade : Nat) → (slot : Unit) →
      L.Value (PairValue C.Value) grade slot ≃+ L.Value (PairValue C.Value) grade slot
  | 0, _ =>
      let e := BoundaryCountedWordInverse.equiv coordinate n
      (e.prodCongr e).toLinearEquiv.toAddEquiv
  | grade+1, slot =>
      (gradeChart coordinate n grade slot).prodCongr (gradeChart coordinate n grade slot)

set_option backward.isDefEq.respectTransparency false in
private theorem collapse_chart (coordinate : BurnolCompletedMellinCoordinate) (n grade : Nat)
    (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
    CF.collapseValue grade (((gradeChart coordinate n grade ()).prodCongr
        (gradeChart coordinate n grade ())) value) =
      BoundaryCountedNativeBeta.branchChart coordinate n (CF.collapseValue grade value) := by
  induction grade with
  | zero => rfl
  | succ grade previous =>
    let e := (gradeChart coordinate n grade ()).prodCongr (gradeChart coordinate n grade ())
    change CF.collapseValue grade (e value.1+e value.2) =
      BoundaryCountedNativeBeta.branchChart coordinate n (CF.collapseValue grade (value.1+value.2))
    rw [← map_add e, previous]

private theorem grade_cast (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
    {first second : Nat} (same : first=second) (value : L.Value (PairValue C.Value) first ()) :
    Eq.mp (congrArg (fun grade => L.Value (PairValue C.Value) grade ()) same)
        (gradeChart coordinate n first () value) =
      gradeChart coordinate n second ()
        (Eq.mp (congrArg (fun grade => L.Value (PairValue C.Value) grade ()) same) value) := by
  cases same
  rfl

private theorem native_collapse_chart (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
    (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
    (value : L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1 ()) :
    NativeSigma.collapseNative factory packet
        (gradeChart coordinate n (AS.nativeAfterAdmission factory packet).1 () value) =
      BoundaryCountedNativeBeta.branchChart coordinate n (NativeSigma.collapseNative factory packet value) := by
  let same := AS.nativeAfterAdmission_grade factory packet
  let castValue := Eq.mp (congrArg (fun grade => L.Value (PairValue C.Value) grade ()) same) value
  have casted := congrArg
    (fun row : L.Value (PairValue C.Value) (packet.1+1) () => CF.collapseValue packet.1 row)
    (grade_cast coordinate n same value)
  exact casted.trans (collapse_chart coordinate n packet.1 castValue)

section Decode

variable (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
variable (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)

abbrev NextValues := L.Value (PairValue C.Value) (BD.nextNative factory native).1

abbrev nextChart (slot : Unit) : NextValues factory native slot ≃+ NextValues factory native slot :=
  gradeChart coordinate n (BD.nextNative factory native).1 slot

local notation "e" => nextChart coordinate n factory native
local notation "word" => BD.admittedBeta factory native
local notation "old" => BD.old factory native
local notation "delta" => BD.increment factory native

/-- Use the actually admitted relation, retaining its atom indices and signed coefficients. -/
def betaWord : Formal ℤ (NextValues factory native) C.Var () :=
  Rechart.word e () word

def betaInventory : NextValues factory native () × NextValues factory native () :=
  updateInventory (R := ℤ) (Rechart.env e old) (Rechart.env e delta) (betaWord coordinate n factory native)

theorem beta_inventory :
    betaInventory coordinate n factory native =
      (e () (evaluation (R := ℤ) old word), e () (effectEvaluator (R := ℤ) old delta word)) :=
  Rechart.inventory e old delta word

private theorem inventory_of_read
    (retained : evaluation (R := ℤ) old word = Rec.retained factory native)
    (effect : effectEvaluator (R := ℤ) old delta word = WB.nativeInverseValue (BD.nextNative factory native)) :
    betaInventory coordinate n factory native =
      (e () (Rec.retained factory native), e () (WB.nativeInverseValue (BD.nextNative factory native))) :=
  (beta_inventory coordinate n factory native).trans
    (congrArg₂ (fun left right : NextValues factory native () => (e () left,e () right)) retained effect)

theorem beta_word_roundtrip :
    (Rechart.word e ()).symm (betaWord coordinate n factory native) = word :=
  (Rechart.word e ()).symm_apply_apply word

/-- The existing range inverse consumes the entire recharted word in the actual next decoder. -/
def updated : NextValues factory native () :=
  let decoder := evaluation (R := ℤ) (s := ()) (Rechart.env e old + Rechart.env e delta)
  (residualEquivRange decoder (canonicalResidual decoder (betaWord coordinate n factory native))).val

theorem updated_source :
    updated coordinate n factory native = e () (Rec.actualUpdatedValue factory native) := by
  have inverse : updated coordinate n factory native =
      (betaInventory coordinate n factory native).1+(betaInventory coordinate n factory native).2 :=
    updated_residual_readout (Rechart.env e old) (Rechart.env e delta) (betaWord coordinate n factory native)
  have encoded := congrArg (fun pair : NextValues factory native () × NextValues factory native () => pair.1+pair.2)
    (beta_inventory coordinate n factory native)
  exact inverse.trans (encoded.trans ((map_add (e ()) _ _).symm.trans
    (congrArg (e ()) (BD.actual_decoder_inverse factory native).symm)))

theorem updated_collapse :
    NativeSigma.collapseNative factory (AS.bornAfterNative native) (updated coordinate n factory native) =
      BoundaryCountedNativeBeta.branchChart coordinate n
        (NativeSigma.collapseNative factory (AS.bornAfterNative native) (Rec.actualUpdatedValue factory native)) :=
  (congrArg (NativeSigma.collapseNative factory (AS.bornAfterNative native))
    (updated_source coordinate n factory native)).trans
    (native_collapse_chart coordinate n factory (AS.bornAfterNative native) (Rec.actualUpdatedValue factory native))

/-- Rechart the following occurrence's paid trace, preserving each original step address. -/
def paidTrace :=
  Rechart.trace e (WB.nativeTrace (BD.nextNative factory native))

theorem paid_words :
    SourceOperationPaidRelations.words (paidTrace coordinate n factory native) =
      (SourceOperationPaidRelations.words (WB.nativeTrace (BD.nextNative factory native))).map (Rechart.word e ()) :=
  Rechart.paid_words e _

end Decode

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "factory" => NativeSigma.originalFactory observation nontrivial half
local notation "nativeAt" => originalNative observation nontrivial half depth

/-- Read the actual old receipt and following native inverse at their complete grades. -/
theorem beta_inventory_source (ordinal n : Nat) :
    type_of% (inventory_of_read c n factory (nativeAt (ordinal+1))
      (Rec.original_old observation nontrivial half depth ordinal)
      (BD.original_action observation nontrivial half depth ordinal)) :=
  inventory_of_read c n factory (nativeAt (ordinal+1))
    (Rec.original_old observation nontrivial half depth ordinal)
    (BD.original_action observation nontrivial half depth ordinal)

theorem actual_physical (ordinal n : Nat) :
    NativeSigma.collapseNative factory (AS.bornAfterNative (nativeAt (ordinal+1)))
      (updated c n factory (nativeAt (ordinal+1))) =
        BoundaryCountedNativeBeta.beta observation nontrivial half depth ordinal n :=
  (updated_collapse c n factory (nativeAt (ordinal+1))).trans
    (BoundaryCountedNativeBeta.beta_source observation nontrivial half depth ordinal n).symm

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeWord
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
