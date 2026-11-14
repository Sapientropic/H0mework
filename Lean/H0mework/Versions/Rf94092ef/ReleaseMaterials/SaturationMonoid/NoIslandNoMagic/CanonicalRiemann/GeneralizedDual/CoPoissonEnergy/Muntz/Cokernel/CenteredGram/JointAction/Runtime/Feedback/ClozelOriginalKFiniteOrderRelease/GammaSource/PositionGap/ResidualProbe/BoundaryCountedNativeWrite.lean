import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedNativeWord
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Scalar.InventoryLift.Rechart.Lift

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeWrite

open BurnolPhysicalState SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
open OriginalKCofinalFullBranchFibre.KernelWrite

namespace W
export NativeSigma.Writeback
  (bornWord admissionWord nativeTrace nativeBoundary nativeReceiptTransfer nativeHistory original_sigma_next_relation)
end W
namespace N
export BoundaryCountedNativeWord (gradeChart betaWord)
end N
namespace BD
export NativeDelta.BetaDecoder (nextNative)
end BD

local instance groups (grade : Nat) (slot : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade slot) := L.groups (PairValue C.Value) grade slot

abbrev Grade (grade : Nat) := L.Value (PairValue C.Value) grade
abbrev WordAt (grade : Nat) := Formal ℤ (Grade grade) C.Var ()

attribute [local irreducible] AS.localNativeReceipt

variable (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)

abbrev chart (grade : Nat) : WordAt grade ≃ₗ[ℤ] WordAt grade :=
  Rechart.word (N.gradeChart coordinate n grade) ()

private theorem cast_chart {first second : Nat} (same : first=second) (source : WordAt first) :
    let cast := Eq.mp (congrArg (fun grade => WordAt first →ₗ[ℤ] WordAt grade) same) LinearMap.id
    chart coordinate n second (cast source) = cast (chart coordinate n first source) := by
  cases same
  rfl

private theorem born_chart (native : NativeSigma.NativePacket) (source : WordAt native.1) :
    chart coordinate n (AS.bornAfterNative native).1 (W.bornWord native source) =
      W.bornWord native (chart coordinate n native.1 source) :=
  cast_chart coordinate n (show native.1=(AS.bornAfterNative native).1 from rfl) source

private theorem admission_chart (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
    (source : WordAt (packet.1+1)) :
    chart coordinate n (AS.nativeAfterAdmission factory packet).1 (W.admissionWord factory packet source) =
      W.admissionWord factory packet (chart coordinate n (packet.1+1) source) :=
  cast_chart coordinate n (AS.nativeAfterAdmission_grade factory packet).symm source

private theorem lift_chart (grade : Nat) (source : WordAt grade) :
    chart coordinate n (grade+1) (liftMap (R := ℤ) (Value := Grade grade) source) =
      liftMap (R := ℤ) (Value := Grade grade) (chart coordinate n grade source) :=
  Rechart.word_lift (N.gradeChart coordinate n grade) source

variable (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)

local notation "born" => AS.bornAfterNative native
local notation "next" => BD.nextNative factory native

private theorem admit_chart (source : WordAt native.1) :
    chart coordinate n (next).1 (W.admissionWord factory born (liftMap (R := ℤ) (W.bornWord native source))) =
      W.admissionWord factory born (liftMap (R := ℤ) (W.bornWord native (chart coordinate n native.1 source))) :=
  (admission_chart coordinate n factory born _).trans
    ((congrArg (W.admissionWord factory born) (lift_chart coordinate n born.1 _)).trans
      (congrArg (fun word => W.admissionWord factory born (liftMap (R := ℤ) word))
        (born_chart coordinate n native source)))

/-- The full admitted beta is produced by the original admission of the charted source boundary. -/
theorem beta_source :
    N.betaWord coordinate n factory native =
      W.admissionWord factory born (liftMap (R := ℤ)
        (W.bornWord native (chart coordinate n native.1 (W.nativeBoundary native)))) :=
  admit_chart coordinate n factory native (W.nativeBoundary native)

/-- The original birth cast and both old/effect lifts commute with the full word chart. -/
theorem next_transfer (source : WordAt native.1) :
    chart coordinate n ((next).1+1) (W.nativeReceiptTransfer factory native source) =
      W.nativeReceiptTransfer factory native (chart coordinate n native.1 source) :=
  (lift_chart coordinate n (next).1 _).trans
    (congrArg (liftMap (R := ℤ)) (admit_chart coordinate n factory native source))

/-- Follow the original ordered paid steps through the actual next receipt transfer. -/
def generatedNext : WordAt ((next).1+1) :=
  ((SourceOperationPaidRelations.words
    (Rechart.trace (N.gradeChart coordinate n native.1) (W.nativeTrace native))).map
      (W.nativeReceiptTransfer factory native)).sum

theorem generated_next_source :
    generatedNext coordinate n factory native =
      chart coordinate n ((next).1+1) (W.nativeReceiptTransfer factory native (W.nativeBoundary native)) := by
  have ordered := Rechart.paid_words (N.gradeChart coordinate n native.1) (W.nativeTrace native)
  have boundary : (SourceOperationPaidRelations.words (W.nativeTrace native)).sum = W.nativeBoundary native :=
    SourceOperationPaidRelations.paid_boundary (W.nativeTrace native)
  unfold generatedNext
  rw [ordered, ← map_list_sum (W.nativeReceiptTransfer factory native),
    ← map_list_sum (chart coordinate n native.1), boundary]
  exact (next_transfer coordinate n factory native (W.nativeBoundary native)).symm

abbrev originalRelations : Submodule ℤ (WordAt ((next).1+1)) :=
  (W.nativeHistory next).relationClosure

abbrev nextRelations : Submodule ℤ (WordAt ((next).1+1)) :=
  Submodule.map (chart coordinate n ((next).1+1)).toLinearMap (originalRelations factory native)

abbrev relationChart : ↥(originalRelations factory native) ≃ₗ[ℤ] ↥(nextRelations coordinate n factory native) :=
  (chart coordinate n ((next).1+1)).submoduleMap (originalRelations factory native)

private theorem generated_member
    (original : W.nativeReceiptTransfer factory native (W.nativeBoundary native) ∈
      originalRelations factory native) :
    generatedNext coordinate n factory native ∈ nextRelations coordinate n factory native := by
  rw [generated_next_source]
  exact Submodule.mem_map.mpr ⟨_,original,rfl⟩

private def of_written
    (original : W.nativeReceiptTransfer factory native (W.nativeBoundary native) ∈
      (W.nativeHistory (AS.nativeAfterAdmission factory (AS.bornAfterNative native))).relationClosure) :
    ↥(nextRelations coordinate n factory native) :=
  ⟨generatedNext coordinate n factory native,generated_member coordinate n factory native original⟩

private theorem generated_readback
    (original : W.nativeReceiptTransfer factory native (W.nativeBoundary native) ∈
      (W.nativeHistory (AS.nativeAfterAdmission factory (AS.bornAfterNative native))).relationClosure) :
    (relationChart coordinate n factory native).symm (of_written coordinate n factory native original) =
      ⟨W.nativeReceiptTransfer factory native (W.nativeBoundary native),original⟩ :=
  Subtype.ext ((congrArg (chart coordinate n ((next).1+1)).symm
    (generated_next_source coordinate n factory native)).trans
      ((chart coordinate n ((next).1+1)).symm_apply_apply _))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "F" => D.factory observation nontrivial half
local notation "nativeAt" => originalNative observation nontrivial half depth

attribute [local irreducible] W.nativeHistory W.nativeReceiptTransfer W.nativeBoundary

private theorem literal_member (ordinal : Nat) :
    W.nativeReceiptTransfer F (nativeAt (ordinal+1)) (W.nativeBoundary (nativeAt (ordinal+1))) ∈
      (W.nativeHistory (AS.nativeAfterAdmission F (AS.bornAfterNative (nativeAt (ordinal+1))))).relationClosure :=
  W.original_sigma_next_relation observation nontrivial half depth (ordinal+1)

/-- Read the already written relation at its literal next grade in the finite coordinates. -/
def actualRelation (ordinal n : Nat) :=
  of_written c n F (nativeAt (ordinal+1)) (literal_member observation nontrivial half depth ordinal)

theorem actual_relation_readback (ordinal n : Nat) :
    type_of% (generated_readback c n F (nativeAt (ordinal+1))
      (literal_member observation nontrivial half depth ordinal)) :=
  generated_readback c n F (nativeAt (ordinal+1)) (literal_member observation nontrivial half depth ordinal)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeWrite
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
