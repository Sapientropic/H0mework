import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedNativeQuery
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Admission

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeUpdate

open BurnolPhysicalState SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift RootInquiryCompletion
open OriginalKCofinalFullBranchFibre.KernelWrite

namespace Q
export BoundaryCountedNativeQuery (configuration steps)
export BoundaryCountedNativeQuery.Stock (state presentation query)
export BoundaryCountedNativeQuery.Source (nativePresentation)
export BoundaryCountedNativeQuery.Install (Raw resultFace result_value result_history)
export BoundaryCountedNativeQuery.Origin (Occurrence Current)
end Q
namespace N
export BoundaryCountedNativeWord (NextValues nextChart gradeChart betaWord betaInventory updated)
end N
namespace W
export BoundaryCountedNativeWrite (Grade chart beta_source)
export NativeSigma.Writeback (receiptSelected nativeTrace nativeBoundary bornWord admissionWord)
end W
namespace B
export NativeDelta.BetaDecoder (nextNative)
end B
namespace Ordered
export SourceInventoryExecutionFeed.WordReceipt (orderedExpression)
export SourceInventoryExecutionFeed.AdmissionReceipt (ordered_literal_read)
end Ordered

local instance groups (grade : Nat) (slot : Unit) : AddCommGroup (W.Grade grade slot) :=
  L.groups (PairValue C.Value) grade slot

variable (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
variable (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)

local notation "next" => B.nextNative factory native
local notation "born" => AS.bornAfterNative native
local notation "V" => N.NextValues factory native
local notation "e" => N.nextChart coordinate n factory native
private abbrev admit : Formal ℤ (W.Grade native.1) C.Var () →ₗ[ℤ] Formal ℤ V C.Var () :=
  (W.admissionWord factory born).comp ((liftMap (R := ℤ)).comp (W.bornWord native))

/-- Each original paid step supplies its own first lifted admitted word. -/
def admittedSteps : List (Formal ℤ V C.Var ()) :=
  (SourceOperationPaidRelations.words
    (Rechart.trace (N.gradeChart coordinate n native.1) (W.nativeTrace native))).map (admit factory native)

theorem admitted_boundary :
    (admittedSteps coordinate n factory native).sum = N.betaWord coordinate n factory native := by
  have original : (SourceOperationPaidRelations.words (W.nativeTrace native)).sum = W.nativeBoundary native :=
    SourceOperationPaidRelations.paid_boundary (W.nativeTrace native)
  rw [admittedSteps, Rechart.paid_words, ← map_list_sum (admit factory native),
    ← map_list_sum (W.chart coordinate n native.1), original]
  exact (W.beta_source coordinate n factory native).symm

theorem original_carried_steps :
    (admittedSteps coordinate n factory native).map (liftMap (R := ℤ)) =
      Q.steps coordinate n factory native := by
  rw [admittedSteps, Q.steps, List.map_map]
  rfl

abbrev selected := W.receiptSelected next
abbrev base := Q.state (selected factory native) (Q.configuration factory native)
local notation "f" => selected factory native
local notation "stock" => base factory native

abbrev sourceMaterial := NativeSigma.RB.transported (Value := V) (Var := C.Var) f (next).2.2.1
private def decoderEnvironment : Env V C.Var := Rechart.env e (sourceMaterial factory native).environment
private def decoderIncrement : Env V C.Var := Rechart.env e (sourceMaterial factory native).increment
local notation "before" => decoderEnvironment coordinate n factory native
local notation "delta" => decoderIncrement coordinate n factory native

private abbrev updateExpression : Expr (PairValue V) C.Var () :=
  liftExpr (Ordered.orderedExpression (admittedSteps coordinate n factory native))

/-- The actual selected decoder supplies both the old environment and its registered increment. -/
def reader {current : Q.Current (f).registered} (_ : Q.Occurrence f (current := current)) :
    Q.Raw (Value := PairValue V) (Var := C.Var) (sort := ()) :=
  ⟨pairEnvironment before delta,updateExpression coordinate n factory native⟩

local notation "read" => reader coordinate n factory native

def request :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.query stock read
    (Q.query f (Q.configuration factory native))

def inquiry :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.state stock read

def result :=
  (Q.resultFace stock read).rootRead

def resultValue : PairValue V () := (result coordinate n factory native).2.2.1

theorem original_ledger :
    (inquiry coordinate n factory native).root.toAuthoritativeRoot.toLedgerRoot =
      (stock).root.toAuthoritativeRoot.toLedgerRoot := rfl

theorem original_visit : HEq (inquiry coordinate n factory native).visit (stock).visit := HEq.rfl

set_option backward.isDefEq.respectTransparency false in
private theorem installed_value :
    resultValue coordinate n factory native =
      (updateExpression coordinate n factory native).eval (pairEnvironment before delta) :=
  Q.result_value stock read

private theorem literal_inventory {A X : Unit → Type} [∀ slot, AddCommGroup (A slot)]
    (environment increment : Env A X) (words : List (Formal ℤ A X ())) :
    (liftExpr (Ordered.orderedExpression words)).eval (pairEnvironment environment increment) =
      updateInventory (R := ℤ) environment increment words.sum :=
  (Ordered.ordered_literal_read words (pairEnvironment environment increment)).trans
    (LinearMap.congr_fun (evaluation_liftMap (R := ℤ) (s := ()) environment increment) words.sum)

/-- One paid expression computes the complete old/effect pair of the actual admitted beta. -/
theorem result_source : resultValue coordinate n factory native = N.betaInventory coordinate n factory native := by
  let words := admittedSteps coordinate n factory native
  let beta := N.betaWord coordinate n factory native
  calc
    resultValue coordinate n factory native =
        (updateExpression coordinate n factory native).eval (pairEnvironment before delta) :=
      installed_value coordinate n factory native
    _ = updateInventory (R := ℤ) before delta words.sum := literal_inventory before delta words
    _ = updateInventory (R := ℤ) before delta beta :=
      congrArg (updateInventory (R := ℤ) before delta) (admitted_boundary coordinate n factory native)
    _ = N.betaInventory coordinate n factory native := rfl

theorem result_budget :
    (result coordinate n factory native).2.1.2.length =
      remaining (liftExpr (Ordered.orderedExpression (admittedSteps coordinate n factory native))) :=
  Q.result_history stock read

def writtenUpdate : V () :=
  (resultValue coordinate n factory native).1+(resultValue coordinate n factory native).2

theorem updated_source : writtenUpdate coordinate n factory native = N.updated coordinate n factory native := by
  have sum := congrArg (fun value : PairValue V () => value.1+value.2) (result_source coordinate n factory native)
  have inverse : N.updated coordinate n factory native =
      (N.betaInventory coordinate n factory native).1+(N.betaInventory coordinate n factory native).2 :=
    updated_residual_readout before delta (N.betaWord coordinate n factory native)
  exact sum.trans inverse.symm

private theorem receipt_presentation (packet : NativeSigma.NativePacket) :
    Q.nativePresentation packet (AS.localNativeReceipt packet).1 =
      Q.presentation (W.receiptSelected packet) (AS.stockCfg packet.2.2.1) :=
  rfl

attribute [local irreducible] AS.localNativeReceipt

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "F" => D.factory observation nontrivial half
local notation "nativeAt" => originalNative observation nontrivial half depth
local notation "runtime" => originalRuntime observation nontrivial half depth

/-- The completed native receipt in the original runtime supplies this calculation's visit. -/
theorem actual_query_current (ordinal : Nat) :
    ((runtime).stateAt (originalBirthTick observation nontrivial half depth (ordinal+2))).engine.node =
      .active (Q.presentation (selected F (nativeAt (ordinal+1))) (Q.configuration F (nativeAt (ordinal+1)))) := by
  have current := ExactCurrent.original_selected_current observation nontrivial half depth (ordinal+2)
  have identified := congrArg (fun packet =>
    RootInquiryProcessNode.active (Q.nativePresentation packet (AS.localNativeReceipt packet).1))
    (NativeDelta.BetaDecoder.Rooting.native_successor observation nontrivial half depth (ordinal+1))
  exact current.trans (identified.trans
    (congrArg RootInquiryProcessNode.active (receipt_presentation (B.nextNative F (nativeAt (ordinal+1))))))

theorem actual_physical (ordinal n : Nat) :
    NativeSigma.collapseNative F (AS.bornAfterNative (nativeAt (ordinal+1)))
      (writtenUpdate c n F (nativeAt (ordinal+1))) =
        BoundaryCountedNativeBeta.beta observation nontrivial half depth ordinal n :=
  (congrArg (NativeSigma.collapseNative F (AS.bornAfterNative (nativeAt (ordinal+1))))
    (updated_source c n F (nativeAt (ordinal+1)))).trans
    (BoundaryCountedNativeWord.actual_physical observation nontrivial half depth ordinal n)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeUpdate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
