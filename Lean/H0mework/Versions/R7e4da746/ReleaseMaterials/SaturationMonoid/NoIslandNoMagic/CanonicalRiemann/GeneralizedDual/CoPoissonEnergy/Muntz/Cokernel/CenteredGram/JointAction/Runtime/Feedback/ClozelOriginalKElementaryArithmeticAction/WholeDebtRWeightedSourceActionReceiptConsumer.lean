import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRGapStateReceiptConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRWeightedSourceActionSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
-- Proof packets have large dependent types; kernel checking needs no let-to-have or runtime codegen.
set_option cleanup.letToHave false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRWeightedSourceActionReceiptConsumer
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalKPairedBEulerJunctionSource OriginalWholeDebtRWeightedSourceActionSource
open private gapPrice gap_source_price from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRGapStateReceiptConsumer

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "seed" => OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed

private def writtenPrice : ℂ :=
  -((pairedMellinTranslationCharacter (c).value junctionShift-
      pairedMellinTranslationCharacter (star (c).value) junctionShift)*
      OriginalRieszFinitePairing.kernelSelfSource c+
    (1/2 : ℂ)*star (OriginalWholeDebtRWeightedSourceActionSource.sourcePrice c))

private theorem weighted_source_price :
    burnolPaFixedShiftResidual c observation.mathlibZero=writtenPrice observation nontrivial half := by
  simpa only [writtenPrice,neg_neg] using
    congrArg (fun price : ℂ => -price) (actual_fixed_residual_source c observation.mathlibZero)

local elab "weightedWritten% " readStx:term " using " equationStx:term : term => do
  let read ← Lean.Elab.Term.elabTerm readStx none
  let equation ← Lean.Elab.Term.elabTerm equationStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let read ← Lean.instantiateMVars read
  let equation ← Lean.instantiateMVars equation
  let readType ← Lean.Meta.inferType read
  let equationType ← Lean.Meta.whnf (← Lean.Meta.inferType equation)
  unless equationType.isAppOfArity ``Eq 3 do
    throwError "expected the generated source price equation"
  let domain := equationType.getAppArgs[0]!
  let oldPrice := equationType.getAppArgs[1]!
  Lean.Meta.withLocalDeclD `price domain fun price => do
    let transported := readType.replace fun expression =>
      if expression == oldPrice then some price else none
    if transported == readType then
      throwError "the actual receipt reads do not expose the original source price"
    let family ← Lean.Meta.mkLambdaFVars #[price] transported
    let typeEquation ← Lean.Meta.mkAppM ``congrArg #[family,equation]
    Lean.Meta.mkAppM ``Eq.mp #[typeEquation,read]

private noncomputable def consume (ordinal : Nat)
    (prior : type_of% (OriginalWholeDebtRGapStateReceiptConsumer.actual_gap_state_source_whole_next
      observation nontrivial half depth ordinal)) :=
  let equation := (gap_source_price observation nontrivial half).symm.trans
    (weighted_source_price observation nontrivial half)
  weightedWritten% prior.2.2.2 using equation

private noncomputable def Result (ordinal : Nat) : Sort _ :=
  Σ' prior : type_of% (OriginalWholeDebtRGapStateReceiptConsumer.actual_gap_state_source_whole_next
      observation nontrivial half depth ordinal),
    PProd (prior=OriginalWholeDebtRGapStateReceiptConsumer.actual_gap_state_source_whole_next
        observation nontrivial half depth ordinal)
      (PProd
        ((type_of% (actual_weighted_band c)) ∧ (type_of% (actual_constant_band c)) ∧
          (type_of% (actual_finite_price_source c)) ∧
          (type_of% (weighted_source_price observation nontrivial half)))
        (type_of% (consume observation nontrivial half depth ordinal prior)))

/-- The same complete indexed packages consume the generated weighted source action price. -/
noncomputable opaque actual_weighted_source_action_whole_next (ordinal : Nat) :
    Result observation nontrivial half depth ordinal := by
  let prior := OriginalWholeDebtRGapStateReceiptConsumer.actual_gap_state_source_whole_next
    observation nontrivial half depth ordinal
  exact ⟨prior,⟨rfl,⟨⟨actual_weighted_band c,actual_constant_band c,actual_finite_price_source c,
    weighted_source_price observation nontrivial half⟩,
    consume observation nontrivial half depth ordinal prior⟩⟩⟩

end OriginalWholeDebtRWeightedSourceActionReceiptConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
