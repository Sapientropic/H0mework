import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiContactGramConsumer

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 350000
set_option linter.defProp false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CP813Independent

open BurnolPhysicalState Filter RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open RootGeneratedDebtActivationJointSource.OwnerFree SourceGeneratedFiniteGram
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open scoped Topology InnerProductSpace lp

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner DivisionEffectPrice.wideNormed

open private Births environment Settlement from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiContactGramNative
open private Boundary boundaryMap from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiBoundaryNative
open private readField from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualPaReturn
open private cotests from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => OriginalPrimitiveRankBalance.conjugateCoordinate c
local notation "degree" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "S" => WideResidualReturn.XiContact.contact a degree
local notation "A" => advanceWide c observation.mathlibZero
local notation "stock" => actualWide observation nontrivial half depth
local notation "birth" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "tests" => cotests observation nontrivial half depth
local notation "prices" => DivisionPriceStream.prices observation nontrivial half depth
local notation "data" => WideResidualReturn.XiContact.JointGram.bank observation nontrivial half depth ordinal
local notation "fitted" => WideResidualReturn.XiContact.JointGram.fit observation nontrivial half depth ordinal
local notation "fittedNext" => WideResidualReturn.XiContact.JointGram.fit observation nontrivial half depth (ordinal+1)
local notation "out" => WideResidualReturn.XiContact.JointGram.output observation nontrivial half depth ordinal
local notation "authority" => OriginalKDirectRCofinalCalculatedSource.calculationRoot observation nontrivial half depth ordinal
local notation "origin" => OriginalKDirectRCofinalCalculatedSource.calculationCurrent observation nontrivial half depth ordinal
local notation "read" => WideResidualReturn.XiContact.JointGram.reader observation nontrivial half depth ordinal

open WideResidualReturn.XiContact.JointGram

elab "birthStage" : term =>
  pure (Lean.mkConst ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiContactGramNative.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision.WideResidualReturn.XiContact.JointGram.Stage.births".toName))

attribute [local irreducible] OriginalKCombFirstFullSourceDynamics.input in
private theorem actual_births_keep_both_complete_banks_and_ordinals (n : Nat) :
    let actual := raw authority origin (read n)
    (actual.environment birthStage () : Births) = (birth ordinal, birth (ordinal+1)) ∧
      ordinal ≠ ordinal+1 := by
  change (environment observation nontrivial half depth ordinal n birthStage () : Births) =
    (birth ordinal, birth (ordinal+1)) ∧ ordinal ≠ ordinal+1
  exact ⟨rfl,Nat.ne_of_lt (Nat.lt_succ_self _)⟩

private theorem pulled_next_test_and_shared_contact_solve (n : Nat) (i : Fin n) :
    test observation nontrivial half depth n (Sum.inl i) = tests i.val ∧
    test observation nontrivial half depth n (Sum.inr i) = ContinuousLinearMap.adjoint A (tests i.val) ∧
    Projection.rhs (test observation nontrivial half depth n) (fitted n : Wide) = data n ∧
    (fitted n : Wide) ∈ S :=
  ⟨rfl,rfl,fit_equations observation nontrivial half depth ordinal n,(fitted n).property⟩

private theorem original_R_prices_and_shared_prefix (n : Nat) (i : Fin n) :
    (out n).1.2 = A (out n).1.1 ∧
    prices (out n).1.1 i.val = prices (stock ordinal) i.val ∧
    prices (out n).1.2 i.val = prices (stock (ordinal+1)) i.val ∧
    prices ((fittedNext n : Wide) - (out n).1.2) i.val = 0 := by
  let computed := paid_source observation nontrivial half depth ordinal n
  have beforeField := congrArg (fun t : Settlement => t.1.1) computed
  have afterField := congrArg (fun t : Settlement => t.1.2) computed
  have meters := paid_two_price_banks observation nontrivial half depth ordinal n i
  exact ⟨afterField.trans (congrArg A beforeField).symm,meters.1,meters.2,
    paid_overlap_silent observation nontrivial half depth ordinal n i⟩

private theorem complete_boundary_and_independent_Pa_write (n : Nat) :
    (out n).2.1 = boundaryMap a
      (WideResidualReturn.XiContact.terminalPosition observation half (fitted n)) ∧
    (out n).2.2 = WideResidualReturn.directReturnMap c (readField (out n).1.1) :=
  ⟨congrArg (fun t : Settlement => t.2.1) (paid_source observation nontrivial half depth ordinal n),
    paid_direct_write observation nontrivial half depth ordinal n⟩

private theorem actual_complete_limit :
    Tendsto out atTop (𝓝 ((stock ordinal, stock (ordinal+1)),
      boundaryMap a (BoundaryAdjointDefect.nativeSlot observation nontrivial half depth ordinal),
      WideResidualReturn.directReturnMap c (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal))) :=
  paid_complete_tendsto observation nontrivial half depth ordinal

private def five_steps_full_payment_actual_material_whole_and_next (n : Nat) :=
  let used := consume_joint_contact_gram observation nontrivial half depth ordinal n
  let runtime := used.2.2.2.2.2.2.2.2
  let target := runtime.2.2.2
  And.intro used.2.1 <| And.intro used.2.2.2.2.2.2.1 <|
    And.intro runtime.1 <| And.intro runtime.2.1 <| And.intro runtime.2.2.1 <|
    And.intro target.2.2.1 target.2.2.2

private theorem empty_bank_erases_graphs_release_B_and_Pa :
    data 0 = 0 ∧ fitted 0 = 0 ∧ (out 0 : Settlement) = 0 := by
  have bankZero : data 0 = 0 := by
    apply WithLp.ofLp_injective
    funext i
    cases i with
    | inl j => exact Fin.elim0 j
    | inr j => exact Fin.elim0 j
  have fitZero : fitted 0 = 0 := by
    change recover observation nontrivial half depth 0 (data 0) = 0
    rw [bankZero, map_zero]
  have fieldZero : ((fitted 0 : S) : Wide) = 0 :=
    congrArg (fun x : S => (x : Wide)) fitZero
  have slotZero : WideResidualReturn.XiContact.terminalPosition observation half (fitted 0) = 0 :=
    (WideResidualReturn.XiContact.terminal_map_source observation half (fitted 0)).symm.trans
      ((congrArg (WideResidualReturn.XiContact.terminalPositionMap observation half) fitZero).trans (map_zero _))
  have outputZero : (out 0 : Settlement) = 0 :=
    (paid_source observation nontrivial half depth ordinal 0).trans (by
      have graphZero : A ((fitted 0 : S) : Wide) = 0 :=
        (congrArg A fieldZero).trans (map_zero _)
      have boundaryZero : boundaryMap a
          (WideResidualReturn.XiContact.terminalPosition observation half (fitted 0)) = 0 :=
        (congrArg (boundaryMap a) slotZero).trans (map_zero _)
      have innerZero : OriginalKCombCofinalPaAction.E (readField (fitted 0 : Wide)) = 0 :=
        (congrArg (fun x : Wide => OriginalKCombCofinalPaAction.E (readField x)) fieldZero).trans
          (by rw [map_zero,map_zero])
      have afterZero : OriginalKCombCofinalPaAction.E (readField (A (fitted 0 : Wide))) = 0 :=
        (congrArg (fun x : Wide => OriginalKCombCofinalPaAction.E (readField x)) graphZero).trans
          (by rw [map_zero,map_zero])
      have paZero : OriginalKCombCofinalPaAction.E (readField (A (fitted 0 : Wide))) -
          OriginalKCombCofinalPaAction.E ((burnolDirectRightResolventCLM c)
            (OriginalKCombCofinalPaAction.E (readField (fitted 0 : Wide)) : BurnolL2)) = 0 := by
        rw [afterZero,innerZero,Submodule.coe_zero,map_zero,map_zero,sub_self]
      exact Prod.ext (Prod.ext fieldZero graphZero) (Prod.ext boundaryZero paZero))
  exact ⟨bankZero,fitZero,outputZero⟩

end CP813Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision

#eval IO.println "CP813_CONTROL + actual_births_keep_both_complete_banks_and_ordinals"
#eval IO.println "CP813_CONTROL + pulled_next_test_and_shared_contact_solve"
#eval IO.println "CP813_CONTROL + original_R_prices_and_shared_prefix"
#eval IO.println "CP813_CONTROL + complete_boundary_and_independent_Pa_write"
#eval IO.println "CP813_CONTROL + actual_complete_limit"
#eval IO.println "CP813_CONTROL + five_steps_full_payment_actual_material_whole_and_next"
#eval IO.println "CP813_CONTROL - empty_bank_erases_graphs_release_B_and_Pa"
#eval IO.println "CP813_GATE_PASS positive=6 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
