import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment
import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiContactGramNative

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 150000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn.XiContact.JointGram

open BurnolPhysicalState Filter RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open RootGeneratedDebtActivationJointSource.OwnerFree
open SourceOperationScalarPresentation
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open scoped Topology InnerProductSpace

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner
attribute [local instance] DivisionEffectPrice.wideNormed

open private Settlement from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiContactGramNative
open private Boundary boundaryMap from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiBoundaryNative
open private readField from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualPaReturn
open private direct_return_eq from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WidePaOverlap
open private native_read from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiAdjointStock
open private cotests price_read from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => OriginalPrimitiveRankBalance.conjugateCoordinate c
local notation "degree" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "A" => advanceWide c observation.mathlibZero
local notation "stock" => actualWide observation nontrivial half depth
local notation "fitted" => fit observation nontrivial half depth ordinal
local notation "fittedNext" => fit observation nontrivial half depth (ordinal+1)
local notation "out" => output observation nontrivial half depth ordinal
local notation "tests" => cotests observation nontrivial half depth
local notation "prices" => PriceStream.prices observation nontrivial half depth
local notation "authority" => OriginalKDirectRCofinalCalculatedSource.calculationRoot observation nontrivial half depth ordinal
local notation "origin" => OriginalKDirectRCofinalCalculatedSource.calculationCurrent observation nontrivial half depth ordinal
local notation "read" => reader observation nontrivial half depth ordinal

/-- Independent original Riesz prices on both written graphs reproduce both actual observed banks. -/
theorem paid_two_price_banks (n : Nat) (i : Fin n) :
    prices (out n).1.1 i.val = prices (stock ordinal) i.val ∧
      prices (out n).1.2 i.val = prices (stock (ordinal+1)) i.val := by
  let x := fitted n
  let original := stock ordinal
  let next := stock (ordinal+1)
  let meter := innerSL ℂ (tests i.val)
  have computed := congrArg (fun t : Settlement => t.1) (paid_source observation nontrivial half depth ordinal n)
  have readout (y : Wide) : prices y i.val = meter y :=
    congrFun (price_read observation nontrivial half depth y) i.val
  have observationSource := (fit_equations observation nontrivial half depth ordinal n).trans
    (bank_source observation nontrivial half depth ordinal n)
  have old : meter (x : Wide) = meter original :=
    congrArg (fun bank : JointBank n => bank (Sum.inl i)) observationSource
  have after : inner ℂ (ContinuousLinearMap.adjoint A (tests i.val)) (x : Wide) =
      inner ℂ (ContinuousLinearMap.adjoint A (tests i.val)) original :=
    congrArg (fun bank : JointBank n => bank (Sum.inr i)) observationSource
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    actual_wide_next observation nontrivial half depth ordinal] at after
  have beforeField : (out n).1.1 = (x : Wide) := congrArg (fun pair : Wide × Wide => pair.1) computed
  have nextField : (out n).1.2 = A (x : Wide) := congrArg (fun pair : Wide × Wide => pair.2) computed
  exact ⟨(congrArg (fun y : Wide => prices y i.val) beforeField).trans
    ((readout (x : Wide)).trans (old.trans (readout original).symm)),
    (congrArg (fun y : Wide => prices y i.val) nextField).trans
      ((readout (A (x : Wide))).trans (after.trans (readout next).symm))⟩

/-- Finite rows need not agree as whole graphs. Their actual discrepancy is invisible on the shared K bank. -/
theorem paid_overlap_silent (n : Nat) (i : Fin n) :
    prices ((fittedNext n : Wide) - (out n).1.2) i.val = 0 := by
  let nextFit := fittedNext n
  let meter := innerSL ℂ (tests i.val)
  have nextSource := (fit_equations observation nontrivial half depth (ordinal+1) n).trans
    (bank_source observation nontrivial half depth (ordinal+1) n)
  have current : meter (nextFit : Wide) = meter (stock (ordinal+1)) :=
    congrArg (fun bank : JointBank n => bank (Sum.inl i)) nextSource
  have old := (paid_two_price_banks observation nontrivial half depth ordinal n i).2
  have readout (y : Wide) : prices y i.val = meter y :=
    congrFun (price_read observation nontrivial half depth y) i.val
  have same : meter (out n).1.2 = meter (stock (ordinal+1)) :=
    (readout (out n).1.2).symm.trans (old.trans (readout (stock (ordinal+1))))
  rw [readout, map_sub, current, same, sub_self]

theorem paid_direct_write (n : Nat) :
    (out n).2.2 = directReturnMap c (readField (out n).1.1) := by
  let x := fitted n
  have result := paid_source observation nontrivial half depth ordinal n
  have fields := congrArg (fun t : Settlement => t.1) result
  have pa : (out n).2.2 =
      Pa.E (readField (A (x : Wide))) - Pa.E ((burnolDirectRightResolventCLM c)
        (Pa.E (readField (x : Wide)) : BurnolL2)) :=
    congrArg (fun t : Settlement => t.2.2) result
  have changeField := congrArg (fun raw : BurnolL2 => Pa.E raw -
    Pa.E ((burnolDirectRightResolventCLM c) (Pa.E (readField (x : Wide)) : BurnolL2)))
    (native_read c observation.mathlibZero (x : Wide))
  have law := direct_return_eq observation half (readField (x : Wide))
  have field : (out n).1.1 = (x : Wide) := congrArg (fun pair : Wide × Wide => pair.1) fields
  exact pa.trans (changeField.trans (law.symm.trans
    (congrArg (fun value : Wide => directReturnMap c (readField value)) field.symm)))

theorem paid_relation_stock (n : Nat) :
    DenseDivisionPrice.relationStock observation half (out n).1.2 =
      advanceStock c (DenseDivisionPrice.relationStock observation half (out n).1.1) := by
  let x := fitted n
  let rel := DenseDivisionPrice.relationStock observation half
  have fields := congrArg (fun t : Settlement => t.1) (paid_source observation nontrivial half depth ordinal n)
  have old : (out n).1.1 = (x : Wide) := congrArg (fun pair : Wide × Wide => pair.1) fields
  have next : (out n).1.2 = A (x : Wide) := congrArg (fun pair : Wide × Wide => pair.2) fields
  exact (congrArg rel next).trans ((DenseDivisionPrice.relation_advance observation nontrivial half
    (x : Wide)).symm.trans (congrArg (fun y : Wide => advanceStock c (rel y)) old.symm))

theorem paid_complete_tendsto :
    Tendsto (out) atTop (𝓝 ((stock ordinal, stock (ordinal+1)),
      boundaryMap a (BoundaryAdjointDefect.nativeSlot observation nontrivial half depth ordinal),
      directReturnMap c (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal))) := by
  let x : ↥(contact a degree) :=
    ⟨stock ordinal, literal_contact observation nontrivial half depth ordinal⟩
  let forward := (contact a degree).subtypeL
  let images := forward.prod ((A).comp forward)
  let boundary := (boundaryMap a).comp (terminalPositionMap observation half)
  let pa := (directReturnMap c).comp (readField.comp forward)
  let process := images.prod (boundary.prod pa)
  have converges := (process.continuous.tendsto x).comp (fit_tendsto observation nontrivial half depth ordinal)
  have terminal : terminalPositionMap observation half x =
      BoundaryAdjointDefect.nativeSlot observation nontrivial half depth ordinal :=
    (terminal_map_source observation half x).trans (terminal_original observation nontrivial half depth ordinal)
  have limit : process x = ((stock ordinal, stock (ordinal+1)),
      boundaryMap a (BoundaryAdjointDefect.nativeSlot observation nontrivial half depth ordinal),
      directReturnMap c (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal)) := by
    change ((stock ordinal, A (stock ordinal)), boundaryMap a (terminalPositionMap observation half x),
      directReturnMap c (readField (stock ordinal))) = _
    rw [terminal, actual_wide_next]
    rfl
  rw [limit] at converges
  refine converges.congr' (Eventually.of_forall fun n => ?_)
  have terminalFit := terminal_map_source observation half (fitted n)
  have direct := direct_return_eq observation half (readField (fitted n : Wide))
  have pair : directReturnMap c (readField (fitted n : Wide)) =
      Pa.E (readField (A (fitted n : Wide))) -
        Pa.E ((burnolDirectRightResolventCLM c) (Pa.E (readField (fitted n : Wide)) : BurnolL2)) := by
    exact direct.trans (congrArg (fun raw : BurnolL2 => Pa.E raw -
      Pa.E ((burnolDirectRightResolventCLM c) (Pa.E (readField (fitted n : Wide)) : BurnolL2)))
      (native_read c observation.mathlibZero (fitted n : Wide))).symm
  exact (congrArg₂ (fun (v : PositionField) (p : BurnolPaAmbientCarrier) =>
    (((fitted n : Wide), A (fitted n : Wide)), boundaryMap a v,p)) terminalFit pair).trans
    (paid_source observation nontrivial half depth ordinal n).symm

theorem paid_whole_word (n : Nat) :
    let trace := Eval.trace authority origin (read n)
    let charges := SourceOperationPaidRelations.fullPayment trace
    let relation := SourceOperationPaidRelations.writePayment trace charges
    SourceOperationPaidRelations.readPayment trace relation = charges ∧
      relation =
        Finsupp.single (raw authority origin (read n)).expression 1 -
          Finsupp.single (.const (out n)) 1 := by
  let trace := Eval.trace authority origin (read n)
  let charges := SourceOperationPaidRelations.fullPayment trace
  exact ⟨SourceOperationPaidRelations.read_write_payment trace charges,
    (SourceOperationPaidRelations.write_full_payment trace).trans
      (Eval.relation_boundary (R := ℤ) authority origin (read n))⟩

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "consume_joint_contact_gram"

theorem consume_joint_contact_gram (n : Nat) :
    type_of% (paid_source observation nontrivial half depth ordinal n) ∧
    type_of% (paid_steps observation nontrivial half depth ordinal n) ∧
    (∀ i, type_of% (paid_two_price_banks observation nontrivial half depth ordinal n i)) ∧
    (∀ i, type_of% (paid_overlap_silent observation nontrivial half depth ordinal n i)) ∧
    type_of% (paid_direct_write observation nontrivial half depth ordinal n) ∧
    type_of% (paid_relation_stock observation nontrivial half depth ordinal n) ∧
    type_of% (paid_whole_word observation nontrivial half depth ordinal n) ∧
    type_of% (paid_complete_tendsto observation nontrivial half depth ordinal) ∧
    type_of% (Eval.original_material authority origin (read n)) ∧
    type_of% (Eval.relation_boundary (R := ℤ) authority origin (read n)) ∧
    type_of% (Relations.boundary_in_inventory authority origin (read n)
      (Calculation.targetRuntime authority origin (read n))) ∧
    type_of% (Calculation.target_factorizes authority origin (read n)) :=
  ⟨paid_source observation nontrivial half depth ordinal n,
    paid_steps observation nontrivial half depth ordinal n,
    paid_two_price_banks observation nontrivial half depth ordinal n,
    paid_overlap_silent observation nontrivial half depth ordinal n,
    paid_direct_write observation nontrivial half depth ordinal n,
    paid_relation_stock observation nontrivial half depth ordinal n,
    paid_whole_word observation nontrivial half depth ordinal n,
    paid_complete_tendsto observation nontrivial half depth ordinal,
    Eval.original_material authority origin (read n),
    Eval.relation_boundary (R := ℤ) authority origin (read n),
    Relations.boundary_in_inventory authority origin (read n) (Calculation.targetRuntime authority origin (read n)),
    Calculation.target_factorizes authority origin (read n)⟩

end WideResidualReturn.XiContact.JointGram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
