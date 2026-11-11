import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRFourFaceSourceAction.Effect
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRFourFaceSourceAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance receivedStockSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

/-- The four new roles are read from actual material, with the inherited four-field cost retained separately. -/
def receivedOwnStock : Branches := CF.collapseValue (grade+1)
 ((stockMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).raw.effect
  (stockMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).environment
  (stockMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).increment) -
 inheritedSourceIncrement observation nontrivial half depth ordinal h H N producer grade data sourceCfg language (language.symm ▸ ())

theorem received_material_own_stock
 (effect : type_of% (actual_material_stock_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) :
 receivedOwnStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language =
 ownFourFaceSource observation nontrivial half depth ordinal h H N := by
 unfold receivedOwnStock
 rw [effect]
 abel

theorem received_four_physical
 (effect : type_of% (actual_material_stock_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) :
 let stock := receivedOwnStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language
 stock.1.1 ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
 stock.1.2 ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
 stock.2.1 ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
 stock.2.2 ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
 dsimp only
 rw [received_material_own_stock _ _ _ _ _ _ _ _ _ _ _ _ _ effect]
 exact own_four_faces_physical _ _ _ _ _ _ _ _

def receivedPhysicalFaces
 (effect : type_of% (actual_material_stock_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) :
 (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) × (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) :=
 let stock := receivedOwnStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language
 let paid := received_four_physical observation nontrivial half depth ordinal h H N producer grade data sourceCfg language effect
 ((⟨stock.1.1,paid.1⟩,⟨stock.1.2,paid.2.1⟩),(⟨stock.2.1,paid.2.2.1⟩,⟨stock.2.2,paid.2.2.2⟩))

/-- The original B source programme prices the four received legs, keeping velocity/contact and both mean windows. -/
theorem received_four_cotest_B_price
 (effect : type_of% (actual_material_stock_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) (shift : ℝ) :
 let stock := receivedPhysicalFaces observation nontrivial half depth ordinal h H N producer grade data sourceCfg language effect
 let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 ((inner ℂ stock.1.1 (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero shift),
   inner ℂ stock.1.2 (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero shift)),
  (inner ℂ stock.2.1 (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero shift),
   inner ℂ stock.2.2 (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero shift))) =
 boundaryFourRead observation nontrivial half stock shift := by
 let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let stock := receivedPhysicalFaces observation nontrivial half depth ordinal h H N producer grade data sourceCfg language effect
 have first := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.1.1 shift
 have second := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.1.2 shift
 have third := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.2.1 shift
 have fourth := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.2.2 shift
 exact congrArg₂ (fun x y => (x,y)) (congrArg₂ (fun x y => (x,y)) first second) (congrArg₂ (fun x y => (x,y)) third fourth)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
