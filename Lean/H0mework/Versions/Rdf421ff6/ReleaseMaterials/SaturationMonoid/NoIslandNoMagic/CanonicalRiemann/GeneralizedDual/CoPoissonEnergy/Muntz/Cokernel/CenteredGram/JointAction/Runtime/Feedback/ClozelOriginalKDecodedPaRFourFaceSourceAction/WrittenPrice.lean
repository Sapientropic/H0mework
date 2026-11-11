import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRFourFaceSourceAction.Received
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance writtenStockSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def bornWrittenStock : Branches := CF.collapseValue grade
 ((stockBorn observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).activeEnvironment () (language.symm ▸ ()))
def inheritedWrittenStock : Branches := CF.collapseValue grade
 (updatedSourceTotal observation nontrivial half depth ordinal h H N (fourFaceFactory producer) grade data sourceCfg language)

def projectedFaces (stock : Branches) := ((P stock.1.1,P stock.1.2),(P stock.2.1,P stock.2.2))

private def vectorFourCotest (B : BurnolPaAmbientCarrier)
 (stock : (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) × (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier)) :=
 ((inner ℂ stock.1.1 B,inner ℂ stock.1.2 B),(inner ℂ stock.2.1 B,inner ℂ stock.2.2 B))

private theorem projected_cotest_full_add (B : BurnolPaAmbientCarrier) (inherited : Branches)
 (own : (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) × (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier)) :
 vectorFourCotest B (projectedFaces (inherited+(((own.1.1 : BurnolL2),(own.1.2 : BurnolL2)),((own.2.1 : BurnolL2),(own.2.2 : BurnolL2))))) =
 vectorFourCotest B (projectedFaces inherited)+vectorFourCotest B own := by
 have p1 : P (own.1.1 : BurnolL2)=own.1.1 := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self own.1.1
 have p2 : P (own.1.2 : BurnolL2)=own.1.2 := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self own.1.2
 have p3 : P (own.2.1 : BurnolL2)=own.2.1 := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self own.2.1
 have p4 : P (own.2.2 : BurnolL2)=own.2.2 := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self own.2.2
 unfold vectorFourCotest projectedFaces
 simp only [Prod.fst_add,Prod.snd_add,map_add,p1,p2,p3,p4,inner_add_left]
 rfl

def boundaryFourCotest (stock : (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) × (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier)) (shift : ℝ) :=
 let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let B := burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero shift
 ((inner ℂ stock.1.1 B,inner ℂ stock.1.2 B),(inner ℂ stock.2.1 B,inner ℂ stock.2.2 B))

theorem full_four_cotest_source_read (stock : (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) × (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier)) (shift : ℝ) :
 boundaryFourCotest observation nontrivial half stock shift = boundaryFourRead observation nontrivial half stock shift := by
 let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have first := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.1.1 shift
 have second := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.1.2 shift
 have third := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.2.1 shift
 have fourth := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.2.2 shift
 exact congrArg₂ (fun x y => (x,y)) (congrArg₂ (fun x y => (x,y)) first second) (congrArg₂ (fun x y => (x,y)) third fourth)

theorem received_born_current_source
 (write : type_of% (actual_born_four_stock_increment observation nontrivial half depth ordinal h H N
  (fourFaceFactory producer) grade data sourceCfg language (language.symm ▸ ())))
 (effect : type_of% (actual_material_stock_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) :
 bornWrittenStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language =
 inheritedWrittenStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language +
 receivedOwnStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language := by
 rw [received_material_own_stock _ _ _ _ _ _ _ _ _ _ _ _ _ effect]
 change bornWrittenStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language-
  inheritedWrittenStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language=
  ownFourFaceSource observation nontrivial half depth ordinal h H N at write
 linear_combination (norm:=module) write

/-- The actual new current is priced with its full inherited four-cotest cost; own physical qualification never transfers to that inherited quantity. -/
theorem received_born_full_B_price
 (write : type_of% (actual_born_four_stock_increment observation nontrivial half depth ordinal h H N
  (fourFaceFactory producer) grade data sourceCfg language (language.symm ▸ ())))
 (effect : type_of% (actual_material_stock_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) (shift : ℝ) :
 boundaryFourCotest observation nontrivial half
  (projectedFaces (bornWrittenStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) shift =
 boundaryFourRead observation nontrivial half
  (projectedFaces (inheritedWrittenStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) shift +
 boundaryFourRead observation nontrivial half
  (receivedPhysicalFaces observation nontrivial half depth ordinal h H N producer grade data sourceCfg language effect) shift := by
 rw [received_born_current_source _ _ _ _ _ _ _ _ _ _ _ _ _ write effect]
 let own := receivedPhysicalFaces observation nontrivial half depth ordinal h H N producer grade data sourceCfg language effect
 let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let B := burnolZeroPairedFixedAnnulusBoundary c (show riemannZeta c.value=0 from observation.mathlibZero) shift
 have split := projected_cotest_full_add B
  (inheritedWrittenStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language) own
 change boundaryFourCotest observation nontrivial half
  (projectedFaces (inheritedWrittenStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language+
    receivedOwnStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) shift =
  boundaryFourCotest observation nontrivial half
   (projectedFaces (inheritedWrittenStock observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) shift+
  boundaryFourCotest observation nontrivial half own shift at split
 exact split.trans (congrArg₂ (fun x y => x+y)
  (full_four_cotest_source_read observation nontrivial half _ shift)
  (full_four_cotest_source_read observation nontrivial half _ shift))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
