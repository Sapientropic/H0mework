import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNativeSourceAction.Native
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace A
export OriginalKDefectAction.A (Programme)
end A
namespace Projection
export OriginalKDefectAction.Projection (code_effect_base)
end Projection
local instance effectGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

def oldEnvironment:=OriginalKDefectAction.oldEnvironment
def incrementEnvironment:=OriginalKDefectAction.incrementEnvironment

private theorem material_effect_at (code : Expr (PairValue (PairValue C.Value)) C.Var ())
    (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
    (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
    CF.collapseValue packet.1 ((R.actualMaterial packet.2.1.1 packet.2.2.1).raw.effect
      (R.actualMaterial packet.2.1.1 packet.2.2.1).environment
      (R.actualMaterial packet.2.1.1 packet.2.2.1).increment)=
      code.effect (oldEnvironment packet) (incrementEnvironment packet) := by
  rcases packet with ⟨grade,packetData,programme,⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar=C.Var at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()) :=
      ⟨C.Var,datum,inventory,pairInventory⟩
    let packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()) :=⟨grade,packetData,cfg,⟨rfl⟩⟩
    have raw:=eq_of_heq (Paid.material_raw_at code packet generated)
    exact (congrArg (fun expression : Expr (PairValue (L.Value (PairValue C.Value) grade)) C.Var ()=>
      CF.collapseValue grade (expression.effect (R.actualMaterial packetData.1 cfg).environment
        (R.actualMaterial packetData.1 cfg).increment)) raw).trans (Projection.code_effect_base code grade _ _)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h : ℝ)

/-- This increment belongs to the new corrected-source occurrence's actual environment. -/
def actualDelta : BurnolPhysicalState.BurnolL2:=
  Prior.originalField (incrementEnvironment (actionPacket observation nontrivial half depth ordinal h) () ())
def actualEffect : Branches:=
  orbitAction observation h
    (incrementEnvironment (actionPacket observation nontrivial half depth ordinal h) () ())

theorem actual_material_source_effect :
    CF.collapseValue (actionPacket observation nontrivial half depth ordinal h).1
      ((material observation nontrivial half depth ordinal h).raw.effect
        (material observation nontrivial half depth ordinal h).environment
        (material observation nontrivial half depth ordinal h).increment)=
      actualEffect observation nontrivial half depth ordinal h := by
  rw [material_effect_at (sourceCode observation nontrivial half depth ordinal h)
    (actionPacket observation nontrivial half depth ordinal h) (actual_admitted_input observation nontrivial half depth ordinal h),
    source_code_effect]
  rfl

theorem actual_orbit_effect :
 (actualEffect observation nontrivial half depth ordinal h).1.1 =
  (pairedAction h - ContinuousLinearMap.id ℂ BurnolPhysicalState.BurnolL2)
   (Flux.sourceA observation • actualDelta observation nontrivial half depth ordinal h) := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
