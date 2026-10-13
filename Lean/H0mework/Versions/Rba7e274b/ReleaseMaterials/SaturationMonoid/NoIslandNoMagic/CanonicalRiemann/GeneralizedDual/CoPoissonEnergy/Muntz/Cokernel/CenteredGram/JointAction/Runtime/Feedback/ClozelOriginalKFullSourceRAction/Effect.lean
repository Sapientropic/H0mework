import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
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
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

/-- This increment belongs to the new R occurrence's actual environment. -/
def actualDelta (ordinal : Nat) : BurnolPhysicalState.BurnolL2:=
  originalField (incrementEnvironment (actionPacket observation nontrivial half depth ordinal) () ())
def actualEffect (ordinal : Nat) : Prior.Branches:=
  variableAction observation nontrivial half
    (incrementEnvironment (actionPacket observation nontrivial half depth ordinal) () ())

theorem actual_material_source_effect (ordinal : Nat) :
    CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
      ((material observation nontrivial half depth ordinal).raw.effect
        (material observation nontrivial half depth ordinal).environment
        (material observation nontrivial half depth ordinal).increment)=
      actualEffect observation nontrivial half depth ordinal := by
  rw [material_effect_at (sourceCode observation nontrivial half)
    (actionPacket observation nontrivial half depth ordinal) (actual_admitted_input observation nontrivial half depth ordinal),
    source_code_effect]
  rfl

theorem actual_R_effect (ordinal : Nat) :
    (actualEffect observation nontrivial half depth ordinal).1.1=
      Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal) ∧
    (actualEffect observation nontrivial half depth ordinal).1.2=
      BurnolPhysicalState.FiniteMobiusResolventFlux.D
        (Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)) :=⟨rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
