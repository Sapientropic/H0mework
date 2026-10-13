import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
local instance effectGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

theorem collapse_add (grade : Nat) {target : Unit}
    (left right : PairValue (L.Value (PairValue C.Value) grade) target) :
    CF.collapseValue grade (left + right) = CF.collapseValue grade left + CF.collapseValue grade right := by
  induction grade with
  | zero => rfl
  | succ grade previous =>
    change CF.collapseValue grade ((left.1 + right.1) + (left.2 + right.2)) =
      CF.collapseValue grade (left.1 + left.2) + CF.collapseValue grade (right.1 + right.2)
    rw [show (left.1 + right.1) + (left.2 + right.2) = (left.1 + left.2) + (right.1 + right.2) by abel]
    exact previous _ _

theorem collapse_sub (grade : Nat) {target : Unit}
    (left right : PairValue (L.Value (PairValue C.Value) grade) target) :
    CF.collapseValue grade (left - right) = CF.collapseValue grade left - CF.collapseValue grade right := by
  induction grade with
  | zero => rfl
  | succ grade previous =>
    change CF.collapseValue grade ((left.1 - right.1) + (left.2 - right.2)) =
      CF.collapseValue grade (left.1 + left.2) - CF.collapseValue grade (right.1 + right.2)
    rw [show (left.1 - right.1) + (left.2 - right.2) = (left.1 + left.2) - (right.1 + right.2) by abel]
    exact previous _ _

def deltaTotal (grade : Nat)
    (increment : Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) : BurnolL2 :=
  totalBranches (CF.collapseValue grade (increment () ()))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem directions_sub (left right : (BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) :
    directions (left - right) = directions left - directions right := by
  apply Prod.ext
  all_goals change (_ - _) + (_ - _) = (_ + _) - (_ + _); abel

theorem totalBranches_add (left right : (BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) :
    totalBranches (left + right) = totalBranches left + totalBranches right := by
  change ((left.1.1 + right.1.1) + (left.1.2 + right.1.2)) +
    ((left.2.1 + right.2.1) + (left.2.2 + right.2.2)) =
    ((left.1.1 + left.1.2) + (left.2.1 + left.2.2)) +
      ((right.1.1 + right.1.2) + (right.2.1 + right.2.2))
  abel

theorem wardSourceValue_add (left right : BurnolL2) :
    wardSourceValue observation nontrivial half (left + right) =
      wardSourceValue observation nontrivial half left + wardSourceValue observation nontrivial half right := by
  simp only [wardSourceValue, map_add, inner_add_right, add_smul, Prod.mk_add_mk]

theorem source_effect_directions (grade : Nat)
    (environment increment : Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) :
    directions (CF.collapseValue grade ((CF.codeAt (actionCode observation nontrivial half) grade).effect environment increment)) =
      wardSourceValue observation nontrivial half (deltaTotal grade increment) := by
  have actual : (CF.codeAt (actionCode observation nontrivial half) grade).effect environment increment =
      (CF.codeAt (actionCode observation nontrivial half) grade).eval (environment + increment) -
        (CF.codeAt (actionCode observation nontrivial half) grade).eval environment := by
    rw [Expr.eval_update]
    abel
  rw [actual, collapse_sub, directions_sub, CF.code_base_value, CF.code_base_value,
    action_code_directions, action_code_directions]
  simp only [Pi.add_apply, collapse_add, totalBranches_add, wardSourceValue_add, deltaTotal]
  abel

private theorem material_raw_at
    (code : Expr (PairValue (PairValue C.Value)) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
    (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
    HEq (R.actualMaterial packet.2.1.1 packet.2.2.1).raw
      (CF.codeAt (packet.2.2.2.down.symm ▸ code) packet.1) := by
  rcases packet with ⟨grade, packetData, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = C.Var at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
      ⟨C.Var, datum, inventory, pairInventory⟩
    let frame := packetData.1
    let supplied := S.actualOccurrence frame
    have actual := (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.stock_action_reader
      frame cfg supplied).symm.trans (generated frame supplied)
    exact heq_of_eq (congrArg (fun sourceRaw => sourceRaw.expression) actual)

def actualDelta (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : BurnolL2 :=
  totalBranches (CF.collapseValue packet.1 ((R.actualMaterial packet.2.1.1 packet.2.2.1).increment ()
    (packet.2.2.2.down.symm ▸ ())))

private theorem material_effect_at
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
    (generated : AI.HasActualInput (actionCode observation nontrivial half) packet.1 packet.2.2.1 packet.2.2.2.down) :
    directions (CF.collapseValue packet.1
      ((R.actualMaterial packet.2.1.1 packet.2.2.1).raw.effect
        (R.actualMaterial packet.2.1.1 packet.2.2.1).environment
        (R.actualMaterial packet.2.1.1 packet.2.2.1).increment)) =
      wardSourceValue observation nontrivial half (actualDelta packet) := by
  rcases packet with ⟨grade, packetData, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = C.Var at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
      ⟨C.Var, datum, inventory, pairInventory⟩
    let packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) :=
      ⟨grade, packetData, cfg, ⟨rfl⟩⟩
    have actual := eq_of_heq (material_raw_at (actionCode observation nontrivial half) packet generated)
    exact (congrArg (fun expression : Expr (PairValue (L.Value (PairValue C.Value) grade)) C.Var () =>
      directions (CF.collapseValue grade (expression.effect
        (R.actualMaterial packetData.1 cfg).environment (R.actualMaterial packetData.1 cfg).increment))) actual).trans
      (source_effect_directions observation nontrivial half grade
        (R.actualMaterial packetData.1 cfg).environment (R.actualMaterial packetData.1 cfg).increment)

theorem actual_material_source_effect (ordinal : Nat) : type_of%
    (material_effect_at observation nontrivial half (actionPacket observation nontrivial half depth ordinal)
      (actual_admitted_input observation nontrivial half depth ordinal)) :=
  material_effect_at observation nontrivial half _ (actual_admitted_input observation nontrivial half depth ordinal)

theorem actual_material_source_ast (ordinal : Nat) : type_of%
    (material_raw_at (actionCode observation nontrivial half)
      (actionPacket observation nontrivial half depth ordinal) (actual_admitted_input observation nontrivial half depth ordinal)) :=
  material_raw_at (actionCode observation nontrivial half) _ (actual_admitted_input observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
