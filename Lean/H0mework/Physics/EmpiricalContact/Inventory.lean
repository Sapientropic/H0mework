import H0mework.Physics.EmpiricalContact.Action

/-! The enriched authority inventory distinguishes the generated epoch from
its preserved predecessors. No extra epoch label is inserted into physics. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch

open Stage9C.Revision
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot

deriving instance DecidableEq for MaterialProjection
deriving instance DecidableEq for SpinPair.Projection
deriving instance DecidableEq for Projection

private def materialValues : List MaterialProjection :=
  [.source, .configuration, .ledger, .residual, .inquiryCompilation, .inquiryConsumer, .spinPairAction]

private theorem material_mem (p : MaterialProjection) : p ∈ materialValues := by
  cases p <;> simp [materialValues]

instance : Fintype MaterialProjection := Fintype.ofList materialValues material_mem

private def spinPairValues : List SpinPair.Projection :=
  materialValues.map SpinPair.Projection.inherited ++
    [.weakActual, .weakCompilation, .weakConsumer, .quantumField, .quantumCompilation, .quantumConsumer]

private theorem spinPair_mem (p : SpinPair.Projection) : p ∈ spinPairValues := by
  cases p with
  | inherited coordinate =>
      exact List.mem_append_left _ (List.mem_map.mpr ⟨coordinate, material_mem coordinate, rfl⟩)
  | weakActual => simp [spinPairValues]
  | weakCompilation => simp [spinPairValues]
  | weakConsumer => simp [spinPairValues]
  | quantumField => simp [spinPairValues]
  | quantumCompilation => simp [spinPairValues]
  | quantumConsumer => simp [spinPairValues]

instance : Fintype SpinPair.Projection := Fintype.ofList spinPairValues spinPair_mem

private def empiricalValues : List Projection := spinPairValues.map Projection.inherited ++
  [.field, .ledger, .residual, .contact, .auditDemand, .compilation, .consumer]

private theorem empirical_mem (p : Projection) : p ∈ empiricalValues := by
  cases p with
  | inherited coordinate =>
      exact List.mem_append_left _ (List.mem_map.mpr ⟨coordinate, spinPair_mem coordinate, rfl⟩)
  | field => simp [empiricalValues]
  | ledger => simp [empiricalValues]
  | residual => simp [empiricalValues]
  | contact => simp [empiricalValues]
  | auditDemand => simp [empiricalValues]
  | compilation => simp [empiricalValues]
  | consumer => simp [empiricalValues]

instance : Fintype Projection := Fintype.ofList empiricalValues empirical_mem

theorem material_inventory_card : Nat.card MaterialProjection = 7 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem spinPair_inventory_card : Nat.card SpinPair.Projection = 13 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem empirical_inventory_card : Nat.card Projection = 20 := by
  rw [Nat.card_eq_fintype_card]
  decide

private instance : Infinite RootProjectionCoordinate :=
  Infinite.of_injective (fun time : ℝ => RootProjectionCoordinate.matter time 0)
    (by intro left right equality; cases equality; rfl)

theorem original_inventory_card : Nat.card RootProjectionCoordinate = 0 :=
  Nat.card_eq_zero_of_infinite

end SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch
