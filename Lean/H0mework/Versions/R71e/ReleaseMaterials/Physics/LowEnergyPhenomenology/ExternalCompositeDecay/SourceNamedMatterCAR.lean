import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterOccupation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.NamedMatterWedgeQt
open SaturationMonoid.PhysicsCore QuantizationCheck.Fermion
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

def occupationFiber (dual : Bool) (w : Finset NamedMode) : FockFiber :=
  EuclideanSpace.single (occupation dual w) 1

private theorem create_basis (i : Mode) (s : Occupation) (hi : i ∉ s) :
    create i (occupationBasis s) = sign i s • occupationBasis (insert i s) := by
  funext t
  by_cases ht : i ∈ t
  · have he : t.erase i = s ↔ t = insert i s := by
      constructor
      · intro h; rw [← Finset.insert_erase ht, h]
      · intro h; rw [h, Finset.erase_insert hi]
    by_cases h : t = insert i s
    · subst t
      unfold create occupationBasis
      change (if i ∈ insert i s then sign i ((insert i s).erase i) *
        (if (insert i s).erase i = s then 1 else 0) else 0) = sign i s *
          (if insert i s = insert i s then 1 else 0)
      rw [if_pos (Finset.mem_insert_self i s), Finset.erase_insert hi, if_pos rfl,
        if_pos rfl]
    · have hn : t.erase i ≠ s := fun e => h (he.mp e)
      unfold create occupationBasis
      change (if i ∈ t then sign i (t.erase i) *
        (if t.erase i = s then 1 else 0) else 0) = sign i s *
          (if t = insert i s then 1 else 0)
      rw [if_pos ht, if_neg hn, if_neg h, mul_zero, mul_zero]
  · have h : t ≠ insert i s := by
      intro e; subst t; exact ht (Finset.mem_insert_self i s)
    simp only [create, if_neg ht, occupationBasis, if_neg h,
      Pi.smul_apply, smul_eq_mul, mul_zero]

theorem actual_named_create (dual : Bool) (i : NamedMode) (w : Finset NamedMode)
    (hi : i ∉ w) :
    GaussCARHistory.createFiber (rootMode dual i) (occupationFiber dual w) =
      sign (rootMode dual i) (occupation dual w) • occupationFiber dual (insert i w) := by
  classical
  apply fiberCoordinates.injective
  have hb (s : Occupation) : fiberCoordinates (EuclideanSpace.single s 1) =
      occupationBasis s := by
    funext t
    simp [fiberCoordinates, EuclideanSpace.single, occupationBasis]
  change fiberCoordinates (SourceCARBound.createOp (rootMode dual i) (occupationFiber dual w)) = _
  rw [SourceCARBound.createOp, SourceCARBound.coordinates_liftOp,
    LowEnergy.Fermion.creation_apply]
  rw [show fiberCoordinates (occupationFiber dual w) = occupationBasis (occupation dual w)
    from hb _, map_smul, show fiberCoordinates (occupationFiber dual (insert i w)) =
      occupationBasis (occupation dual (insert i w)) from hb _]
  have hm : rootMode dual i ∉ occupation dual w := by
    simpa [occupation, modeEmbedding] using hi
  rw [create_basis _ _ hm]
  have ho : occupation dual (insert i w) = insert (rootMode dual i) (occupation dual w) := by
    simp [occupation, modeEmbedding]
  rw [ho]

theorem actual_named_car (dual : Bool) (i j : NamedMode) :
    GaussCARHistory.annihilateFiber (rootMode dual i) *
        GaussCARHistory.createFiber (rootMode dual j) +
      GaussCARHistory.createFiber (rootMode dual j) *
        GaussCARHistory.annihilateFiber (rootMode dual i) = if i = j then 1 else 0 := by
  rw [GaussCARHistory.fiber_car]
  congr 1
  exact propext (modeEmbedding dual).injective.eq_iff

def orderedTriple (dual : Bool) (i j k : NamedMode) : FockFiber :=
  GaussCARHistory.createFiber (rootMode dual i)
    (GaussCARHistory.createFiber (rootMode dual j)
      (GaussCARHistory.createFiber (rootMode dual k) (occupationFiber dual ∅)))

theorem actual_ordered_triple (dual : Bool) (i j k : NamedMode)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    orderedTriple dual i j k =
      (sign (rootMode dual j) {rootMode dual k} *
        sign (rootMode dual i) {rootMode dual j, rootMode dual k}) •
          occupationFiber dual {i, j, k} := by
  classical
  rw [orderedTriple, actual_named_create dual k ∅ (by simp)]
  simp only [occupation, Finset.map_empty, sign_empty, one_smul, Finset.insert_empty]
  rw [actual_named_create dual j {k} (by simpa using hjk), map_smul,
    actual_named_create dual i {j, k} (by simp [hij, hik]), smul_smul]
  simp only [occupation, Finset.map_insert, Finset.map_singleton]
  rfl

end LowEnergy.NamedMatterWedgeQt
