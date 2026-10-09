import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterOccupation

set_option autoImplicit false
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

abbrev NamedMode := Fin 4 × Fin 3 × Fin 2

def spectator (i : Fin 2) : SU7MotherIndex :=
  if i = 0 then hyperPlusIndex else Sum.inr (Sum.inl 0)

def internalBasis (c : Fin 3) (i : Fin 2) : ExteriorBasisIndex 2 :=
  ⟨{Sum.inl c, spectator i}, by fin_cases i <;> simp [spectator, hyperPlusIndex]⟩

def rootIndex (i : NamedMode) : LowEnergy.Quantum.Index :=
  ⟨i.1, Sum.inr (Sum.inl (internalBasis i.2.1 i.2.2))⟩

def rootMode (dual : Bool) (i : NamedMode) : Mode :=
  if dual then Sum.inr (rootIndex i) else Sum.inl (rootIndex i)

theorem rootIndex_injective : Function.Injective rootIndex := by
  intro i j h
  have hs := congrArg (fun v : LowEnergy.Quantum.Index => v.1) h
  have hc : internalBasis i.2.1 i.2.2 = internalBasis j.2.1 j.2.2 := by
    simpa only [rootIndex, Sum.inr.injEq, Sum.inl.injEq] using
      congrArg (fun v : LowEnergy.Quantum.Index => v.2) h
  have hslots : i.2 = j.2 := by
    rcases i with ⟨is, ic, it⟩; rcases j with ⟨js, jc, jt⟩
    fin_cases ic <;> fin_cases it <;> fin_cases jc <;> fin_cases jt <;>
      simp_all [internalBasis, spectator, hyperPlusIndex, Finset.ext_iff]
  exact Prod.ext hs hslots

def modeEmbedding (dual : Bool) : NamedMode ↪ Mode where
  toFun := rootMode dual
  inj' := by
    intro i j h
    cases dual <;> apply rootIndex_injective <;> simpa [rootMode] using h

def occupation (dual : Bool) (w : Finset NamedMode) : Occupation :=
  w.map (modeEmbedding dual)

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
    intro hmem
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hmem
    have he : j = i := (modeEmbedding dual).injective hji
    exact hi (he ▸ hj)
  rw [create_basis _ _ hm]
  have ho : occupation dual (insert i w) = insert (rootMode dual i) (occupation dual w) := by
    change (insert i w).map (modeEmbedding dual) = _
    rw [Finset.map_insert]
    rfl
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

end LowEnergy.MixedSpectatorCandidate
