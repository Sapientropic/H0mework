import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.FiniteCAR

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open scoped BigOperators InnerProductSpace Matrix

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : CPS1SameEventFunction.Classical.Raw}
  {before : CPS1SameEventFunction.Classical.Current cursor priorRaw}
  {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
  {raw : Raw} {source : Common before step raw}

/-- Modes occupied only after the same source/current transition. -/
def canonicalAdded (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : List (AddressedBasisIndex current) :=
  (after.val \ previous.val).toList

/-- Modes occupied only before the same source/current transition. -/
def canonicalRemoved (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : List (AddressedBasisIndex current) :=
  (previous.val \ after.val).toList

/-- The canonical direction is `(J \ I) → (I \ J)`: new modes point to removed modes. -/
def canonicalPairing (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    List (AddressedBasisIndex current × AddressedBasisIndex current) :=
  (canonicalAdded current previous after).zip (canonicalRemoved current previous after)

private theorem canonical_sdiff_card (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    (after.val \ previous.val).card = (previous.val \ after.val).card := by
  have previousCard : previous.val.card = electronCount source.nodes :=
    Set.powersetCard.card_eq previous
  have afterCard : after.val.card = electronCount source.nodes :=
    Set.powersetCard.card_eq after
  rw [Finset.card_sdiff,Finset.card_sdiff,previousCard,afterCard,Finset.inter_comm]

theorem canonical_pairing_length (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    (canonicalPairing current previous after).length =
      (canonicalAdded current previous after).length ∧
      (canonicalPairing current previous after).length =
        (canonicalRemoved current previous after).length := by
  have equal : (canonicalAdded current previous after).length =
      (canonicalRemoved current previous after).length := by
    simp only [canonicalAdded,canonicalRemoved,Finset.length_toList]
    exact canonical_sdiff_card current previous after
  simp only [canonicalPairing,List.length_zip]
  exact ⟨Nat.min_eq_left (le_of_eq equal),Nat.min_eq_right (le_of_eq equal.symm)⟩

/-- Occupation shared by the two configurations, as a pointwise idempotent projector. -/
def commonOccupation (current : NativeCurrent source)
    (previous after : AtomConfiguration current) (mode : AddressedBasisIndex current) : ℂ :=
  if mode ∈ previous.val ∩ after.val then 1 else 0

theorem common_occupation_projector (current : NativeCurrent source)
    (previous after : AtomConfiguration current) (mode : AddressedBasisIndex current) :
    commonOccupation current previous after mode * commonOccupation current previous after mode =
      commonOccupation current previous after mode := by
  unfold commonOccupation
  split <;> norm_num

theorem common_occupation_mem (current : NativeCurrent source)
    (previous after : AtomConfiguration current) (mode : AddressedBasisIndex current) :
    commonOccupation current previous after mode = 1 ↔
      mode ∈ previous.val ∧ mode ∈ after.val := by
  unfold commonOccupation
  by_cases held : mode ∈ previous.val ∩ after.val
  · constructor
    · intro _
      exact Finset.mem_inter.mp held
    · intro _
      simp [held]
  · constructor
    · simp [held]
    · intro both
      exact (held (Finset.mem_inter.mpr both)).elim

/-- Only the symmetric-difference modes enter the reduced CAR word. -/
def canonicalCARWord (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : List (SourceCARSymbol current) :=
  (canonicalPairing current previous after).flatMap (fun pair =>
    [SourceCARSymbol.creating pair.1, SourceCARSymbol.annihilating pair.2])

def canonicalCARPhase (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : ℂ :=
  if Even ((canonicalAdded current previous after).length *
      (canonicalRemoved current previous after).length) then 1 else -1

theorem canonical_car_phase_pm_one (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    canonicalCARPhase current previous after = 1 ∨
      canonicalCARPhase current previous after = -1 := by
  unfold canonicalCARPhase
  split <;> simp

/-- Source charged word generated from the canonical pairing; no caller-supplied history. -/
def canonicalChargedWord (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : ChargedSourceWord cursor :=
  (canonicalPairing current previous after).map
    (fun pair => .electron (sectorOrigin current pair.2.1) (sectorOrigin current pair.1.1))

def canonicalChargeDelta (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : Charges cursor :=
  ((canonicalPairing current previous after).map (fun pair =>
    electronRequestDelta (.electron (sectorOrigin current pair.2.1)
      (sectorOrigin current pair.1.1)))).sum

theorem canonical_pairing_charge (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    ((canonicalPairing current previous after).map (fun pair =>
      electronRequestDelta (.electron (sectorOrigin current pair.2.1)
        (sectorOrigin current pair.1.1)))).sum =
      canonicalChargeDelta current previous after := by
  rfl

theorem canonical_word_charge (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    ((canonicalCARWord current previous after).map SourceCARSymbol.charge).sum =
      canonicalChargeDelta current previous after := by
  classical
  change ((canonicalCARWord current previous after).map SourceCARSymbol.charge).sum =
    ((canonicalPairing current previous after).map (fun pair =>
      electronRequestDelta (.electron (sectorOrigin current pair.2.1)
        (sectorOrigin current pair.1.1)))).sum
  have pairCharge (pair : AddressedBasisIndex current × AddressedBasisIndex current) :
      (SourceCARSymbol.creating pair.1).charge +
          (SourceCARSymbol.annihilating pair.2).charge =
        electronRequestDelta (.electron (sectorOrigin current pair.2.1)
          (sectorOrigin current pair.1.1)) := by
    simp only [SourceCARSymbol.charge,electronRequestDelta]
    abel
  have wordCharge : ∀ (pairs : List (AddressedBasisIndex current × AddressedBasisIndex current)),
      ((pairs.flatMap (fun pair =>
        [SourceCARSymbol.creating pair.1,SourceCARSymbol.annihilating pair.2])).map
          SourceCARSymbol.charge).sum =
        (pairs.map (fun pair =>
          electronRequestDelta (.electron (sectorOrigin current pair.2.1)
            (sectorOrigin current pair.1.1)))).sum := by
    intro pairs
    induction pairs with
    | nil => simp
    | cons pair rest ih =>
        simp only [List.flatMap_cons,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
          List.map_nil,List.sum_nil,add_zero]
        rw [pairCharge,ih]
  exact wordCharge (canonicalPairing current previous after)

theorem canonical_word_total_charge (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    totalCharge (canonicalChargeDelta current previous after) = 0 := by
  classical
  unfold canonicalChargeDelta
  have pairTotal (pair : AddressedBasisIndex current × AddressedBasisIndex current) :
      totalCharge (electronRequestDelta (.electron (sectorOrigin current pair.2.1)
        (sectorOrigin current pair.1.1))) = 0 := by
    unfold electronRequestDelta
    rw [map_sub]
    simp only [totalCharge,chargeWeight,Finsupp.linearCombination_single,one_smul,sub_self]
  have total : ∀ (pairs : List (AddressedBasisIndex current × AddressedBasisIndex current)),
      totalCharge ((pairs.map (fun pair =>
        electronRequestDelta (.electron (sectorOrigin current pair.2.1)
          (sectorOrigin current pair.1.1)))).sum) = 0 := by
    intro pairs
    induction pairs with
    | nil => simp
    | cons pair rest ih =>
        simp only [List.map_cons,List.sum_cons,map_add]
        rw [pairTotal,ih,zero_add]
  exact total (canonicalPairing current previous after)

theorem canonical_word_atom_charge (current : NativeCurrent source)
    (previous after : AtomConfiguration current) (observed : AtomSector source)
    (state : SourceFermion) :
    atomNumber current observed ((evaluateCARWord (canonicalCARWord current previous after)) state) -
      (evaluateCARWord (canonicalCARWord current previous after))
        (atomNumber current observed state) =
      (-(canonicalChargeDelta current previous after (sectorOrigin current observed)) : ℂ) •
        (evaluateCARWord (canonicalCARWord current previous after)) state := by
  rw [source_car_word_atom_charge]
  rw [canonical_word_charge]

theorem canonical_word_pauli (current : NativeCurrent source)
    (_previous _after : AtomConfiguration current) (mode : AddressedBasisIndex current)
    (state : SourceFermion) :
    physicalCreation (addressedBasis current mode)
        (physicalCreation (addressedBasis current mode) state) = 0 ∧
      physicalAnnihilation (addressedBasis current mode)
        (physicalAnnihilation (addressedBasis current mode) state) = 0 :=
  ⟨physical_creation_pauli _ _,physical_annihilation_pauli _ _⟩

theorem canonical_pairing_ne (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    (canonicalAdded current previous after).length =
      (canonicalRemoved current previous after).length := by
  exact (canonical_pairing_length current previous after).1.symm.trans
    (canonical_pairing_length current previous after).2

def canonicalStock (source : Common before step raw) (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : SourceChargedRun source current :=
  runChargedWord source current (canonicalChargedWord current previous after)

def canonicalStockFold (source : Common before step raw) (current : NativeCurrent source) :
    List (SourceChargedRun source current) :=
  ((Finset.univ : Finset (AtomConfiguration current × AtomConfiguration current)).toList).map
    (fun pair => canonicalStock source current pair.1 pair.2)

theorem canonical_stock_whole (source : Common before step raw)
    (current : NativeCurrent source) (previous after : AtomConfiguration current) :
    (canonicalStock source current previous after).state.whole.1 = current ∧
      (canonicalStock source current previous after).state.whole.1.occupied = current.occupied ∧
      (canonicalStock source current previous after).state.whole.1.remaining = current.remaining := by
  have whole := charged_run_whole source current
    (canonicalChargedWord current previous after)
  exact ⟨whole.1,whole.2.2.1,whole.2.2.2⟩

theorem canonical_stock_fold_whole (source : Common before step raw)
    (current : NativeCurrent source) (run : SourceChargedRun source current)
    (held : run ∈ canonicalStockFold source current) :
    run.state.whole.1 = current ∧ run.state.whole.1.occupied = current.occupied ∧
      run.state.whole.1.remaining = current.remaining := by
  classical
  unfold canonicalStockFold at held
  obtain ⟨pair,_,same⟩ := List.mem_map.mp held
  subst run
  exact canonical_stock_whole source current pair.1 pair.2

end
end CPS1MaterialIncidence
