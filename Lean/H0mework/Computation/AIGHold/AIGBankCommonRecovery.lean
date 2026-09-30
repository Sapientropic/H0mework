import H0mework.Computation.AIGHold.AIGBankRecovery

/-! # One source-clocked deadline restores every actual output capacitor simultaneously -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance Set
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α : Type} [DecidableEq α] [Hashable α] {width : Nat}

noncomputable section

theorem aigBankRecoveryVoltageAt_correct_after
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
    (index : Fin width) (actualInitial : SIVolt) (offset time : ℝ)
    (late : aigBankRecoveryReady technology entry offset +
      ((aigBankCell technology entry index).arbitraryRecoveryTime actualInitial).value ≤ time) :
    BitBand (aigBankCell technology entry index)
      (AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩)
      (aigBankRecoveryVoltageAt technology entry memory assignment index actualInitial offset time) := by
  have controls := aigBankRecoveryControl_continuous technology entry memory assignment index offset
  have generated := (aigBankCell technology entry index).driven_nand_from_arbitrary_initial
    (!(AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩))
    (!(AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩))
    (aigBankRecoveryControl technology entry memory assignment index offset)
    (aigBankRecoveryControl technology entry memory assignment index offset) actualInitial controls controls
    (aigBankRecoveryReady technology entry offset) time (le_max_left _ _) late
    (fun t ht => ⟨aigBankRecoveryControl_band technology entry memory assignment index offset t ht.1,
      aigBankRecoveryControl_band technology entry memory assignment index offset t ht.1⟩)
  simpa only [Bool.and_self, Bool.not_not, aigBankRecoveryVoltageAt] using generated

def aigBankMaxRecoveryDuration (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (actualInitial : Fin width → SIVolt) : ℝ :=
  (Finset.univ : Finset (Option (Fin width))).sup' ⟨none, Finset.mem_univ _⟩
    (fun index => match index with
      | none => 0
      | some i => ((aigBankCell technology entry i).arbitraryRecoveryTime (actualInitial i)).value)

theorem aigBankMaxRecoveryDuration_nonneg (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (actualInitial : Fin width → SIVolt) : 0 ≤ aigBankMaxRecoveryDuration technology entry actualInitial :=
  Finset.le_sup' (fun index : Option (Fin width) => match index with
    | none => 0
    | some i => ((aigBankCell technology entry i).arbitraryRecoveryTime (actualInitial i)).value) (Finset.mem_univ none)

theorem aigBankMaxRecoveryDuration_covers (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (actualInitial : Fin width → SIVolt) (index : Fin width) :
    ((aigBankCell technology entry index).arbitraryRecoveryTime (actualInitial index)).value ≤
      aigBankMaxRecoveryDuration technology entry actualInitial :=
  Finset.le_sup' (fun selected : Option (Fin width) => match selected with
    | none => 0
    | some i => ((aigBankCell technology entry i).arbitraryRecoveryTime (actualInitial i)).value) (Finset.mem_univ (some index))

def aigBankCommonRecoveryTime (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (actualInitial : Fin width → SIVolt) (offset : ℝ)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) : SISecond :=
  finiteSamplingClockSampleTime clock code
    ⟨aigBankRecoveryReady technology entry offset + aigBankMaxRecoveryDuration technology entry actualInitial⟩

theorem aigBankCommonRecoveryTime_nonneg (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (actualInitial : Fin width → SIVolt) (offset : ℝ)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    0 ≤ (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value :=
  (add_nonneg (le_max_left _ _) (aigBankMaxRecoveryDuration_nonneg technology entry actualInitial)).trans
    (finiteSamplingClock_requested_le_sampleTime clock code _)

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (actualInitial : Fin width → SIVolt) (offset : ℝ)
  (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)

theorem aigBankCommonRecoveryTime_band (index : Fin width) :
    BitBand (aigBankCell technology entry index)
      (AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩)
      (aigBankRecoveryVoltageAt technology entry memory assignment index (actualInitial index) offset
        (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value) := by
  apply aigBankRecoveryVoltageAt_correct_after
  calc
    _ ≤ aigBankRecoveryReady technology entry offset + aigBankMaxRecoveryDuration technology entry actualInitial :=
      add_le_add le_rfl (aigBankMaxRecoveryDuration_covers technology entry actualInitial index)
    _ ≤ _ := finiteSamplingClock_requested_le_sampleTime clock code
      (⟨aigBankRecoveryReady technology entry offset + aigBankMaxRecoveryDuration technology entry actualInitial⟩ : SISecond)

theorem aigBankCommonRecoveryTime_in_rail (index : Fin width) :
    InRail (aigBankCell technology entry index)
      (aigBankRecoveryVoltageAt technology entry memory assignment index (actualInitial index) offset
        (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value) := by
  have band := aigBankCommonRecoveryTime_band technology entry memory assignment actualInitial offset clock code index
  cases bit : AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩ <;> rw [bit] at band
  · exact ⟨band.1, by linarith [band.2, (aigBankCell technology entry index).supply_pos]⟩
  · exact ⟨by linarith [band.1, (aigBankCell technology entry index).supply_pos], band.2⟩

def aigBankCommonRecoveryRead : Vector (Option Bool) width :=
  let sample := aigBankCommonRecoveryTime technology entry actualInitial offset clock code
  Vector.ofFn fun index => railRead? (aigBankCell technology entry index)
    (aigBankRecoveryVoltageAt technology entry memory assignment index (actualInitial index) offset sample.value)

theorem aigBankCommonRecoveryRead_eq_source_refs :
    aigBankCommonRecoveryRead technology entry memory assignment actualInitial offset clock code =
      Vector.ofFn (fun index : Fin width => some (AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩)) := by
  apply Vector.ext
  intro index bound
  simp only [aigBankCommonRecoveryRead, Vector.getElem_ofFn]
  have band := aigBankCommonRecoveryTime_band technology entry memory assignment actualInitial offset clock code ⟨index, bound⟩
  cases bit : AIG.denote assignment ⟨entry.aig, entry.vec.get index bound⟩ <;> rw [bit] at band
  · exact railRead?_of_low _ _ band
  · exact railRead?_of_high _ _ band

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
