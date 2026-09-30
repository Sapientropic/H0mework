import H0mework.Computation.ADCGates.RawAdmissionGate
import H0mework.Computation.ADCGates.RawPacketAdmission
import H0mework.Computation.AIGExecution.AIGExecutionCorrectnessSource

/-!
# Correctness of raw ADC admission gates

The packet and calibration restrictions retain the same runtime assignment but
have separate fixed AIGs, so the receiver can preserve its parsed and calibrated
states. The combined graph decides the full raw admission proposition without a
validity or desired-result premise.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat
open Std.Tactic.BVDecide

private theorem finiteADCRawAdmissionAssignment_eval_packetTick
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) :
    BVExpr.eval (finiteADCRawAdmissionAssignment input) (.var 0 : BVExpr counterBits) =
      BitVec.ofFin input.packetTick := by
  rw [BVExpr.eval_var]
  unfold finiteADCRawAdmissionAssignment BVExpr.Assignment.get
  change
    (BitVec.truncate counterBits
      ((Lean.RArray.ofFn (finiteADCRawAdmissionPackedVariable input)
        finiteADCRawAdmissionVariableCount_pos).get (0 : Fin 62).val).bv) = _
  rw [Lean.RArray.get_ofFn]
  change (BitVec.ofFin input.packetTick).truncate counterBits = _
  simp

private theorem finiteADCRawAdmissionAssignment_eval_lastTickBound
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) :
    BVExpr.eval (finiteADCRawAdmissionAssignment input) (.var 1 : BVExpr counterBits) =
      BitVec.ofFin input.lastTickBound := by
  rw [BVExpr.eval_var]
  unfold finiteADCRawAdmissionAssignment BVExpr.Assignment.get
  change
    (BitVec.truncate counterBits
      ((Lean.RArray.ofFn (finiteADCRawAdmissionPackedVariable input)
        finiteADCRawAdmissionVariableCount_pos).get (1 : Fin 62).val).bv) = _
  rw [Lean.RArray.get_ofFn]
  change (BitVec.ofFin input.lastTickBound).truncate counterBits = _
  simp

private theorem finiteADCRawAdmissionAssignment_eval_word
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits)
    (address : FiniteADCRawWordAddress) :
    BVExpr.eval (finiteADCRawAdmissionAssignment input)
        (.var (finiteADCRawAdmissionWordVariable address) : BVExpr (adcWordBits code)) =
      BitVec.ofFin (input.rawWordAt address.1.1 address.1.2 address.2) := by
  rw [BVExpr.eval_var]
  unfold finiteADCRawAdmissionAssignment BVExpr.Assignment.get
  let index : Fin 62 := ⟨finiteADCRawAdmissionWordVariable address, by
    have bound := (finiteADCRawWordAddressEquivFin address).isLt
    unfold finiteADCRawAdmissionWordVariable
    omega⟩
  change
    (BitVec.truncate (adcWordBits code)
      ((Lean.RArray.ofFn (finiteADCRawAdmissionPackedVariable input)
        finiteADCRawAdmissionVariableCount_pos).get index.val).bv) = _
  rw [Lean.RArray.get_ofFn]
  have notZero : index.val ≠ 0 := by
    change 2 + (finiteADCRawWordAddressEquivFin address).val ≠ 0
    omega
  have notOne : index.val ≠ 1 := by
    change 2 + (finiteADCRawWordAddressEquivFin address).val ≠ 1
    omega
  rw [finiteADCRawAdmissionPackedVariable, dif_neg notZero, dif_neg notOne]
  change (BitVec.ofFin (input.rawWordAt _ _ _)).truncate (adcWordBits code) = _
  rw [show finiteADCRawWordAddressEquivFin.symm ⟨index.val - 2, by omega⟩ = address by
    apply finiteADCRawWordAddressEquivFin.injective
    simp [index, finiteADCRawAdmissionWordVariable]]
  simp

/-- The shared receiver dataflow consumes the same original raw-word assignment. -/
theorem finiteADCRawAdmissionAssignment_word_value
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits)
    (address : FiniteADCRawWordAddress) :
    BVExpr.eval (finiteADCRawAdmissionAssignment input)
        (.var (finiteADCRawAdmissionWordVariable address) : BVExpr (adcWordBits code)) =
      BitVec.ofFin (input.rawWordAt address.1.1 address.1.2 address.2) :=
  finiteADCRawAdmissionAssignment_eval_word input address

private theorem finiteADCRawNotUlt_eq_decide_le
    {width : Nat} (maximum raw : BitVec width) :
    (!maximum.ult raw) = decide (raw.toNat ≤ maximum.toNat) := by
  rw [BitVec.ult_eq_decide]
  by_cases less : maximum.toNat < raw.toNat
  · simp [less]
  · have le : raw.toNat ≤ maximum.toNat := by omega
    simp [less, le]

private theorem finiteADCRawAdmissionHeaderExpr_exact
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) :
    BVLogicalExpr.eval (finiteADCRawAdmissionAssignment input)
        (finiteADCRawAdmissionHeaderExpr counterBits) =
      decide (input.packetTick.val ≤ input.lastTickBound.val) := by
  rw [finiteADCRawAdmissionHeaderExpr, BVLogicalExpr.eval_not,
    BVLogicalExpr.eval_literal, BVPred.eval_bin, BVBinPred.eval_ult,
    finiteADCRawAdmissionAssignment_eval_lastTickBound,
    finiteADCRawAdmissionAssignment_eval_packetTick, BitVec.ult_eq_decide_lt]
  by_cases le : input.packetTick.val ≤ input.lastTickBound.val
  · have notLess : ¬ input.lastTickBound < input.packetTick := by simpa using le
    simp [le, notLess]
  · have less : input.lastTickBound < input.packetTick := by
      simpa using (Nat.lt_of_not_ge le)
    simp [le, less]

private theorem finiteADCRawAdmissionWordExpr_exact
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits)
    (address : FiniteADCRawWordAddress) :
    BVLogicalExpr.eval (finiteADCRawAdmissionAssignment input)
        (finiteADCRawAdmissionWordExpr code address) =
      decide (validADCWord code (input.rawWordAt address.1.1 address.1.2 address.2)) := by
  rw [finiteADCRawAdmissionWordExpr, BVLogicalExpr.eval_not,
    BVLogicalExpr.eval_literal, BVPred.eval_bin, BVBinPred.eval_ult,
    BVExpr.eval_const, finiteADCRawAdmissionAssignment_eval_word,
    finiteADCRawNotUlt_eq_decide_le, BitVec.toNat_ofFin, BitVec.toNat_ofFin]
  cases code <;>
    norm_num [validADCWord, finiteADCValidRawMaximum,
      finiteADCGridDenominator, adcWordBits]

private theorem finiteADCRawAdmissionSpanExpr_exact
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits)
    (address : FiniteADCRawSpanAddress) :
    BVLogicalExpr.eval (finiteADCRawAdmissionAssignment input)
        (finiteADCRawAdmissionSpanExpr code address) =
      decide ((input.rawWordAt .zeroReference address.1 address.2).val <
        (input.rawWordAt .spanReference address.1 address.2).val) := by
  rw [finiteADCRawAdmissionSpanExpr, BVLogicalExpr.eval_literal,
    BVPred.eval_bin, BVBinPred.eval_ult,
    finiteADCRawAdmissionAssignment_eval_word,
    finiteADCRawAdmissionAssignment_eval_word,
    BitVec.ult_eq_decide, BitVec.toNat_ofFin, BitVec.toNat_ofFin]

private theorem finiteADCRawAdmissionAnd_eval
    (assign : BVExpr.Assignment) (predicates : List BVLogicalExpr) :
    BVLogicalExpr.eval assign (finiteADCRawAdmissionAnd predicates) =
      predicates.all (BVLogicalExpr.eval assign) := by
  induction predicates with
  | nil => rfl
  | cons predicate rest ih =>
      simp only [finiteADCRawAdmissionAnd, BVLogicalExpr.eval_gate,
        Gate.eval, List.all_cons, ih]

private theorem finiteADCRawAdmissionAnd_true_iff
    (assign : BVExpr.Assignment) (predicates : List BVLogicalExpr) :
    BVLogicalExpr.eval assign (finiteADCRawAdmissionAnd predicates) = true ↔
      ∀ predicate ∈ predicates, BVLogicalExpr.eval assign predicate = true := by
  rw [finiteADCRawAdmissionAnd_eval, List.all_eq_true]

private theorem finiteADCRawPacketExpr_true_iff
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) :
    BVLogicalExpr.eval (finiteADCRawAdmissionAssignment input)
        (finiteADCRawPacketExpr code counterBits) = true ↔ input.packetAccepted := by
  rw [finiteADCRawPacketExpr, finiteADCRawAdmissionAnd_true_iff]
  constructor
  · intro all
    refine ⟨?_, fun address => ?_⟩
    · have header := all (finiteADCRawAdmissionHeaderExpr counterBits) (by
        simp [finiteADCRawPacketPredicates])
      rw [finiteADCRawAdmissionHeaderExpr_exact] at header
      exact of_decide_eq_true header
    · have word := all (finiteADCRawAdmissionWordExpr code address) (by
        simp only [finiteADCRawPacketPredicates, List.mem_cons, List.mem_ofFn]
        exact Or.inr ⟨finiteADCRawWordAddressEquivFin address, by simp⟩)
      rw [finiteADCRawAdmissionWordExpr_exact] at word
      exact of_decide_eq_true word
  · rintro ⟨header, words⟩ predicate member
    simp only [finiteADCRawPacketPredicates, List.mem_cons, List.mem_ofFn] at member
    rcases member with rfl | ⟨index, rfl⟩
    · rw [finiteADCRawAdmissionHeaderExpr_exact, decide_eq_true_eq]
      exact header
    · rw [finiteADCRawAdmissionWordExpr_exact, decide_eq_true_eq]
      exact words _

private theorem finiteADCRawCalibrationExpr_true_iff
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) :
    BVLogicalExpr.eval (finiteADCRawAdmissionAssignment input)
        (finiteADCRawCalibrationExpr code) = true ↔ input.calibrationAccepted := by
  rw [finiteADCRawCalibrationExpr, finiteADCRawAdmissionAnd_true_iff]
  constructor
  · intro all address
    have span := all (finiteADCRawAdmissionSpanExpr code address) (by
      simp only [finiteADCRawCalibrationPredicates, List.mem_ofFn]
      exact ⟨finiteADCRawSpanAddressEquivFin address, by simp⟩)
    rw [finiteADCRawAdmissionSpanExpr_exact] at span
    exact of_decide_eq_true span
  · intro spans predicate member
    simp only [finiteADCRawCalibrationPredicates, List.mem_ofFn] at member
    rcases member with ⟨index, rfl⟩
    rw [finiteADCRawAdmissionSpanExpr_exact, decide_eq_true_eq]
    exact spans _

private theorem finiteADCRawAdmissionAnd_append_eval
    (assign : BVExpr.Assignment) (left right : List BVLogicalExpr) :
    BVLogicalExpr.eval assign (finiteADCRawAdmissionAnd (left ++ right)) =
      (BVLogicalExpr.eval assign (finiteADCRawAdmissionAnd left) &&
        BVLogicalExpr.eval assign (finiteADCRawAdmissionAnd right)) := by
  induction left with
  | nil => simp [finiteADCRawAdmissionAnd]
  | cons predicate rest ih =>
      simp only [List.cons_append, finiteADCRawAdmissionAnd,
        BVLogicalExpr.eval_gate, Gate.eval, ih, Bool.and_assoc]

private theorem finiteADCRawGraphRun_eq_eval
    (expr : BVLogicalExpr) (assign : BVExpr.Assignment) :
    aigExecutionRead assign.toAIGAssignment (BVLogicalExpr.bitblast expr).ref =
      BVLogicalExpr.eval assign expr := by
  rw [aigExecutionRead_eq_denote, BVLogicalExpr.denote_bitblast]

/-- The whole graph reuses the two original source predicates without expanding their circuits. -/
theorem finiteADCRawAdmissionEval_eq_runs
    (code : FiniteADCResolutionCode) {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    BVLogicalExpr.eval (finiteADCRawAdmissionAssignment (finiteADCRawAdmissionInputOfPacketFor code lastTick packet))
      (finiteADCRawAdmissionExpr code counterBits) =
      (finiteADCRawPacketGateRunFor code lastTick packet && finiteADCRawCalibrationGateRunFor code lastTick packet) := by
  unfold finiteADCRawPacketGateRunFor finiteADCRawPacketGraph
    finiteADCRawCalibrationGateRunFor finiteADCRawCalibrationGraph
  rw [finiteADCRawGraphRun_eq_eval, finiteADCRawGraphRun_eq_eval]
  exact finiteADCRawAdmissionAnd_append_eval _ _ _

private theorem finiteADCRawAdmissionClampedLastTick_exact
    {counterBits : Nat} (lastTick : Nat) (tick : Fin (2 ^ counterBits)) :
    tick.val ≤ (finiteADCRawAdmissionClampedLastTick counterBits lastTick).val ↔
      tick.val ≤ lastTick := by
  unfold finiteADCRawAdmissionClampedLastTick
  dsimp only
  have bound := tick.isLt
  have positive := Nat.two_pow_pos counterBits
  omega

private theorem finiteADCRawAdmissionInput_packetAccepted_iff
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    (finiteADCRawAdmissionInputOfPacketFor code lastTick packet).packetAccepted ↔
      validADCWirePacketFor code lastTick packet := by
  unfold FiniteADCRawAdmissionInput.packetAccepted validADCWirePacketFor
  change
    (packet.1.val ≤ (finiteADCRawAdmissionClampedLastTick counterBits lastTick).val ∧
      ∀ address : FiniteADCRawWordAddress,
        validADCWord code (packet.2 address.1.1 address.1.2 address.2)) ↔ _
  constructor
  · rintro ⟨tick, words⟩
    exact ⟨(finiteADCRawAdmissionClampedLastTick_exact lastTick packet.1).mp tick,
      fun frame leg channel => words ((frame, leg), channel)⟩
  · rintro ⟨tick, words⟩
    exact ⟨(finiteADCRawAdmissionClampedLastTick_exact lastTick packet.1).mpr tick,
      fun address => words address.1.1 address.1.2 address.2⟩

private theorem finiteADCRawAdmissionInput_calibrationAccepted_iff
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    (finiteADCRawAdmissionInputOfPacketFor code lastTick packet).calibrationAccepted ↔
      ∀ leg channel,
        (packet.2 .zeroReference leg channel).val <
          (packet.2 .spanReference leg channel).val := by
  constructor
  · exact fun spans leg channel => spans (leg, channel)
  · exact fun spans address => spans address.1 address.2

private theorem finiteADCRawAdmissionExpr_true_iff
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) :
    BVLogicalExpr.eval (finiteADCRawAdmissionAssignment input)
        (finiteADCRawAdmissionExpr code counterBits) = true ↔ input.accepted := by
  unfold finiteADCRawAdmissionExpr finiteADCRawAdmissionPredicates
    FiniteADCRawAdmissionInput.accepted
  rw [finiteADCRawAdmissionAnd_append_eval, Bool.and_eq_true]
  exact and_congr (finiteADCRawPacketExpr_true_iff input)
    (finiteADCRawCalibrationExpr_true_iff input)

/-- Exact packet admission needs only the finite code, width, bound and raw packet. -/
theorem finiteADCRawPacketGateFor_exact
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawPacketGateRunFor code lastTick packet =
      decide (validADCWirePacketFor code lastTick packet) := by
  unfold finiteADCRawPacketGateRunFor finiteADCRawPacketGraph
  rw [finiteADCRawGraphRun_eq_eval]
  apply Bool.eq_iff_iff.mpr
  rw [finiteADCRawPacketExpr_true_iff, decide_eq_true_eq]
  exact finiteADCRawAdmissionInput_packetAccepted_iff code lastTick packet

theorem finiteADCRawCalibrationGateFor_exact
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawCalibrationGateRunFor code lastTick packet =
      decide (∀ leg channel,
        (packet.2 .zeroReference leg channel).val <
          (packet.2 .spanReference leg channel).val) := by
  unfold finiteADCRawCalibrationGateRunFor finiteADCRawCalibrationGraph
  rw [finiteADCRawGraphRun_eq_eval]
  apply Bool.eq_iff_iff.mpr
  rw [finiteADCRawCalibrationExpr_true_iff, decide_eq_true_eq]
  exact finiteADCRawAdmissionInput_calibrationAccepted_iff code lastTick packet

theorem finiteADCRawAdmissionGateFor_exact
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawAdmissionGateRunFor code lastTick packet =
      decide (validADCWirePacketFor code lastTick packet ∧
        ∀ leg channel, (packet.2 .zeroReference leg channel).val <
          (packet.2 .spanReference leg channel).val) := by
  unfold finiteADCRawAdmissionGateRunFor finiteADCRawAdmissionGraph
  rw [finiteADCRawGraphRun_eq_eval]
  apply Bool.eq_iff_iff.mpr
  rw [finiteADCRawAdmissionExpr_true_iff, decide_eq_true_eq]
  exact and_congr (finiteADCRawAdmissionInput_packetAccepted_iff code lastTick packet)
    (finiteADCRawAdmissionInput_calibrationAccepted_iff code lastTick packet)

theorem finiteADCRawPacketGate_exact
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawPacketGateRun source lastTick packet =
      decide (validADCWirePacket source lastTick packet) :=
  finiteADCRawPacketGateFor_exact source.adcCode lastTick packet

theorem finiteADCRawCalibrationGate_exact
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawCalibrationGateRun source lastTick packet =
      decide (∀ leg channel,
        (packet.2 .zeroReference leg channel).val <
          (packet.2 .spanReference leg channel).val) :=
  finiteADCRawCalibrationGateFor_exact source.adcCode lastTick packet

theorem finiteADCRawCalibrationGate_exact_of_validWords
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits)
    (validWords : ∀ frame leg channel,
      validADCWord source.adcCode (packet.2 frame leg channel)) :
    finiteADCRawCalibrationGateRun source lastTick packet =
      decide (validADCEnergyCalibration (unpackADCWirePacket source packet)) := by
  rw [finiteADCRawCalibrationGate_exact]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro spans leg channel
    exact (finiteADCDecodedSpanPositive_iff_raw_lt source.adcCode _ _
      (validWords .zeroReference leg channel)
      (validWords .spanReference leg channel)).mpr (spans leg channel)
  · intro calibrated leg channel
    exact (finiteADCDecodedSpanPositive_iff_raw_lt source.adcCode _ _
      (validWords .zeroReference leg channel)
      (validWords .spanReference leg channel)).mp (calibrated leg channel)

theorem finiteADCRawAdmissionGate_exact
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawAdmissionGateRun source lastTick packet =
      decide (finiteADCRawPacketAdmission source lastTick packet) := by
  unfold finiteADCRawAdmissionGateRun
  rw [finiteADCRawAdmissionGateFor_exact]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, validADCWirePacketFor, finiteADCRawPacketAdmission, and_assoc]
  symm
  exact decide_eq_true_iff

theorem finiteADCRawPacketGateTicks_pos
    (code : FiniteADCResolutionCode) (counterBits : Nat) :
    0 < finiteADCRawPacketGateTicks code counterBits := by
  unfold finiteADCRawPacketGateTicks
  have bound := (finiteADCRawPacketGraph code counterBits).ref.hgate
  omega

theorem finiteADCRawCalibrationGateTicks_pos (code : FiniteADCResolutionCode) :
    0 < finiteADCRawCalibrationGateTicks code := by
  unfold finiteADCRawCalibrationGateTicks
  have bound := (finiteADCRawCalibrationGraph code).ref.hgate
  omega

theorem finiteADCRawAdmissionGateTicks_pos
    (code : FiniteADCResolutionCode) (counterBits : Nat) :
    0 < finiteADCRawAdmissionGateTicks code counterBits := by
  unfold finiteADCRawAdmissionGateTicks
  have bound := (finiteADCRawAdmissionGraph code counterBits).ref.hgate
  omega

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
