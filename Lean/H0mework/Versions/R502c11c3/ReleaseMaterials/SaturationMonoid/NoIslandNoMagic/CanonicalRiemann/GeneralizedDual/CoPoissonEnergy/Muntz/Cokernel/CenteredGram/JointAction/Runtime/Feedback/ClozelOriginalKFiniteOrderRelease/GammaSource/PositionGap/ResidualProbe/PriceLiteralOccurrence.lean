import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PriceLiteralOccurrence

open BurnolPhysicalState HilbertInventory HilbertInventory.SecondConductorStock
open HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open SourceOperationEffects SourceOperationScalarInventoryLift
open scoped lp

open private current damping_ne from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients
open private fullRead from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse
open private nativeLanguage from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private packet_whole_at from
  H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit

namespace Receipt
export OriginalKDirectRCofinalMaterial.AS (nativeAfterAdmission localNativeReceipt bornAfterNative)
end Receipt

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

private def ratio (level : Nat) (a : ℓ²(Nat, ℂ)) : ℂ := a (level+1) / a level

private theorem ratio_step (coord : BurnolCompletedMellinCoordinate) (a b : ℓ²(Nat, ℂ))
    (level : Nat) (step : nextCoefficients coord a = b) (vanish : ∀ i < level, a i = 0)
    (headLive : a level ≠ 0) (nextLive : b level ≠ 0) :
    ratio level b = ratio level a - 1 := by
  let δ : ℂ := sourceDamping coord
  have head : δ * b level = -a level := by
    cases level with
    | zero => simpa only [step] using nextCoefficients_zero coord a
    | succ j =>
      have previous : a j = 0 := vanish j (Nat.lt_succ_self j)
      simpa only [step,previous,zero_sub] using nextCoefficients_succ coord a j
  have adjacent : δ * b (level+1) = a level - a (level+1) := by
    simpa only [step] using nextCoefficients_succ coord a level
  have cancel : a (level+1) / a level * a level = a (level+1) :=
    div_mul_cancel₀ _ headLive
  unfold ratio
  apply (div_eq_iff nextLive).2
  apply mul_left_cancel₀ (damping_ne coord)
  calc
    δ * b (level+1) = a level - a (level+1) := adjacent
    _ = (a (level+1) / a level - 1) * (δ * b level) := by
      rw [head,sub_mul,mul_neg,one_mul,cancel]
      ring
    _ = δ * ((a (level+1) / a level - 1) * b level) := by ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "stock" => actualWide observation nontrivial half depth
local notation "inventory" => coefficientsAt observation nontrivial half depth
local notation "Data" => DivisionPriceStream.Stream observation nontrivial half depth
local notation "graph" => DivisionPriceStream.graph observation nontrivial half depth
local notation "capture" => DivisionPriceStream.capture observation nontrivial half depth
local notation "priceAt" => DivisionPriceStream.prices observation nontrivial half depth
local notation "advance" => DivisionPriceStream.advance observation nontrivial half depth
local notation "packet" => Native.packet observation nontrivial half depth
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth

private def coefficients (x : Wide) : ℓ²(Nat, ℂ) :=
  (wholeCoordinates c (fullRead (x : Ambient))).fst

local notation "coeff" => coefficients observation half

private theorem coefficients_at (ordinal : Nat) : coeff (stock ordinal) = inventory ordinal := by
  let v := current observation nontrivial half depth ordinal
  have paid := branchCoordinates_gap c ((v : BurnolL2),0) v (add_zero _)
  have read := congrArg (fun value : WholeBranchStock => value.1.fst) paid
  change (wholeCoordinates c ((v : BurnolL2)+0)).fst = (basis c).repr v at read
  rw [add_zero] at read
  exact read

private theorem ratio_at (ordinal : Nat) :
    ratio m (inventory ordinal) = ratio m (inventory 0) - (ordinal : ℂ) := by
  induction ordinal with
  | zero => simp
  | succ n earlier =>
    have before := actual_division_first_coefficient observation nontrivial half depth n
    have after := actual_division_first_coefficient observation nontrivial half depth (n+1)
    have step := ratio_step c (inventory n) (inventory (n+1)) m
      (actual_division_coefficient_step observation nontrivial half depth n) before.1 before.2.2 after.2.2
    rw [step,earlier,Nat.cast_succ]
    ring

/-- The native neighbor difference subtracts one from the first live ratio on each actual action. -/
theorem actual_clock_coordinate (ordinal : Nat) :
    (ratio m (inventory 0) - ratio m (coeff (stock ordinal))).re = (ordinal : ℝ) := by
  rw [coefficients_at,ratio_at observation nontrivial half depth ordinal,sub_sub_cancel]
  exact Complex.natCast_re ordinal

/-- Read a candidate literal address from the original prices and the fixed root's initial ratio. -/
def address (data : Data) : Nat := ⌊(ratio m (inventory 0) - ratio m (coeff (graph data))).re⌋₊

local notation "addressAt" => address observation nontrivial half depth

theorem actual_address (ordinal : Nat) : addressAt (capture (stock ordinal)) = ordinal := by
  unfold address
  rw [DivisionPriceStream.graph_capture,actual_clock_coordinate,Nat.floor_natCast]

/-- The complete price match identifies a unique graph value in the fixed original orbit. -/
theorem occurrence_fibre (data : Data) :
    (∀ i, data.val i = priceAt (stock (addressAt data)) i) ↔
      ∃! ordinal, graph data = stock ordinal := by
  have as_capture (ordinal : Nat) (same : graph data = stock ordinal) : data = capture (stock ordinal) :=
    Subtype.ext ((DivisionPriceStream.prices_graph observation nontrivial half depth data).symm.trans
      (congrArg priceAt same))
  constructor
  · intro fit
    have exactData : data = capture (stock (addressAt data)) := Subtype.ext (funext fit)
    refine ⟨addressAt data, (congrArg graph exactData).trans (DivisionPriceStream.graph_capture
      observation nontrivial half depth _),?_⟩
    intro ordinal same
    exact ((congrArg addressAt (as_capture ordinal same)).trans
      (actual_address observation nontrivial half depth ordinal)).symm
  · rintro ⟨ordinal,same,_⟩
    have exactData := as_capture ordinal same
    have found := (congrArg addressAt exactData).trans
      (actual_address observation nontrivial half depth ordinal)
    intro i
    rw [found]
    exact congrArg (fun value : Data => value.val i) exactData

private theorem coefficients_smul (a : ℂ) (x : Wide) (i : Nat) :
    coeff (a • x) i = a * coeff x i := by
  unfold coefficients
  rw [Submodule.coe_smul, map_smul, map_smul]
  rfl

/-- An unchanged clock ratio can accompany a different complete source. -/
theorem scaled_clock_alias (ordinal : Nat) (a : ℂ) (nonzero : a ≠ 0) (changed : a ≠ 1) :
    let data := capture (a • stock ordinal)
    addressAt data = ordinal ∧ ¬ (∀ i, data.val i = priceAt (stock (addressAt data)) i) := by
  let data := capture (a • stock ordinal)
  have read : graph data = a • stock ordinal := DivisionPriceStream.graph_capture
    observation nontrivial half depth _
  have clock : addressAt data = ordinal := by
    unfold address
    rw [read]
    have same : ratio m (coeff (a • stock ordinal)) = ratio m (coeff (stock ordinal)) := by
      unfold ratio
      rw [coefficients_smul,coefficients_smul,mul_div_mul_left _ _ nonzero]
    rw [same,actual_clock_coordinate,Nat.floor_natCast]
  refine ⟨clock,?_⟩
  intro fit
  have fitGraph : graph data = stock (addressAt data) := by
    have exactData : data = capture (stock (addressAt data)) := Subtype.ext (funext fit)
    exact (congrArg graph exactData).trans (DivisionPriceStream.graph_capture
      observation nontrivial half depth _)
  have same := congrArg (fun x => coeff x m) (read.symm.trans (fitGraph.trans (congrArg stock clock)))
  rw [coefficients_smul,coefficients_at] at same
  have cancel : a * inventory ordinal m = (1 : ℂ) * inventory ordinal m :=
    same.trans (one_mul _).symm
  exact changed (mul_right_cancel₀
    (actual_division_first_coefficient observation nontrivial half depth ordinal).2.2 cancel)

/-- The reconstructed address reads an existing dependent admission in the fixed original run. -/
def readPacket (data : Data) : PacketFit.Packet := packet (addressAt data)

local notation "received" => readPacket observation nontrivial half depth

def nativeWrite (data : Data) := Receipt.nativeAfterAdmission factory (received data)

local notation "written" => nativeWrite observation nontrivial half depth

def receipt (data : Data) := Receipt.localNativeReceipt (written data)

def nextPacket (data : Data) : PacketFit.Packet := Receipt.bornAfterNative (written data)

theorem actual_packet (ordinal : Nat) : received (capture (stock ordinal)) = packet ordinal :=
  congrArg packet (actual_address observation nontrivial half depth ordinal)

theorem actual_receipt (ordinal : Nat) :
    HEq (receipt observation nontrivial half depth (capture (stock ordinal)))
      (Receipt.localNativeReceipt (Receipt.nativeAfterAdmission factory (packet ordinal))) := by
  unfold receipt nativeWrite
  rw [actual_packet]

/-- The receipt's native successor and its four-branch write coincide with the independent next K read. -/
theorem actual_native_next (ordinal : Nat) :
    let data := capture (stock ordinal)
    nextPacket observation nontrivial half depth data = received (advance data) ∧
      PacketFit.packetWhole (received data) = fullRead (graph (advance data) : Ambient) := by
  let data := capture (stock ordinal)
  have result := DivisionPriceStream.actual_current_and_next observation nontrivial half depth ordinal
  have nextStream : advance data = capture (stock (ordinal+1)) := result.2.2.1
  have nextGraph : graph (advance data) = stock (ordinal+1) := result.2.1
  have actual : received data = packet ordinal := actual_packet observation nontrivial half depth ordinal
  have nextActual : received (advance data) = packet (ordinal+1) :=
    (congrArg received nextStream).trans (actual_packet observation nontrivial half depth (ordinal+1))
  constructor
  · change PacketFit.Table.nextPacket factory (received data) = received (advance data)
    rw [actual,nextActual]
    exact PacketFit.Table.next_packetAt factory (Native.initial observation nontrivial half depth)
      (Native.firstCfg observation nontrivial half depth) (nativeLanguage observation nontrivial half depth)
      (ordinal+1)
  · rw [actual,packet_whole_at,nextGraph]
    exact Native.calculated_target_raw_successor observation nontrivial half depth ordinal

open ActualCofinalRootResidualConsumer (consume generatedCurrent actual_generated_current)

/-- The existing compiler and whole-ledger receipt use the exact recovered address as their index. -/
def rootedWrite (data : Data) := consume factory initial cfg language (addressAt data)

private def stoppedAt (ordinal : Nat) :=
  ActualCofinalRootResidualConsumer.C.currentAtStop factory initial cfg language ordinal

def canonicalNext (data : Data) := generatedCurrent factory initial cfg language (addressAt data)

private theorem selected_stop (data : Data) :
    stoppedAt observation nontrivial half depth (addressAt data+1) =
      canonicalNext observation nontrivial half depth data :=
  actual_generated_current factory initial cfg language (addressAt data)

attribute [local irreducible] stoppedAt canonicalNext

/-- The next current uses the independently reconstructed successor address in the same runtime. -/
theorem actual_generated_next (ordinal : Nat) :
    let data := capture (stock ordinal)
    stoppedAt observation nontrivial half depth (addressAt (advance data)) =
      canonicalNext observation nontrivial half depth data := by
  let data := capture (stock ordinal)
  have nextStream : advance data = capture (stock (ordinal+1)) :=
    (DivisionPriceStream.actual_current_and_next observation nontrivial half depth ordinal).2.2.1
  have current : addressAt data = ordinal := actual_address observation nontrivial half depth ordinal
  have next : addressAt (advance data) = ordinal+1 :=
    (congrArg addressAt nextStream).trans (actual_address observation nontrivial half depth (ordinal+1))
  have clock := next.trans (congrArg Nat.succ current).symm
  exact (congrArg (stoppedAt observation nontrivial half depth) clock).trans
    (selected_stop observation nontrivial half depth data)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PriceLiteralOccurrence
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
