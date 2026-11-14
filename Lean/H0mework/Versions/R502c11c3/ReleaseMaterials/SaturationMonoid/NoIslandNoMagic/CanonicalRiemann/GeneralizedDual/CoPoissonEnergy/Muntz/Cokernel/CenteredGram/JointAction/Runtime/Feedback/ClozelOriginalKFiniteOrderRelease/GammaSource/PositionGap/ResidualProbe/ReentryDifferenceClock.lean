import Mathlib.Algebra.Group.ForwardDiff
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ReentryDifferenceClock

open BurnolPhysicalState HilbertInventory HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKDirectRCofinalReentrySourceAction
open BurnolPhysicalState.OriginalRSourceJointContact.OutsideHistory
open OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial (sourceIndex)
open scoped InnerProductSpace

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private adjointWord betaRead vector_ne raw_power from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn
open private adjoint_powers_R from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionXiEscape
open private source_right_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource

open private damping_ne from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "δ" => (sourceDamping c : ℂ)
local notation "R" => burnolDirectRightResolventCLM c
local notation "T" => sourceCayley c
local notation "J" => ContinuousLinearMap.adjoint (sourceCayley c)
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "V" => (sourceReentryVector c : BurnolPaAmbientCarrier)
local notation "β" => betaRead observation half
local notation "k" => FirstPaReturn.exitIndex observation nontrivial half
local notation "word" => adjointWord observation nontrivial half
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "stock" => actualWide observation nontrivial half depth
local notation "capture" => DivisionPriceStream.capture observation nontrivial half depth
local notation "received" => PriceLiteralOccurrence.readPacket observation nontrivial half depth
local notation "face" => AdjointCofinalReturn.face observation nontrivial half depth

private theorem word_power : word = J^k := by
  have positive := (FirstPaReturn.first_exit observation nontrivial half).1
  have next : k-1+1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt positive)
  have literal : word = J^(k-1+1) := by rw [pow_succ']; rfl
  exact literal.trans (congrArg (fun j : Nat => J^j) next)

private def normal (value : BurnolL2) (level n : Nat) : ℂ :=
  (-δ)^n * β ((J^level) ((R^n) value))

local notation "row" => normal observation half

private def drop (f : Nat → ℂ) : Nat → ℂ := - fwdDiff 1 f

private theorem drop_step (value : BurnolL2) (level : Nat) :
    drop (row value (level+1)) = row value level := by
  funext n
  let old := (R^n) value
  let lifted := (J^(level+1)) old
  have performed : T lifted = (J^level) old := by
    change T ((J^(level+1)) old) = _
    rw [pow_succ',mul_apply_eq_comp,source_right_inverse]
  have paid : β lifted + δ * β (R lifted) = β ((J^level) old) := by
    have read := congrArg (fun v : BurnolL2 => β v) performed
    rw [sourceCayley_apply,map_add β,map_smul β,smul_eq_mul] at read
    exact read
  have next : (J^(level+1)) ((R^(n+1)) value) = R lifted := by
    rw [pow_succ' (R) n,mul_apply_eq_comp]
    exact adjoint_powers_R c old level.succ
  change -((-δ)^(n+1) * β ((J^(level+1)) ((R^(n+1)) value)) -
    (-δ)^n * β lifted) = (-δ)^n * β ((J^level) old)
  rw [next,pow_succ,← paid]
  ring

private theorem drop_iterate (value : BurnolL2) (level count : Nat) (within : count ≤ level) :
    (drop^[count]) (row value level) = row value (level-count) := by
  induction count with
  | zero => simp
  | succ count earlier =>
    have prev := earlier (Nat.le_of_succ_le within)
    have slot : level-count = (level-(count+1))+1 := by omega
    rw [Function.iterate_succ_apply',prev,slot,drop_step]

private theorem native_powers (ordinal n : Nat) :
    raw (ordinal+n) = (R^n) (raw ordinal) := by
  induction n with
  | zero => simp only [Nat.add_zero,pow_zero,one_apply_eq_self]
  | succ n previous =>
    rw [Nat.add_succ,OriginalKCombFirstFullSourceDynamics.raw_successor,
      OriginalKCombCofinalRAction.original_R_direct,pow_succ',mul_apply_eq_comp,← previous]
    rfl

private theorem test_exists : ∃ i : Nat,
    PhysicalPriceCountable.price (DenseDivisionPrice.height observation nontrivial half depth i) V ≠ 0 := by
  by_contra! silent
  exact vector_ne observation nontrivial half
    (DenseDivisionPrice.separates observation nontrivial half depth V silent)

private def testIndex : Nat := open Classical in Nat.find (test_exists observation nontrivial half depth)

local notation "readAt" => PhysicalPriceCountable.price
  (DenseDivisionPrice.height observation nontrivial half depth (testIndex observation nontrivial half depth))

private theorem test_ne : readAt V ≠ 0 :=
  open Classical in Nat.find_spec (test_exists observation nontrivial half depth)

/-- Read the original receipt's dependent Pa return on one retained original K address. -/
def clock (ordinal n : Nat) : ℂ :=
  let data := capture (stock (ordinal+n))
  (-δ)^n *
    (readAt (E (word (PacketFit.packetWhole (received data))) -
      E (R (E (face data) : BurnolL2))) / readAt V)

local notation "clockAt" => clock observation nontrivial half depth

private theorem clock_native (ordinal : Nat) : clockAt ordinal = row (raw ordinal) k := by
  funext n
  let data := capture (stock (ordinal+n))
  let nextOf := DivisionPriceStream.advance observation nontrivial half depth
  have receipt : word (PacketFit.packetWhole (received data)) = face (nextOf data) :=
    AdjointCofinalReturn.receipt_face observation nontrivial half depth (ordinal+n)
  have effect : E (face (nextOf data)) - E (R (E (face data) : BurnolL2)) = β (face data) • V :=
    AdjointCofinalReturn.face_write observation nontrivial half depth data
  have price : readAt (β (face data) • V) = β (face data) * readAt V := by
    unfold PhysicalPriceCountable.price
    rw [map_smul,smul_eq_mul]
  have source : face data = (J^k) ((R^n) (raw ordinal)) := by
    rw [AdjointCofinalReturn.face_actual,word_power,native_powers]
  have measured : readAt (E (word (PacketFit.packetWhole (received data))) -
      E (R (E (face data) : BurnolL2))) / readAt V = β (face data) := by
    rw [receipt,effect,price,mul_div_cancel_right₀ _ (test_ne observation nontrivial half depth)]
  change (-δ)^n * _ = (-δ)^n * β ((J^k) ((R^n) (raw ordinal)))
  rw [measured,source]

/-- A finite word of existing receipt prices generates the native literal return coefficient. -/
def fee (ordinal : Nat) : ℂ := (drop^[k]) (clockAt ordinal) 0
local notation "decoded" => fee observation nontrivial half depth

theorem literal_fee (ordinal : Nat) : decoded ordinal = β (raw ordinal) := by
  unfold fee
  rw [clock_native,drop_iterate observation half (raw ordinal) k k le_rfl,Nat.sub_self]
  simp only [normal,pow_zero,one_apply_eq_self,one_mul]

/-- The actual original cofinal Pa write consumes the fee decoded from that same occurrence's receipts. -/
theorem literal_write (ordinal : Nat) :
    pa (ordinal+1) - E (R (pa ordinal : BurnolL2)) = decoded ordinal • V := by
  have write := OriginalKCombCofinalPaAction.actual_defect_value observation nontrivial half depth ordinal
  have native := actual_reentry_Q_generated observation nontrivial half depth ordinal
  have direct : OriginalKCombPhysicalAction.R observation nontrivial half (pa ordinal : BurnolL2) =
      R (pa ordinal : BurnolL2) := OriginalKCombCofinalRAction.original_R_direct observation nontrivial half _
  rw [direct] at write
  have returned : E (OriginalKCombPhysicalAction.R observation nontrivial half
      (OriginalKCombCofinalPaAction.invisible (raw ordinal))) = β (raw ordinal) • V := native
  rw [write,returned,literal_fee]

private theorem beta_zero_of_pa {value : BurnolL2} (inside : value ∈ burnolOriginalPaInL2) :
    β value = 0 := by
  obtain ⟨p,belongs,rfl⟩ := Submodule.mem_map.mp inside
  let Q := OriginalKCombCofinalPaAction.Q
  have physical : burnolEvenAmbientProjection (p : BurnolL2) = p :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p
  have erased : Q (p : BurnolL2) = 0 := by
    change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolEvenAmbientProjection (p : BurnolL2)) = 0
    rw [physical]
    exact Submodule.starProjection_orthogonal_apply_eq_zero belongs
  change inner ℂ (fourierL2 (burnolUnitTailResponse
    (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4)) (Q (p : BurnolL2) : BurnolL2) = 0
  rw [erased,Submodule.coe_zero,inner_zero_right]

local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)

private theorem initial_row (j : Nat) (before : j < k) : row seed j 0 = 0 := by
  have inside : (J^j) seed ∈ burnolOriginalPaInL2 :=
    (FirstPaReturn.first_exit observation nontrivial half).2.2.2 j before
  simpa only [normal,pow_zero,one_apply_eq_self,one_mul] using beta_zero_of_pa observation half inside

private theorem constant_above (value : BurnolL2) (j : Nat) (silent : row value j = 0) :
    row value (j+1) = fun _ => row value (j+1) 0 := by
  funext n
  induction n with
  | zero => rfl
  | succ n previous =>
    have diff := congrFun ((drop_step observation half value j).trans silent) n
    change -(row value (j+1) (n+1) - row value (j+1) n) = 0 at diff
    exact (sub_eq_zero.mp (neg_eq_zero.mp diff)).trans previous

private theorem original_clock (ordinal n : Nat) :
    (-δ)^(sourceIndex observation ordinal) * clockAt ordinal n =
      row seed k (n + sourceIndex observation ordinal) := by
  rw [clock_native]
  let site := sourceIndex observation ordinal
  change (-δ)^site * ((-δ)^n * β ((J^k) ((R^n) (raw ordinal)))) =
    (-δ)^(n+site) * β ((J^k) ((R^(n+site)) seed))
  rw [raw_power,show sourceIndex observation ordinal = site from rfl,
    pow_add (R) n site,mul_apply_eq_comp,pow_add (-δ) n site]
  ring

private theorem clock_shift (start offset n : Nat) :
    clockAt start (offset+n) = (-δ)^offset * clockAt (start+offset) n := by
  unfold clock
  rw [← Nat.add_assoc start offset n,pow_add,mul_assoc]

private theorem drop_constant (a : ℂ) : drop (fun _ => a) = 0 := by
  funext n
  simp [drop]

private theorem drop_positive_constant (j : Nat) (positive : 0 < j) (a : ℂ) :
    (drop^[j]) (fun _ => a) = 0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [Function.iterate_succ_apply,drop_constant]
  clear positive
  induction j with
  | zero => rfl
  | succ j previous => rw [Function.iterate_succ_apply',previous]; exact drop_constant 0

/-- Literal tail silence is exactly stationarity of the compensated actual receipt clock. -/
theorem literal_silence_iff_constant :
    (∃ cutoff : Nat, ∀ ordinal ≥ cutoff, decoded ordinal = 0) ↔
      ∀ n : Nat, clockAt 0 n = clockAt 0 0 := by
  constructor
  · rintro ⟨cutoff,silent⟩
    let index := sourceIndex observation cutoff
    have quiet (n : Nat) (late : index ≤ n) : β ((R^n) seed) = 0 := by
      let ordinal := n-sourceIndex observation 0
      have address : sourceIndex observation ordinal = n := by
        dsimp [index,ordinal,sourceIndex] at *
        omega
      have later : cutoff ≤ ordinal := by
        dsimp [index,ordinal,sourceIndex] at *
        omega
      have paid := silent ordinal later
      rw [literal_fee,raw_power,address] at paid
      exact paid
    have lowest : row seed 0 = 0 := by
      funext n
      have paid := original_power_read_zero_of_tail (β) c seed index quiet n
      simp only [normal,pow_zero,one_apply_eq_self,paid,mul_zero,Pi.zero_apply]
    have lower (j : Nat) (before : j < k) : row seed j = 0 := by
      induction j with
      | zero => exact lowest
      | succ j earlier =>
        rw [constant_above observation half seed j (earlier (by omega)),
          initial_row observation nontrivial half (j+1) before]
        rfl
    have pos := (FirstPaReturn.first_exit observation nontrivial half).1
    have prior : k-1 < k := by omega
    have stationarity := constant_above observation half seed (k-1) (lower (k-1) prior)
    have head : k-1+1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt pos)
    rw [head] at stationarity
    intro n
    apply mul_left_cancel₀ (pow_ne_zero (sourceIndex observation 0) (neg_ne_zero.mpr (damping_ne c)))
    rw [original_clock,original_clock,congrFun stationarity (n+sourceIndex observation 0),
      congrFun stationarity (0+sourceIndex observation 0)]
  · intro constant
    refine ⟨0, fun ordinal _ => ?_⟩
    have stationary : clockAt ordinal = fun _ => clockAt ordinal 0 := by
      funext n
      apply mul_left_cancel₀ (pow_ne_zero ordinal (neg_ne_zero.mpr (damping_ne c)))
      have a := clock_shift observation nontrivial half depth 0 ordinal n
      have b := clock_shift observation nontrivial half depth 0 ordinal 0
      rw [Nat.zero_add] at a b
      rw [← a,← b]
      exact (constant _).trans (constant _).symm
    unfold fee
    rw [stationary,drop_positive_constant _ (FirstPaReturn.first_exit observation nontrivial half).1]
    rfl

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ReentryDifferenceClock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
