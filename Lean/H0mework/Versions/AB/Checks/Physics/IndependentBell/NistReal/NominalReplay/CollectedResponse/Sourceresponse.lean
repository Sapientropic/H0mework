import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.Investigation.CollectedSource.Collection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Source-generated collected CH response

The finite real Collection source and its actual transmission/loss columns generate
all three non-normalized optical objects. Public angles are measured from V: the
rank-one click vector is (sin φ, cos φ) in the unchanged H-first carrier.
The single-pair and named M3 rate laws consume these objects before CH is formed.
Calibration bounds are conditional consumers of source-generated rates.
-/

set_option autoImplicit false

namespace P23.Collection.Response

open scoped BigOperators
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B]
variable (p : Preparation) (f : Source A B) (oA : Optic A) (oB : Optic B)

def jointTotal : ℝ := (omegaAB p f oA oB).hh + (omegaAB p f oA oB).vv
def jointContrast : ℝ := (omegaAB p f oA oB).vv - (omegaAB p f oA oB).hh
def jointCoherence : ℝ := 2 * (omegaAB p f oA oB).hv
def aliceTotal : ℝ := (omegaA p f oA).1 + (omegaA p f oA).2
def bobTotal : ℝ := (omegaB p f oB).1 + (omegaB p f oB).2
def aliceContrast : ℝ := (omegaA p f oA).2 - (omegaA p f oA).1
def bobContrast : ℝ := (omegaB p f oB).2 - (omegaB p f oB).1

/-- The V-referenced joint rank-one effect consumes the actual collected joint object. -/
def linearBorn (a b : ℝ) : ℝ :=
  jointRead (omegaAB p f oA oB) (Real.sin a * Real.sin b) (Real.cos a * Real.cos b)

theorem linearBorn_from_source (a b : ℝ) :
    linearBorn p f oA oB a b =
      ∑ i, ∑ j, (p.c * branch f oA oB false false false i j *
        (Real.sin a * Real.sin b) + p.s * branch f oA oB true false false i j *
        (Real.cos a * Real.cos b)) ^ 2 :=
  joint_read_from_source p f oA oB _ _

/-- Singles retain the partner's lost polarization and mode labels. -/
def aliceBorn (a : ℝ) : ℝ :=
  (omegaA p f oA).1 * Real.sin a ^ 2 + (omegaA p f oA).2 * Real.cos a ^ 2

def bobBorn (b : ℝ) : ℝ :=
  (omegaB p f oB).1 * Real.sin b ^ 2 + (omegaB p f oB).2 * Real.cos b ^ 2

theorem aliceBorn_from_loss (a : ℝ) :
    aliceBorn p f oA a =
      p.c ^ 2 * (power f oA oB false false false + power f oA oB false false true) *
        Real.sin a ^ 2 +
      p.s ^ 2 * (power f oA oB true false false + power f oA oB true false true) *
        Real.cos a ^ 2 := by
  unfold aliceBorn omegaA
  rw [alice_includes_partner_loss f oA oB false, alice_includes_partner_loss f oA oB true]

theorem bobBorn_from_loss (b : ℝ) :
    bobBorn p f oB b =
      p.c ^ 2 * (power f oA oB false false false + power f oA oB false true false) *
        Real.sin b ^ 2 +
      p.s ^ 2 * (power f oA oB true false false + power f oA oB true true false) *
        Real.cos b ^ 2 := by
  unfold bobBorn omegaB
  rw [bob_includes_partner_loss f oA oB false, bob_includes_partner_loss f oA oB true]

theorem linearBorn_eq (a b : ℝ) :
    linearBorn p f oA oB a b =
      (jointTotal p f oA oB * (1 + Real.cos (2 * a) * Real.cos (2 * b)) +
        jointContrast p f oA oB * (Real.cos (2 * a) + Real.cos (2 * b)) +
        jointCoherence p f oA oB * Real.sin (2 * a) * Real.sin (2 * b)) / 4 := by
  unfold linearBorn jointRead jointTotal jointContrast jointCoherence
  rw [Real.sin_two_mul, Real.sin_two_mul]
  simp only [mul_pow, Real.sin_sq_eq_half_sub, Real.cos_sq]
  ring

theorem aliceBorn_eq (a : ℝ) :
    aliceBorn p f oA a =
      (aliceTotal p f oA + aliceContrast p f oA * Real.cos (2 * a)) / 2 := by
  unfold aliceBorn aliceTotal aliceContrast
  rw [Real.sin_sq_eq_half_sub, Real.cos_sq]
  ring

theorem bobBorn_eq (b : ℝ) :
    bobBorn p f oB b =
      (bobTotal p f oB + bobContrast p f oB * Real.cos (2 * b)) / 2 := by
  unfold bobBorn bobTotal bobContrast
  rw [Real.sin_sq_eq_half_sub, Real.cos_sq]
  ring

def observedA (Q uA bgA a : ℝ) : ℝ := Q * uA * aliceBorn p f oA a + bgA
def observedB (Q uB bgB b : ℝ) : ℝ := Q * uB * bobBorn p f oB b + bgB

/-- λ=0 is the single-pair rate; λ=1 is the separately named M3 accidental-rate law. -/
def coincidence (lam Q uA uB bgA bgB a b : ℝ) : ℝ :=
  Q * uA * uB * linearBorn p f oA oB a b +
    lam * observedA p f oA Q uA bgA a * observedB p f oB Q uB bgB b

def rawCH (lam Q uA uB bgA bgB a0 a1 b0 b1 : ℝ) : ℝ :=
  coincidence p f oA oB lam Q uA uB bgA bgB a0 b0 +
    coincidence p f oA oB lam Q uA uB bgA bgB a0 b1 +
    coincidence p f oA oB lam Q uA uB bgA bgB a1 b0 -
    coincidence p f oA oB lam Q uA uB bgA bgB a1 b1 -
    observedA p f oA Q uA bgA a0 - observedB p f oB Q uB bgB b0

def aliceCH (lam Q uA uB bgA bgB a0 b0 b1 u : ℝ) : ℝ :=
  rawCH p f oA oB lam Q uA uB bgA bgB a0 u b0 b1

def bobCH (lam Q uA uB bgA bgB a0 a1 b0 u : ℝ) : ℝ :=
  rawCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0 u

def zCoeff (lam Q : ℝ) : ℝ :=
  jointTotal p f oA oB + lam * Q * aliceContrast p f oA * bobContrast p f oB

def cosCoeff (lam Q uA uB d0 d1 : ℝ) : ℝ :=
  Q * uA * uB / 4 * zCoeff p f oA oB lam Q *
    (Real.cos (2 * d0) - Real.cos (2 * d1))

def sinCoeff (Q uA uB d0 d1 : ℝ) : ℝ :=
  Q * uA * uB / 4 * jointCoherence p f oA oB *
    (Real.sin (2 * d0) - Real.sin (2 * d1))

def primedSlope (lam Q uA uB d0 d1 u : ℝ) : ℝ :=
  2 * (-cosCoeff p f oA oB lam Q uA uB d0 d1 * Real.sin (2 * u) +
    sinCoeff p f oA oB Q uA uB d0 d1 * Real.cos (2 * u))

theorem alice_harmonic (lam Q uA uB bgA bgB a0 b0 b1 u : ℝ) :
    aliceCH p f oA oB lam Q uA uB bgA bgB a0 b0 b1 u =
      aliceCH p f oA oB lam Q uA uB bgA bgB a0 b0 b1 0 +
        cosCoeff p f oA oB lam Q uA uB b0 b1 * (Real.cos (2 * u) - 1) +
        sinCoeff p f oA oB Q uA uB b0 b1 * Real.sin (2 * u) := by
  unfold aliceCH rawCH coincidence observedA observedB
  simp only [linearBorn_eq, aliceBorn_eq, bobBorn_eq, cosCoeff, sinCoeff, zCoeff,
    mul_zero, Real.sin_zero, Real.cos_zero]
  ring

theorem bob_harmonic (lam Q uA uB bgA bgB a0 a1 b0 u : ℝ) :
    bobCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0 u =
      bobCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0 0 +
        cosCoeff p f oA oB lam Q uA uB a0 a1 * (Real.cos (2 * u) - 1) +
        sinCoeff p f oA oB Q uA uB a0 a1 * Real.sin (2 * u) := by
  unfold bobCH rawCH coincidence observedA observedB
  simp only [linearBorn_eq, aliceBorn_eq, bobBorn_eq, cosCoeff, sinCoeff, zCoeff,
    mul_zero, Real.sin_zero, Real.cos_zero]
  ring

private theorem harmonic_hasDerivAt (base c s u : ℝ) :
    HasDerivAt
      (fun t : ℝ => base + c * (Real.cos (2 * t) - 1) + s * Real.sin (2 * t))
      (2 * (-c * Real.sin (2 * u) + s * Real.cos (2 * u))) u := by
  have doubled : HasDerivAt (fun t : ℝ => 2 * t) 2 u := hasDerivAt_const_mul 2
  have harmonic := ((hasDerivAt_const u base).add
    (((doubled.cos).sub_const 1).const_mul c)).add ((doubled.sin).const_mul s)
  exact harmonic.congr_deriv (by ring)

theorem alice_hasDerivAt (lam Q uA uB bgA bgB a0 b0 b1 u : ℝ) :
    HasDerivAt (aliceCH p f oA oB lam Q uA uB bgA bgB a0 b0 b1)
      (primedSlope p f oA oB lam Q uA uB b0 b1 u) u := by
  have response_eq : aliceCH p f oA oB lam Q uA uB bgA bgB a0 b0 b1 =
      (fun t : ℝ => aliceCH p f oA oB lam Q uA uB bgA bgB a0 b0 b1 0 +
        cosCoeff p f oA oB lam Q uA uB b0 b1 * (Real.cos (2 * t) - 1) +
        sinCoeff p f oA oB Q uA uB b0 b1 * Real.sin (2 * t)) := by
    funext t
    exact alice_harmonic p f oA oB lam Q uA uB bgA bgB a0 b0 b1 t
  rw [response_eq]
  exact harmonic_hasDerivAt _ _ _ u

theorem bob_hasDerivAt (lam Q uA uB bgA bgB a0 a1 b0 u : ℝ) :
    HasDerivAt (bobCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0)
      (primedSlope p f oA oB lam Q uA uB a0 a1 u) u := by
  have response_eq : bobCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0 =
      (fun t : ℝ => bobCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0 0 +
        cosCoeff p f oA oB lam Q uA uB a0 a1 * (Real.cos (2 * t) - 1) +
        sinCoeff p f oA oB Q uA uB a0 a1 * Real.sin (2 * t)) := by
    funext t
    exact bob_harmonic p f oA oB lam Q uA uB bgA bgB a0 a1 b0 t
  rw [response_eq]
  exact harmonic_hasDerivAt _ _ _ u

/-- Both response directions are indexed by the same actual source and optics. -/
def ResponseAt (lam Q uA uB bgA bgB a0 a1 b0 b1 u v : ℝ) : Prop :=
  (aliceCH p f oA oB lam Q uA uB bgA bgB a0 b0 b1 u =
    aliceCH p f oA oB lam Q uA uB bgA bgB a0 b0 b1 0 +
      cosCoeff p f oA oB lam Q uA uB b0 b1 * (Real.cos (2 * u) - 1) +
      sinCoeff p f oA oB Q uA uB b0 b1 * Real.sin (2 * u)) ∧
  HasDerivAt (aliceCH p f oA oB lam Q uA uB bgA bgB a0 b0 b1)
    (primedSlope p f oA oB lam Q uA uB b0 b1 u) u ∧
  (bobCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0 v =
    bobCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0 0 +
      cosCoeff p f oA oB lam Q uA uB a0 a1 * (Real.cos (2 * v) - 1) +
      sinCoeff p f oA oB Q uA uB a0 a1 * Real.sin (2 * v)) ∧
  HasDerivAt (bobCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0)
    (primedSlope p f oA oB lam Q uA uB a0 a1 v) v

theorem response_contract (lam Q uA uB bgA bgB a0 a1 b0 b1 u v : ℝ) :
    ResponseAt p f oA oB lam Q uA uB bgA bgB a0 a1 b0 b1 u v :=
  ⟨alice_harmonic p f oA oB lam Q uA uB bgA bgB a0 b0 b1 u,
    alice_hasDerivAt p f oA oB lam Q uA uB bgA bgB a0 b0 b1 u,
    bob_harmonic p f oA oB lam Q uA uB bgA bgB a0 a1 b0 v,
    bob_hasDerivAt p f oA oB lam Q uA uB bgA bgB a0 a1 b0 v⟩

theorem models_response (Q uA uB bgA bgB a0 a1 b0 b1 u v : ℝ) :
    ResponseAt p f oA oB 0 Q uA uB bgA bgB a0 a1 b0 b1 u v ∧
    ResponseAt p f oA oB 1 Q uA uB bgA bgB a0 a1 b0 b1 u v :=
  ⟨response_contract p f oA oB 0 Q uA uB bgA bgB a0 a1 b0 b1 u v,
    response_contract p f oA oB 1 Q uA uB bgA bgB a0 a1 b0 b1 u v⟩

private theorem cc_bounds (pol : Bool) :
    0 ≤ power f oA oB pol false false ∧ power f oA oB pol false false ≤ 1 := by
  have conserved := four_branches_conserve f oA oB pol
  have h00 := power_nonnegative f oA oB pol false false
  have h01 := power_nonnegative f oA oB pol false true
  have h10 := power_nonnegative f oA oB pol true false
  have h11 := power_nonnegative f oA oB pol true true
  exact ⟨h00, by linarith⟩

include oB in
private theorem singleA_bounds (pol : Bool) :
    0 ≤ singleA f oA pol ∧ singleA f oA pol ≤ 1 := by
  rw [alice_includes_partner_loss f oA oB pol]
  have conserved := four_branches_conserve f oA oB pol
  have h00 := power_nonnegative f oA oB pol false false
  have h01 := power_nonnegative f oA oB pol false true
  have h10 := power_nonnegative f oA oB pol true false
  have h11 := power_nonnegative f oA oB pol true true
  constructor <;> linarith

include oA in
private theorem singleB_bounds (pol : Bool) :
    0 ≤ singleB f oB pol ∧ singleB f oB pol ≤ 1 := by
  rw [bob_includes_partner_loss f oA oB pol]
  have conserved := four_branches_conserve f oA oB pol
  have h00 := power_nonnegative f oA oB pol false false
  have h01 := power_nonnegative f oA oB pol false true
  have h10 := power_nonnegative f oA oB pol true false
  have h11 := power_nonnegative f oA oB pol true true
  constructor <;> linarith

/-- Generated positivity, loss inclusion, and conservation bounds of one collection source. -/
structure SourceBounds : Prop where
  joint_nonnegative : 0 ≤ jointTotal p f oA oB
  joint_le_one : jointTotal p f oA oB ≤ 1
  alice_nonnegative : 0 ≤ aliceTotal p f oA
  bob_nonnegative : 0 ≤ bobTotal p f oB
  joint_le_alice : jointTotal p f oA oB ≤ aliceTotal p f oA
  joint_le_bob : jointTotal p f oA oB ≤ bobTotal p f oB
  alice_le_one : aliceTotal p f oA ≤ 1
  bob_le_one : bobTotal p f oB ≤ 1
  alice_contrast : |aliceContrast p f oA| ≤ aliceTotal p f oA
  bob_contrast : |bobContrast p f oB| ≤ bobTotal p f oB

theorem source_bounds : SourceBounds p f oA oB := by
  have hc := sq_nonneg p.c
  have hs := sq_nonneg p.s
  have hh := cc_bounds f oA oB false
  have hv := cc_bounds f oA oB true
  have ah := singleA_bounds f oA oB false
  have av := singleA_bounds f oA oB true
  have bh := singleB_bounds f oA oB false
  have bv := singleB_bounds f oA oB true
  have hHH := mul_nonneg hc hh.1
  have hVV := mul_nonneg hs hv.1
  have hAH := mul_nonneg hc ah.1
  have hAV := mul_nonneg hs av.1
  have hBH := mul_nonneg hc bh.1
  have hBV := mul_nonneg hs bv.1
  have hH1 := mul_le_mul_of_nonneg_left hh.2 hc
  have hV1 := mul_le_mul_of_nonneg_left hv.2 hs
  have hA1 := mul_le_mul_of_nonneg_left ah.2 hc
  have hA2 := mul_le_mul_of_nonneg_left av.2 hs
  have hB1 := mul_le_mul_of_nonneg_left bh.2 hc
  have hB2 := mul_le_mul_of_nonneg_left bv.2 hs
  have aLoss := omegaA_generated_loss p f oA oB
  have bLoss := omegaB_generated_loss p f oA oB
  have hALH := mul_nonneg hc (power_nonnegative f oA oB false false true)
  have hALV := mul_nonneg hs (power_nonnegative f oA oB true false true)
  have hBLH := mul_nonneg hc (power_nonnegative f oA oB false true false)
  have hBLV := mul_nonneg hs (power_nonnegative f oA oB true true false)
  dsimp [omegaA, omegaB, omegaAB] at aLoss bLoss
  constructor
  · exact add_nonneg hHH hVV
  · dsimp [jointTotal, omegaAB]; nlinarith [p.unit]
  · exact add_nonneg hAH hAV
  · exact add_nonneg hBH hBV
  · dsimp [jointTotal, aliceTotal, omegaAB, omegaA]; linarith [aLoss.1, aLoss.2]
  · dsimp [jointTotal, bobTotal, omegaAB, omegaB]; linarith [bLoss.1, bLoss.2]
  · dsimp [aliceTotal, omegaA]; nlinarith [p.unit]
  · dsimp [bobTotal, omegaB]; nlinarith [p.unit]
  · apply abs_le.mpr
    dsimp [aliceContrast, aliceTotal, omegaA]
    constructor <;> linarith
  · apply abs_le.mpr
    dsimp [bobContrast, bobTotal, omegaB]
    constructor <;> linarith

def qEff (Q : ℝ) : ℝ :=
  effectiveQ Q (aliceTotal p f oA) (bobTotal p f oB) (jointTotal p f oA oB)

def etaKA (uA : ℝ) : ℝ := etaA (bobTotal p f oB) (jointTotal p f oA oB) uA
def etaKB (uB : ℝ) : ℝ := etaB (aliceTotal p f oA) (jointTotal p f oA oB) uB

def relativeCorrection (lam Q : ℝ) : ℝ :=
  lam * Q * aliceContrast p f oA * bobContrast p f oB / jointTotal p f oA oB

theorem qEff_nonnegative (Q : ℝ) (hQ : 0 ≤ Q) (hT : 0 < jointTotal p f oA oB) :
    0 ≤ qEff p f oA oB Q := by
  have bounds := source_bounds p f oA oB
  exact div_nonneg
    (mul_nonneg (mul_nonneg hQ bounds.alice_nonnegative) bounds.bob_nonnegative) hT.le

theorem correction_bound (lam Q : ℝ) (hlam : lam = 0 ∨ lam = 1)
    (hQ : 0 ≤ Q) (hT : 0 < jointTotal p f oA oB) :
    |relativeCorrection p f oA oB lam Q| ≤ qEff p f oA oB Q := by
  rcases hlam with hzero | hone
  · rw [hzero]
    simpa [relativeCorrection] using qEff_nonnegative p f oA oB Q hQ hT
  · rw [hone]
    have bounds := source_bounds p f oA oB
    have product := mul_le_mul bounds.alice_contrast bounds.bob_contrast
      (abs_nonneg (bobContrast p f oB)) bounds.alice_nonnegative
    have scaled := mul_le_mul_of_nonneg_left product hQ
    have divided := div_le_div_of_nonneg_right scaled hT.le
    simpa [relativeCorrection, qEff, effectiveQ, abs_div, abs_mul,
      abs_of_nonneg hQ, abs_of_pos hT, mul_assoc] using divided

/-- Generated Klyshko rates share the same unscreened preparation and collection planes. -/
theorem calibration_identity (Q uA uB : ℝ) (hT : 0 < jointTotal p f oA oB) :
    qEff p f oA oB Q * etaKA p f oA oB uA * etaKB p f oA oB uB =
      Q * jointTotal p f oA oB * uA * uB := by
  have bounds := source_bounds p f oA oB
  have hTA := lt_of_lt_of_le hT bounds.joint_le_alice
  have hTB := lt_of_lt_of_le hT bounds.joint_le_bob
  exact (effective_rates Q _ _ _ uA uB
    (ne_of_gt hTA) (ne_of_gt hTB) (ne_of_gt hT)).2.2

/-- The effective-pair budget is consumed directly, without changing its rate identity. -/
theorem effective_pair_budget (lam Q qmax : ℝ) (hlam : lam = 0 ∨ lam = 1)
    (hQ : 0 ≤ Q) (hT : 0 < jointTotal p f oA oB)
    (budget : qEff p f oA oB Q ≤ qmax) :
    |relativeCorrection p f oA oB lam Q| ≤ qmax :=
  (correction_bound p f oA oB lam Q hlam hQ hT).trans budget

/-- A collected-pair budget is divided by the two generated Klyshko efficiencies. -/
theorem collected_pair_budget (Q uA uB qmax : ℝ) (hQ : 0 ≤ Q)
    (hT : 0 < jointTotal p f oA oB) (huA0 : 0 ≤ uA) (huA1 : uA ≤ 1)
    (_huB0 : 0 ≤ uB) (huB1 : uB ≤ 1)
    (hEA : 0 < etaKA p f oA oB uA) (hEB : 0 < etaKB p f oA oB uB)
    (budget : Q * jointTotal p f oA oB ≤ qmax) :
    qEff p f oA oB Q ≤ qmax / (etaKA p f oA oB uA * etaKB p f oA oB uB) := by
  apply (le_div_iff₀ (mul_pos hEA hEB)).mpr
  rw [← mul_assoc, calibration_identity p f oA oB Q uA uB hT]
  have hu : uA * uB ≤ 1 := by nlinarith
  have scaled := mul_le_mul_of_nonneg_left hu (mul_nonneg hQ hT.le)
  calc
    Q * jointTotal p f oA oB * uA * uB =
      (Q * jointTotal p f oA oB) * (uA * uB) := by ring
    _ ≤ Q * jointTotal p f oA oB := by simpa using scaled
    _ ≤ qmax := budget

/-- The emitted-one-pair budget first consumes conservation T≤1. -/
theorem emitted_pair_budget (Q uA uB qmax : ℝ) (hQ : 0 ≤ Q)
    (hT : 0 < jointTotal p f oA oB) (huA0 : 0 ≤ uA) (huA1 : uA ≤ 1)
    (huB0 : 0 ≤ uB) (huB1 : uB ≤ 1)
    (hEA : 0 < etaKA p f oA oB uA) (hEB : 0 < etaKB p f oA oB uB)
    (budget : Q ≤ qmax) :
    qEff p f oA oB Q ≤ qmax / (etaKA p f oA oB uA * etaKB p f oA oB uB) := by
  have bounds := source_bounds p f oA oB
  have scaled : Q * jointTotal p f oA oB ≤ Q :=
    by simpa using mul_le_mul_of_nonneg_left bounds.joint_le_one hQ
  have collected : Q * jointTotal p f oA oB ≤ qmax := scaled.trans budget
  exact collected_pair_budget p f oA oB Q uA uB qmax hQ hT huA0 huA1 huB0 huB1
    hEA hEB collected

/-- The common calibration envelope accepts three explicitly distinguished pair-rate budgets. -/
theorem calibrated_correction_bound (lam Q uA uB : ℝ) (hlam : lam = 0 ∨ lam = 1)
    (hQ : 0 ≤ Q) (hT : 0 < jointTotal p f oA oB)
    (huA0 : 0 ≤ uA) (huA1 : uA ≤ 1) (huB0 : 0 ≤ uB) (huB1 : uB ≤ 1)
    (hEA : (93 / 125 : ℝ) ≤ etaKA p f oA oB uA)
    (hEB : (753 / 1000 : ℝ) ≤ etaKB p f oA oB uB)
    (budget : qEff p f oA oB Q ≤ 3 / 5000 ∨
      Q * jointTotal p f oA oB ≤ 3 / 5000 ∨ Q ≤ 3 / 5000) :
    |relativeCorrection p f oA oB lam Q| ≤ (25 / 23343 : ℝ) := by
  have hEApos : 0 < etaKA p f oA oB uA := lt_of_lt_of_le (by norm_num) hEA
  have hEBpos : 0 < etaKB p f oA oB uB := lt_of_lt_of_le (by norm_num) hEB
  have hden : (93 / 125 : ℝ) * (753 / 1000) ≤
      etaKA p f oA oB uA * etaKB p f oA oB uB :=
    mul_le_mul hEA hEB (by norm_num) hEApos.le
  have upper : (3 / 5000 : ℝ) /
      (etaKA p f oA oB uA * etaKB p f oA oB uB) ≤ 25 / 23343 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3 / 5000)
      (by norm_num : (0 : ℝ) < (93 / 125) * (753 / 1000)) hden
    norm_num at h ⊢
    exact h
  rcases budget with effective | collected | emitted
  · have bounded := effective_pair_budget p f oA oB lam Q (3 / 5000) hlam hQ hT effective
    exact bounded.trans (by norm_num)
  · exact (correction_bound p f oA oB lam Q hlam hQ hT).trans
      ((collected_pair_budget p f oA oB Q uA uB (3 / 5000) hQ hT huA0 huA1 huB0 huB1
        hEApos hEBpos collected).trans upper)
  · exact (correction_bound p f oA oB lam Q hlam hQ hT).trans
      ((emitted_pair_budget p f oA oB Q uA uB (3 / 5000) hQ hT huA0 huA1 huB0 huB1
        hEApos hEBpos emitted).trans upper)

/-- The collected ratio and coherence are source readouts, never independently fitted fields. -/
def collectedRatio : ℝ := p.s / p.c * Real.sqrt
  (power f oA oB true false false / power f oA oB false false false)

def gamma : ℝ := overlap f oA oB / Real.sqrt
  (power f oA oB false false false * power f oA oB true false false)

private theorem coherence_factor (c s H V Z : ℝ) (hc : c ≠ 0) (hH : 0 < H) (hV : 0 < V) :
    2 * (c * s * Z) / (c ^ 2 * H + s ^ 2 * V) =
      (Z / Real.sqrt (H * V)) *
        (2 * (s / c * Real.sqrt (V / H)) / (1 + (s / c * Real.sqrt (V / H)) ^ 2)) := by
  let a := Real.sqrt H
  let b := Real.sqrt V
  have ha : a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hH)
  have hb : b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hV)
  have ha2 : a ^ 2 = H := Real.sq_sqrt hH.le
  have hb2 : b ^ 2 = V := Real.sq_sqrt hV.le
  have hratio : Real.sqrt (V / H) = b / a := Real.sqrt_div hV.le H
  have hnorm : Real.sqrt (H * V) = a * b := Real.sqrt_mul hH.le V
  rw [hratio, hnorm, ← ha2, ← hb2]
  have hnormpos : 0 < c ^ 2 * a ^ 2 + s ^ 2 * b ^ 2 := by
    exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_ne_zero hc)
      (sq_pos_of_ne_zero ha)) (mul_nonneg (sq_nonneg s) (sq_nonneg b))
  field_simp

theorem collected_coherence_factor (hc : p.c ≠ 0)
    (hH : 0 < power f oA oB false false false)
    (hV : 0 < power f oA oB true false false) :
    jointCoherence p f oA oB / jointTotal p f oA oB =
      gamma f oA oB * (2 * collectedRatio p f oA oB /
        (1 + collectedRatio p f oA oB ^ 2)) :=
  coherence_factor _ _ _ _ _ hc hH hV

theorem normalized_source_ratio (lam Q : ℝ) (hc : p.c ≠ 0)
    (hH : 0 < power f oA oB false false false)
    (hV : 0 < power f oA oB true false false) (hz : zCoeff p f oA oB lam Q ≠ 0) :
    jointCoherence p f oA oB / zCoeff p f oA oB lam Q =
      (gamma f oA oB * (2 * collectedRatio p f oA oB /
        (1 + collectedRatio p f oA oB ^ 2))) /
          (1 + relativeCorrection p f oA oB lam Q) := by
  rw [← collected_coherence_factor p f oA oB hc hH hV]
  have hT : jointTotal p f oA oB ≠ 0 := by
    have hpos : 0 < p.c ^ 2 * power f oA oB false false false :=
      mul_pos (sq_pos_of_ne_zero hc) hH
    have hnonneg := mul_nonneg (sq_nonneg p.s) hV.le
    exact ne_of_gt (add_pos_of_pos_of_nonneg hpos hnonneg)
  unfold relativeCorrection zCoeff at *
  field_simp

theorem actual_contrast_product_difference :
    aliceContrast p sourceII collectBin0 * bobContrast p sourceII collectBin0 -
      aliceContrast p sourceI collectBin0 * bobContrast p sourceI collectBin0 =
        (-9 / 400 : ℝ) := by
  unfold aliceContrast bobContrast omegaA omegaB
  rw [calibrationI_powers.1, calibrationI_powers.2.1, calibrationI_powers.2.2.1,
    calibrationI_powers.2.2.2, calibrationII_powers.1, calibrationII_powers.2.1,
    calibrationII_powers.2.2.1, calibrationII_powers.2.2.2]
  linear_combination (-9 / 400 : ℝ) * (p.c ^ 2 + p.s ^ 2 + 1) * p.unit

/-- Equal actual joint objects force equal single-pair primed responses. -/
theorem actual_zero_slopes (Q uA uB d0 d1 u : ℝ) :
    primedSlope p sourceI collectBin0 collectBin0 0 Q uA uB d0 d1 u =
      primedSlope p sourceII collectBin0 collectBin0 0 Q uA uB d0 d1 u := by
  unfold primedSlope cosCoeff sinCoeff zCoeff jointTotal jointCoherence
  simp only [zero_mul, add_zero]
  rw [same_collected_joint p]

/-- M3's response difference is generated by the actual two-source loss contrasts. -/
theorem actual_slope_difference (lam Q uA uB d0 d1 u : ℝ) :
    primedSlope p sourceII collectBin0 collectBin0 lam Q uA uB d0 d1 u -
      primedSlope p sourceI collectBin0 collectBin0 lam Q uA uB d0 d1 u =
        -lam * Q ^ 2 * uA * uB / 2 * (-9 / 400 : ℝ) * Real.sin (2 * u) *
          (Real.cos (2 * d0) - Real.cos (2 * d1)) := by
  unfold primedSlope cosCoeff sinCoeff zCoeff jointTotal jointCoherence
  rw [← same_collected_joint p]
  linear_combination (-lam * Q ^ 2 * uA * uB / 2 * Real.sin (2 * u) *
    (Real.cos (2 * d0) - Real.cos (2 * d1))) * actual_contrast_product_difference p

/-- This consumer calls both actual source programs; it does not supply their response coefficients. -/
theorem actual_source_consumer (Q uA uB bgA bgB a0 a1 b0 b1 u v : ℝ) :
    (HasDerivAt
      (aliceCH p sourceI collectBin0 collectBin0 0 Q uA uB bgA bgB a0 b0 b1)
      (primedSlope p sourceII collectBin0 collectBin0 0 Q uA uB b0 b1 u) u ∧
    HasDerivAt
      (bobCH p sourceI collectBin0 collectBin0 0 Q uA uB bgA bgB a0 a1 b0)
      (primedSlope p sourceII collectBin0 collectBin0 0 Q uA uB a0 a1 v) v) ∧
    (primedSlope p sourceII collectBin0 collectBin0 1 Q uA uB b0 b1 u -
      primedSlope p sourceI collectBin0 collectBin0 1 Q uA uB b0 b1 u =
        -Q ^ 2 * uA * uB / 2 * (-9 / 400 : ℝ) * Real.sin (2 * u) *
          (Real.cos (2 * b0) - Real.cos (2 * b1))) ∧
    (primedSlope p sourceII collectBin0 collectBin0 1 Q uA uB a0 a1 v -
      primedSlope p sourceI collectBin0 collectBin0 1 Q uA uB a0 a1 v =
        -Q ^ 2 * uA * uB / 2 * (-9 / 400 : ℝ) * Real.sin (2 * v) *
          (Real.cos (2 * a0) - Real.cos (2 * a1))) := by
  constructor
  · constructor
    · rw [← actual_zero_slopes p Q uA uB b0 b1 u]
      exact alice_hasDerivAt p sourceI collectBin0 collectBin0 0 Q uA uB bgA bgB a0 b0 b1 u
    · rw [← actual_zero_slopes p Q uA uB a0 a1 v]
      exact bob_hasDerivAt p sourceI collectBin0 collectBin0 0 Q uA uB bgA bgB a0 a1 b0 v
  · constructor
    · simpa only [neg_mul, one_mul] using actual_slope_difference p 1 Q uA uB b0 b1 u
    · simpa only [neg_mul, one_mul] using actual_slope_difference p 1 Q uA uB a0 a1 v

end
end P23.Collection.Response
