import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.CollectedResponse.Sourceresponse

/-!
# Public observable laws of one collected source

The primitive is the actual Collection preparation, source amplitudes and local
transmission/loss columns. X is Re Ω(HH,VV), never twice that entry. Public V-reference
effects generate rows (h,v,2w). A common nonnegative readout scale is absorbed into
the same source Gram. Training rows are fixed at 00,01,11; 10 remains held out.
-/

set_option autoImplicit false

namespace P23.Collection.Observable

open scoped BigOperators
noncomputable section

structure DesignRow where
  h : ℝ
  v : ℝ
  cross : ℝ

def angleRow (a b : ℝ) : DesignRow :=
  ⟨(Real.sin a * Real.sin b) ^ 2, (Real.cos a * Real.cos b) ^ 2,
    2 * (Real.sin a * Real.sin b) * (Real.cos a * Real.cos b)⟩

def rowRead (r : DesignRow) (g : JointObject) : ℝ :=
  r.h * g.hh + r.v * g.vv + r.cross * g.hv

def GramCone (g : JointObject) : Prop :=
  0 ≤ g.hh ∧ 0 ≤ g.vv ∧ g.hv ^ 2 ≤ g.hh * g.vv

def det3 (a b c : DesignRow) : ℝ :=
  a.h * (b.v * c.cross - b.cross * c.v) -
    a.v * (b.h * c.cross - b.cross * c.h) +
    a.cross * (b.h * c.v - b.v * c.h)

def deltaH (a b c : DesignRow) (y0 y1 y2 : ℝ) : ℝ :=
  det3 {a with h := y0} {b with h := y1} {c with h := y2}

def deltaV (a b c : DesignRow) (y0 y1 y2 : ℝ) : ℝ :=
  det3 {a with v := y0} {b with v := y1} {c with v := y2}

def deltaX (a b c : DesignRow) (y0 y1 y2 : ℝ) : ℝ :=
  det3 {a with cross := y0} {b with cross := y1} {c with cross := y2}

def recover3 (a b c : DesignRow) (y0 y1 y2 : ℝ) : JointObject :=
  ⟨deltaH a b c y0 y1 y2 / det3 a b c,
    deltaV a b c y0 y1 y2 / det3 a b c,
    deltaX a b c y0 y1 y2 / det3 a b c⟩

/-- Pure linear algebra; the three observations are evaluations of one supplied vector. -/
theorem cramer_generated (a b c : DesignRow) (g : JointObject) :
    deltaH a b c (rowRead a g) (rowRead b g) (rowRead c g) = det3 a b c * g.hh ∧
    deltaV a b c (rowRead a g) (rowRead b g) (rowRead c g) = det3 a b c * g.vv ∧
    deltaX a b c (rowRead a g) (rowRead b g) (rowRead c g) = det3 a b c * g.hv := by
  simp only [deltaH, deltaV, deltaX, det3, rowRead]
  constructor
  · ring
  · constructor <;> ring

theorem recover3_generated (a b c : DesignRow) (g : JointObject) (hd : det3 a b c ≠ 0) :
    recover3 a b c (rowRead a g) (rowRead b g) (rowRead c g) = g := by
  have generated := cramer_generated a b c g
  unfold recover3
  rw [generated.1, generated.2.1, generated.2.2]
  have hh : det3 a b c * g.hh / det3 a b c = g.hh := by field_simp
  have vv : det3 a b c * g.vv / det3 a b c = g.vv := by field_simp
  have hv : det3 a b c * g.hv / det3 a b c = g.hv := by field_simp
  rw [hh, vv, hv]

def nullCoeff (r : Fin 4 → DesignRow) (i : Fin 4) : ℝ :=
  if i = 0 then det3 (r 1) (r 2) (r 3)
  else if i = 1 then -det3 (r 0) (r 2) (r 3)
  else if i = 2 then det3 (r 0) (r 1) (r 3)
  else -det3 (r 0) (r 1) (r 2)

def nullResidual (r : Fin 4 → DesignRow) (y : Fin 4 → ℝ) : ℝ :=
  ∑ i, nullCoeff r i * y i

theorem null_generated (r : Fin 4 → DesignRow) (g : JointObject) :
    nullResidual r (fun i => rowRead (r i) g) = 0 := by
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  simp only [nullResidual, Fin.sum_univ_four, nullCoeff, h10, h20, h21, h30, h31, h32,
    if_pos, if_false]
  simp only [det3, rowRead]
  ring

/-- Calibration rows are frozen at 00,01,11 and never chosen from the held-out value. -/
def trainingMinor (r : Fin 4 → DesignRow) : ℝ := det3 (r 0) (r 1) (r 3)

def recoverTraining (r : Fin 4 → DesignRow) (y : Fin 4 → ℝ) : JointObject :=
  recover3 (r 0) (r 1) (r 3) (y 0) (y 1) (y 3)

def predictHeldOut (r : Fin 4 → DesignRow) (y : Fin 4 → ℝ) : ℝ :=
  rowRead (r 2) (recoverTraining r y)

def heldOutResidual (r : Fin 4 → DesignRow) (y : Fin 4 → ℝ) : ℝ :=
  y 2 - predictHeldOut r y

theorem predict_generated (r : Fin 4 → DesignRow) (g : JointObject)
    (hd : trainingMinor r ≠ 0) :
    predictHeldOut r (fun i => rowRead (r i) g) = rowRead (r 2) g := by
  unfold predictHeldOut recoverTraining
  rw [recover3_generated _ _ _ g hd]

theorem predict_add (r : Fin 4 → DesignRow) (y e : Fin 4 → ℝ)
    (_hd : trainingMinor r ≠ 0) :
    predictHeldOut r (fun i => y i + e i) = predictHeldOut r y + predictHeldOut r e := by
  unfold predictHeldOut recoverTraining recover3 rowRead deltaH deltaV deltaX det3
  field_simp
  ring

variable {A B : Type*} [Fintype A] [Fintype B]
variable (p : Preparation) (f : Source A B) (oA : Optic A) (oB : Optic B)

def amplitudeH (ij : A × B) : ℝ := p.c * branch f oA oB false false false ij.1 ij.2
def amplitudeV (ij : A × B) : ℝ := p.s * branch f oA oB true false false ij.1 ij.2

theorem native_hh : (∑ ij, amplitudeH p f oA oB ij ^ 2) = (omegaAB p f oA oB).hh := by
  simp only [amplitudeH, Fintype.sum_prod_type, omegaAB, power, mul_pow, Finset.mul_sum]

theorem native_vv : (∑ ij, amplitudeV p f oA oB ij ^ 2) = (omegaAB p f oA oB).vv := by
  simp only [amplitudeV, Fintype.sum_prod_type, omegaAB, power, mul_pow, Finset.mul_sum]

theorem native_hv : (∑ ij, amplitudeH p f oA oB ij * amplitudeV p f oA oB ij) =
    (omegaAB p f oA oB).hv := by
  simp only [amplitudeH, amplitudeV, Fintype.sum_prod_type, omegaAB, overlap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The cone certificate is generated by the actual two CC amplitude columns. -/
theorem native_source_cone : GramCone (omegaAB p f oA oB) := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (amplitudeH p f oA oB) (amplitudeV p f oA oB)
  rw [native_hv, native_hh, native_vv] at cauchy
  refine ⟨?_, ?_, cauchy⟩
  · rw [← native_hh]
    exact Finset.sum_nonneg fun ij _ => sq_nonneg _
  · rw [← native_vv]
    exact Finset.sum_nonneg fun ij _ => sq_nonneg _

def scaledGram (sigma : ℝ) : JointObject :=
  ⟨sigma * (omegaAB p f oA oB).hh, sigma * (omegaAB p f oA oB).vv,
    sigma * (omegaAB p f oA oB).hv⟩

theorem scaled_source_cone (sigma : ℝ) (hs : 0 ≤ sigma) :
    GramCone (scaledGram p f oA oB sigma) := by
  have native := native_source_cone p f oA oB
  refine ⟨mul_nonneg hs native.1, mul_nonneg hs native.2.1, ?_⟩
  have scaled := mul_le_mul_of_nonneg_left native.2.2 (sq_nonneg sigma)
  simpa [scaledGram, mul_pow, pow_two, mul_assoc, mul_left_comm, mul_comm] using scaled

def signalJoint (sigma a b : ℝ) : ℝ := sigma * Response.linearBorn p f oA oB a b

theorem source_design (sigma a b : ℝ) :
    signalJoint p f oA oB sigma a b = rowRead (angleRow a b) (scaledGram p f oA oB sigma) := by
  unfold signalJoint Response.linearBorn jointRead rowRead angleRow scaledGram
  ring

def designRows (theta : Fin 4 → ℝ × ℝ) (i : Fin 4) : DesignRow :=
  angleRow (theta i).1 (theta i).2

def sourceFour (sigma : ℝ) (theta : Fin 4 → ℝ × ℝ) (i : Fin 4) : ℝ :=
  signalJoint p f oA oB sigma (theta i).1 (theta i).2

theorem source_null_law (sigma : ℝ) (theta : Fin 4 → ℝ × ℝ) :
    nullResidual (designRows theta) (sourceFour p f oA oB sigma theta) = 0 := by
  unfold sourceFour
  simp_rw [source_design]
  exact null_generated (designRows theta) (scaledGram p f oA oB sigma)

theorem source_recovery (sigma : ℝ) (theta : Fin 4 → ℝ × ℝ)
    (hd : trainingMinor (designRows theta) ≠ 0) :
    recoverTraining (designRows theta) (sourceFour p f oA oB sigma theta) =
      scaledGram p f oA oB sigma := by
  unfold recoverTraining sourceFour
  simp_rw [source_design]
  exact recover3_generated _ _ _ _ hd

theorem source_held_out (sigma : ℝ) (theta : Fin 4 → ℝ × ℝ)
    (hd : trainingMinor (designRows theta) ≠ 0) :
    predictHeldOut (designRows theta) (sourceFour p f oA oB sigma theta) =
      sourceFour p f oA oB sigma theta 2 := by
  unfold predictHeldOut
  rw [source_recovery p f oA oB sigma theta hd]
  exact (source_design p f oA oB sigma _ _).symm

theorem source_cramer_psd (sigma : ℝ) (hs : 0 ≤ sigma) (theta : Fin 4 → ℝ × ℝ) :
    let r := designRows theta
    let y := sourceFour p f oA oB sigma theta
    0 ≤ trainingMinor r * deltaH (r 0) (r 1) (r 3) (y 0) (y 1) (y 3) ∧
    0 ≤ trainingMinor r * deltaV (r 0) (r 1) (r 3) (y 0) (y 1) (y 3) ∧
    deltaX (r 0) (r 1) (r 3) (y 0) (y 1) (y 3) ^ 2 ≤
      deltaH (r 0) (r 1) (r 3) (y 0) (y 1) (y 3) *
      deltaV (r 0) (r 1) (r 3) (y 0) (y 1) (y 3) := by
  dsimp only
  unfold sourceFour
  simp_rw [source_design]
  have generated := cramer_generated (designRows theta 0) (designRows theta 1)
    (designRows theta 3) (scaledGram p f oA oB sigma)
  dsimp only [designRows] at generated ⊢
  rw [generated.1, generated.2.1, generated.2.2]
  have cone := scaled_source_cone p f oA oB sigma hs
  constructor
  · simpa [trainingMinor, designRows, pow_two, mul_assoc] using
      mul_nonneg (sq_nonneg (trainingMinor (designRows theta))) cone.1
  · constructor
    · simpa [trainingMinor, designRows, pow_two, mul_assoc] using
        mul_nonneg (sq_nonneg (trainingMinor (designRows theta))) cone.2.1
    · have bounded := mul_le_mul_of_nonneg_left cone.2.2
        (sq_nonneg (trainingMinor (designRows theta)))
      simpa [trainingMinor, designRows, mul_pow, pow_two, mul_assoc, mul_left_comm,
        mul_comm] using bounded

theorem source_noise_residual (sigma : ℝ) (theta : Fin 4 → ℝ × ℝ) (e : Fin 4 → ℝ)
    (hd : trainingMinor (designRows theta) ≠ 0) :
    heldOutResidual (designRows theta) (fun i => sourceFour p f oA oB sigma theta i + e i) =
      e 2 - predictHeldOut (designRows theta) e := by
  unfold heldOutResidual
  rw [predict_add _ _ _ hd, source_held_out p f oA oB sigma theta hd]
  ring

def mirrorSettings (a0 a1 : ℝ) (i : Fin 4) : ℝ × ℝ :=
  if i = 0 then (a0, -a0) else if i = 1 then (a0, -a1)
  else if i = 2 then (a1, -a0) else (a1, -a1)

theorem source_mirror (sigma a0 a1 : ℝ) :
    sourceFour p f oA oB sigma (mirrorSettings a0 a1) 1 =
      sourceFour p f oA oB sigma (mirrorSettings a0 a1) 2 := by
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  simp only [sourceFour, mirrorSettings, h10, h20, h21, if_pos, if_false, signalJoint,
    Response.linearBorn, jointRead, Real.sin_neg, Real.cos_neg]
  ring

theorem native_h_reference (a b : ℝ) :
    Response.linearBorn p f oA oB a b =
      jointRead (omegaAB p f oA oB)
        (Real.cos (Real.pi / 2 - a) * Real.cos (Real.pi / 2 - b))
        (Real.sin (Real.pi / 2 - a) * Real.sin (Real.pi / 2 - b)) := by
  rw [Real.cos_pi_div_two_sub, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub, Real.sin_pi_div_two_sub]
  rfl

def singleAlphaA (Q uA bgA : ℝ) : ℝ := Q * uA * Response.aliceTotal p f oA / 2 + bgA
def singleAlphaB (Q uB bgB : ℝ) : ℝ := Q * uB * Response.bobTotal p f oB / 2 + bgB
def singleBetaA (Q uA : ℝ) : ℝ := Q * uA * Response.aliceContrast p f oA / 2
def singleBetaB (Q uB : ℝ) : ℝ := Q * uB * Response.bobContrast p f oB / 2

theorem source_single_affineA (Q uA bgA a : ℝ) :
    Response.observedA p f oA Q uA bgA a =
      singleAlphaA p f oA Q uA bgA + singleBetaA p f oA Q uA * Real.cos (2 * a) := by
  rw [Response.observedA, Response.aliceBorn_eq]
  unfold singleAlphaA singleBetaA
  ring

theorem source_single_affineB (Q uB bgB b : ℝ) :
    Response.observedB p f oB Q uB bgB b =
      singleAlphaB p f oB Q uB bgB + singleBetaB p f oB Q uB * Real.cos (2 * b) := by
  rw [Response.observedB, Response.bobBorn_eq]
  unfold singleAlphaB singleBetaB
  ring

def singleBetaRead (s0 s1 a0 a1 : ℝ) : ℝ :=
  (s0 - s1) / (Real.cos (2 * a0) - Real.cos (2 * a1))

theorem source_single_betaA (Q uA bgA a0 a1 : ℝ)
    (hd : Real.cos (2 * a0) - Real.cos (2 * a1) ≠ 0) :
    singleBetaRead (Response.observedA p f oA Q uA bgA a0)
      (Response.observedA p f oA Q uA bgA a1) a0 a1 = singleBetaA p f oA Q uA := by
  rw [source_single_affineA, source_single_affineA]
  unfold singleBetaRead
  field_simp
  ring

theorem source_single_betaB (Q uB bgB b0 b1 : ℝ)
    (hd : Real.cos (2 * b0) - Real.cos (2 * b1) ≠ 0) :
    singleBetaRead (Response.observedB p f oB Q uB bgB b0)
      (Response.observedB p f oB Q uB bgB b1) b0 b1 = singleBetaB p f oB Q uB := by
  rw [source_single_affineB, source_single_affineB]
  unfold singleBetaRead
  field_simp
  ring

def observableZ (g : JointObject) (lam betaA betaB : ℝ) : ℝ :=
  g.hh + g.vv + 4 * lam * betaA * betaB

def observableSlope (g : JointObject) (lam betaA betaB d0 d1 u : ℝ) : ℝ :=
  (-(observableZ g lam betaA betaB) * Real.sin (2 * u) *
      (Real.cos (2 * d0) - Real.cos (2 * d1)) +
    2 * g.hv * Real.cos (2 * u) * (Real.sin (2 * d0) - Real.sin (2 * d1))) / 2

theorem source_observable_slope (lam Q uA uB d0 d1 u : ℝ) :
    Response.primedSlope p f oA oB lam Q uA uB d0 d1 u =
      observableSlope (scaledGram p f oA oB (Q * uA * uB)) lam
        (singleBetaA p f oA Q uA) (singleBetaB p f oB Q uB) d0 d1 u := by
  unfold Response.primedSlope Response.cosCoeff Response.sinCoeff Response.zCoeff
    Response.jointTotal Response.jointCoherence observableSlope observableZ scaledGram
    singleBetaA singleBetaB
  ring

theorem source_alice_observable_deriv (lam Q uA uB bgA bgB a0 b0 b1 u : ℝ) :
    HasDerivAt (Response.aliceCH p f oA oB lam Q uA uB bgA bgB a0 b0 b1)
      (observableSlope (scaledGram p f oA oB (Q * uA * uB)) lam
        (singleBetaA p f oA Q uA) (singleBetaB p f oB Q uB) b0 b1 u) u := by
  rw [← source_observable_slope]
  exact Response.alice_hasDerivAt p f oA oB lam Q uA uB bgA bgB a0 b0 b1 u

theorem source_bob_observable_deriv (lam Q uA uB bgA bgB a0 a1 b0 u : ℝ) :
    HasDerivAt (Response.bobCH p f oA oB lam Q uA uB bgA bgB a0 a1 b0)
      (observableSlope (scaledGram p f oA oB (Q * uA * uB)) lam
        (singleBetaA p f oA Q uA) (singleBetaB p f oB Q uB) a0 a1 u) u := by
  rw [← source_observable_slope]
  exact Response.bob_hasDerivAt p f oA oB lam Q uA uB bgA bgB a0 a1 b0 u

/-- M3 subtraction uses the full observed singles, including their fixed backgrounds. -/
theorem m3_subtraction (lam Q uA uB bgA bgB a b : ℝ) :
    Response.coincidence p f oA oB lam Q uA uB bgA bgB a b -
      lam * Response.observedA p f oA Q uA bgA a * Response.observedB p f oB Q uB bgB b =
        signalJoint p f oA oB (Q * uA * uB) a b := by
  unfold Response.coincidence signalJoint
  ring

theorem m3_background_order (lam Q uA uB bgA bgB a b : ℝ) :
    let sA := Response.observedA p f oA Q uA bgA a - bgA
    let sB := Response.observedB p f oB Q uB bgB b - bgB
    Response.coincidence p f oA oB lam Q uA uB bgA bgB a b -
      lam * (sA * sB + bgA * sB + bgB * sA + bgA * bgB) =
        signalJoint p f oA oB (Q * uA * uB) a b := by
  dsimp
  rw [← m3_subtraction p f oA oB lam Q uA uB bgA bgB a b]
  ring

def orSingle (background signal : ℝ) : ℝ := background + (1 - background) * signal

def orCoincidence (bgA bgB aSignal bSignal jointSignal : ℝ) : ℝ :=
  (1 - bgA) * (1 - bgB) * jointSignal + bgA * (1 - bgB) * bSignal +
    bgB * (1 - bgA) * aSignal + bgA * bgB

def orScale (bgA bgB : ℝ) : ℝ := (1 - bgA) * (1 - bgB)

theorem or_correction (bgA bgB aSignal bSignal jointSignal : ℝ) :
    orCoincidence bgA bgB aSignal bSignal jointSignal -
      bgB * orSingle bgA aSignal - bgA * orSingle bgB bSignal + bgA * bgB =
        orScale bgA bgB * jointSignal := by
  unfold orCoincidence orSingle orScale
  ring

theorem or_single_inverse (background signal : ℝ) (hb : background ≠ 1) :
    (orSingle background signal - background) / (1 - background) = signal := by
  have h : 1 - background ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  unfold orSingle
  field_simp
  ring

def sourceORJoint (Q uA uB bgA bgB a b : ℝ) : ℝ :=
  orCoincidence bgA bgB (Response.observedA p f oA Q uA 0 a)
    (Response.observedB p f oB Q uB 0 b) (signalJoint p f oA oB (Q * uA * uB) a b)

theorem source_OR_correction (Q uA uB bgA bgB a b : ℝ) :
    sourceORJoint p f oA oB Q uA uB bgA bgB a b -
      bgB * orSingle bgA (Response.observedA p f oA Q uA 0 a) -
      bgA * orSingle bgB (Response.observedB p f oB Q uB 0 b) + bgA * bgB =
        signalJoint p f oA oB (orScale bgA bgB * (Q * uA * uB)) a b := by
  rw [sourceORJoint, or_correction]
  unfold signalJoint
  ring

theorem source_OR_cone (sigma bgA bgB : ℝ) (hs : 0 ≤ sigma)
    (hA : bgA ≤ 1) (hB : bgB ≤ 1) :
    GramCone (scaledGram p f oA oB (orScale bgA bgB * sigma)) := by
  exact scaled_source_cone p f oA oB _
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)) hs)

def gramCH (g : JointObject) (a0 a1 b0 b1 : ℝ) : ℝ :=
  rowRead (angleRow a0 b0) g + rowRead (angleRow a0 b1) g +
    rowRead (angleRow a1 b0) g - rowRead (angleRow a1 b1) g

def sourceORCH (Q uA uB bgA bgB a0 a1 b0 b1 : ℝ) : ℝ :=
  sourceORJoint p f oA oB Q uA uB bgA bgB a0 b0 +
    sourceORJoint p f oA oB Q uA uB bgA bgB a0 b1 +
    sourceORJoint p f oA oB Q uA uB bgA bgB a1 b0 -
    sourceORJoint p f oA oB Q uA uB bgA bgB a1 b1 -
    orSingle bgA (Response.observedA p f oA Q uA 0 a0) -
    orSingle bgB (Response.observedB p f oB Q uB 0 b0)

/-- OR's fixed-background affine terms cancel from every simultaneous primed update. -/
theorem source_OR_gain (Q uA uB bgA bgB a0 a1 b0 b1 a1' b1' : ℝ) :
    sourceORCH p f oA oB Q uA uB bgA bgB a0 a1' b0 b1' -
      sourceORCH p f oA oB Q uA uB bgA bgB a0 a1 b0 b1 =
        gramCH (scaledGram p f oA oB (orScale bgA bgB * (Q * uA * uB))) a0 a1' b0 b1' -
          gramCH (scaledGram p f oA oB (orScale bgA bgB * (Q * uA * uB))) a0 a1 b0 b1 := by
  unfold sourceORCH sourceORJoint orCoincidence orSingle gramCH
  simp_rw [← source_design]
  unfold signalJoint orScale
  ring

def sourceOROffset (Q uA uB bgA bgB a0 b0 : ℝ) : ℝ :=
  2 * bgA * bgB - bgA - bgB +
    (1 - bgA) * (2 * bgB - 1) * Response.observedA p f oA Q uA 0 a0 +
    (1 - bgB) * (2 * bgA - 1) * Response.observedB p f oB Q uB 0 b0 +
    orScale bgA bgB * (Response.observedA p f oA Q uA 0 a0 +
      Response.observedB p f oB Q uB 0 b0)

theorem source_OR_CH_eq (Q uA uB bgA bgB a0 a1 b0 b1 : ℝ) :
    sourceORCH p f oA oB Q uA uB bgA bgB a0 a1 b0 b1 =
      orScale bgA bgB * Response.rawCH p f oA oB 0 Q uA uB 0 0 a0 a1 b0 b1 +
        sourceOROffset p f oA oB Q uA uB bgA bgB a0 b0 := by
  unfold sourceORCH sourceORJoint orCoincidence orSingle Response.rawCH
    Response.coincidence signalJoint sourceOROffset orScale
  ring

theorem source_OR_alice_deriv (Q uA uB bgA bgB a0 b0 b1 u : ℝ) :
    HasDerivAt (fun t => sourceORCH p f oA oB Q uA uB bgA bgB a0 t b0 b1)
      (observableSlope (scaledGram p f oA oB (orScale bgA bgB * (Q * uA * uB)))
        0 0 0 b0 b1 u) u := by
  have eqn : (fun t => sourceORCH p f oA oB Q uA uB bgA bgB a0 t b0 b1) =
      (fun t => orScale bgA bgB * Response.aliceCH p f oA oB 0 Q uA uB 0 0 a0 b0 b1 t +
        sourceOROffset p f oA oB Q uA uB bgA bgB a0 b0) := by
    funext t
    exact source_OR_CH_eq p f oA oB Q uA uB bgA bgB a0 t b0 b1
  rw [eqn]
  have deriv := (Response.alice_hasDerivAt p f oA oB 0 Q uA uB 0 0 a0 b0 b1 u).const_mul
    (orScale bgA bgB)
  apply (deriv.add_const _).congr_deriv
  unfold Response.primedSlope Response.cosCoeff Response.sinCoeff Response.zCoeff
    Response.jointTotal Response.jointCoherence observableSlope observableZ scaledGram
  ring

theorem source_OR_bob_deriv (Q uA uB bgA bgB a0 a1 b0 u : ℝ) :
    HasDerivAt (fun t => sourceORCH p f oA oB Q uA uB bgA bgB a0 a1 b0 t)
      (observableSlope (scaledGram p f oA oB (orScale bgA bgB * (Q * uA * uB)))
        0 0 0 a0 a1 u) u := by
  have eqn : (fun t => sourceORCH p f oA oB Q uA uB bgA bgB a0 a1 b0 t) =
      (fun t => orScale bgA bgB * Response.bobCH p f oA oB 0 Q uA uB 0 0 a0 a1 b0 t +
        sourceOROffset p f oA oB Q uA uB bgA bgB a0 b0) := by
    funext t
    exact source_OR_CH_eq p f oA oB Q uA uB bgA bgB a0 a1 b0 t
  rw [eqn]
  have deriv := (Response.bob_hasDerivAt p f oA oB 0 Q uA uB 0 0 a0 a1 b0 u).const_mul
    (orScale bgA bgB)
  apply (deriv.add_const _).congr_deriv
  unfold Response.primedSlope Response.cosCoeff Response.sinCoeff Response.zCoeff
    Response.jointTotal Response.jointCoherence observableSlope observableZ scaledGram
  ring

def signalPopulationA (Q uA : ℝ) (pol : Bool) : ℝ :=
  Q * uA * (if pol then (omegaA p f oA).2 else (omegaA p f oA).1)

def signalPopulationB (Q uB : ℝ) (pol : Bool) : ℝ :=
  Q * uB * (if pol then (omegaB p f oB).2 else (omegaB p f oB).1)

private theorem detected_loss_le (Q ua ub P S : ℝ) (hQ : 0 ≤ Q) (hua : 0 ≤ ua)
    (hub : ub ≤ 1) (hP : 0 ≤ P) (hPS : P ≤ S) :
    Q * ua * ub * P ≤ Q * ua * S := by
  have scaled : ub * P ≤ P := by simpa using mul_le_mul_of_nonneg_right hub hP
  have bound : ub * P ≤ S := scaled.trans hPS
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left bound (mul_nonneg hQ hua)

/-- Union collection is bounded by the same source's complete four-branch inventory. -/
theorem collected_union_bound :
    Response.aliceTotal p f oA + Response.bobTotal p f oB -
      Response.jointTotal p f oA oB ≤ 1 := by
  have consH := four_branches_conserve f oA oB false
  have consV := four_branches_conserve f oA oB true
  have lostH := power_nonnegative f oA oB false true true
  have lostV := power_nonnegative f oA oB true true true
  have hH : power f oA oB false false false + power f oA oB false false true +
      power f oA oB false true false ≤ 1 := by linarith
  have hV : power f oA oB true false false + power f oA oB true false true +
      power f oA oB true true false ≤ 1 := by linarith
  have weightedH := mul_le_mul_of_nonneg_left hH (sq_nonneg p.c)
  have weightedV := mul_le_mul_of_nonneg_left hV (sq_nonneg p.s)
  unfold Response.aliceTotal Response.bobTotal Response.jointTotal omegaA omegaB omegaAB
  rw [alice_includes_partner_loss f oA oB false, alice_includes_partner_loss f oA oB true,
    bob_includes_partner_loss f oA oB false, bob_includes_partner_loss f oA oB true]
  nlinarith [p.unit]

structure SignalLossAt (Q uA uB : ℝ) : Prop where
  alice_nonnegative : ∀ pol, 0 ≤ signalPopulationA p f oA Q uA pol
  bob_nonnegative : ∀ pol, 0 ≤ signalPopulationB p f oB Q uB pol
  h_in_alice : (scaledGram p f oA oB (Q * uA * uB)).hh ≤ signalPopulationA p f oA Q uA false
  v_in_alice : (scaledGram p f oA oB (Q * uA * uB)).vv ≤ signalPopulationA p f oA Q uA true
  h_in_bob : (scaledGram p f oA oB (Q * uA * uB)).hh ≤ signalPopulationB p f oB Q uB false
  v_in_bob : (scaledGram p f oA oB (Q * uA * uB)).vv ≤ signalPopulationB p f oB Q uB true
  union_le_one :
    (signalPopulationA p f oA Q uA false + signalPopulationB p f oB Q uB false -
      (scaledGram p f oA oB (Q * uA * uB)).hh) +
    (signalPopulationA p f oA Q uA true + signalPopulationB p f oB Q uB true -
      (scaledGram p f oA oB (Q * uA * uB)).vv) ≤ 1

theorem source_signal_loss (Q uA uB : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hA0 : 0 ≤ uA) (hA1 : uA ≤ 1) (hB0 : 0 ≤ uB) (hB1 : uB ≤ 1) :
    SignalLossAt p f oA oB Q uA uB := by
  have native := native_source_cone p f oA oB
  have aLoss := omegaA_generated_loss p f oA oB
  have bLoss := omegaB_generated_loss p f oA oB
  have alH : (omegaAB p f oA oB).hh ≤ (omegaA p f oA).1 := by
    have h := mul_nonneg (sq_nonneg p.c) (power_nonnegative f oA oB false false true)
    linarith [aLoss.1]
  have alV : (omegaAB p f oA oB).vv ≤ (omegaA p f oA).2 := by
    have h := mul_nonneg (sq_nonneg p.s) (power_nonnegative f oA oB true false true)
    linarith [aLoss.2]
  have blH : (omegaAB p f oA oB).hh ≤ (omegaB p f oB).1 := by
    have h := mul_nonneg (sq_nonneg p.c) (power_nonnegative f oA oB false true false)
    linarith [bLoss.1]
  have blV : (omegaAB p f oA oB).vv ≤ (omegaB p f oB).2 := by
    have h := mul_nonneg (sq_nonneg p.s) (power_nonnegative f oA oB true true false)
    linarith [bLoss.2]
  have bounds := Response.source_bounds p f oA oB
  constructor
  · intro pol
    cases pol
    · exact mul_nonneg (mul_nonneg hQ0 hA0) (native.1.trans alH)
    · exact mul_nonneg (mul_nonneg hQ0 hA0) (native.2.1.trans alV)
  · intro pol
    cases pol
    · exact mul_nonneg (mul_nonneg hQ0 hB0) (native.1.trans blH)
    · exact mul_nonneg (mul_nonneg hQ0 hB0) (native.2.1.trans blV)
  · exact detected_loss_le Q uA uB _ _ hQ0 hA0 hB1 native.1 alH
  · exact detected_loss_le Q uA uB _ _ hQ0 hA0 hB1 native.2.1 alV
  · simpa [scaledGram, signalPopulationB, mul_assoc, mul_left_comm, mul_comm] using
      detected_loss_le Q uB uA _ _ hQ0 hB0 hA1 native.1 blH
  · simpa [scaledGram, signalPopulationB, mul_assoc, mul_left_comm, mul_comm] using
      detected_loss_le Q uB uA _ _ hQ0 hB0 hA1 native.2.1 blV
  · have rA := mul_nonneg (sub_nonneg.mpr hA1)
      (sub_nonneg.mpr bounds.joint_le_alice)
    have rB := mul_nonneg (sub_nonneg.mpr hB1)
      (sub_nonneg.mpr bounds.joint_le_bob)
    have rAB := mul_nonneg (mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hB1))
      bounds.joint_nonnegative
    have detector : uA * Response.aliceTotal p f oA + uB * Response.bobTotal p f oB -
        uA * uB * Response.jointTotal p f oA oB ≤
          Response.aliceTotal p f oA + Response.bobTotal p f oB -
            Response.jointTotal p f oA oB := by nlinarith
    have generatedUnion := collected_union_bound p f oA oB
    have scaled := mul_le_mul_of_nonneg_left (detector.trans generatedUnion) hQ0
    have upper : Q * (uA * Response.aliceTotal p f oA + uB * Response.bobTotal p f oB -
        uA * uB * Response.jointTotal p f oA oB) ≤ Q := by simpa using scaled
    calc
      (signalPopulationA p f oA Q uA false + signalPopulationB p f oB Q uB false -
        (scaledGram p f oA oB (Q * uA * uB)).hh) +
        (signalPopulationA p f oA Q uA true + signalPopulationB p f oB Q uB true -
        (scaledGram p f oA oB (Q * uA * uB)).vv) =
          Q * (uA * Response.aliceTotal p f oA + uB * Response.bobTotal p f oB -
            uA * uB * Response.jointTotal p f oA oB) := by
              unfold signalPopulationA signalPopulationB scaledGram Response.aliceTotal
                Response.bobTotal Response.jointTotal
              simp
              ring
      _ ≤ 1 := upper.trans hQ1

end
end P23.Collection.Observable
