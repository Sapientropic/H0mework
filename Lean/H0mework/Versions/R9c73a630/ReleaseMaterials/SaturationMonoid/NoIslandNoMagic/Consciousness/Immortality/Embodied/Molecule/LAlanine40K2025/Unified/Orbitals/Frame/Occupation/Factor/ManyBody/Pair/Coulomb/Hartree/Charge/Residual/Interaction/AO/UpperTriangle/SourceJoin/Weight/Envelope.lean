import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Moment
import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Exponential
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Primitive
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.GenericS

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel SourceExponential
open GaussianPair Laplace.Axis
noncomputable section

def weightFloor (x : ℚ) : ℚ := ⌊weightScale * x⌋ / weightScale
def weightCeil (x : ℚ) : ℚ := ⌈weightScale * x⌉ / weightScale

theorem weightFloor_le (x : ℚ) : weightFloor x ≤ x := by
  unfold weightFloor
  have h : ⌊weightScale * x⌋ ≤ weightScale * x := Int.floor_le _
  calc ⌊weightScale * x⌋ / weightScale ≤ weightScale * x / weightScale :=
        div_le_div_of_nonneg_right h weightScale_pos.le
    _ = x := by rw [mul_comm, mul_div_cancel_right₀ _ weightScale_pos.ne']

theorem le_weightCeil (x : ℚ) : x ≤ weightCeil x := by
  unfold weightCeil
  have h : weightScale * x ≤ ⌈weightScale * x⌉ := Int.le_ceil _
  calc x = weightScale * x / weightScale := by
        rw [mul_comm, mul_div_cancel_right₀ _ weightScale_pos.ne']
    _ ≤ ⌈weightScale * x⌉ / weightScale :=
        div_le_div_of_nonneg_right h weightScale_pos.le

theorem weightFloor_nonneg (x : ℚ) (h : 0 ≤ x) : 0 ≤ weightFloor x := by
  unfold weightFloor
  apply div_nonneg _ weightScale_pos.le
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg weightScale_pos.le h)

theorem weightCeil_nonneg (x : ℚ) (h : 0 ≤ x) : 0 ≤ weightCeil x :=
  h.trans (le_weightCeil x)

def expUp (T : ℚ) : ℚ := (UnifiedOrbitals.negativeExp (weightFloor T) 8).2

theorem expUp_reduction_valid (T : ℚ) (hT : 0 ≤ T) :
    UnifiedOrbitals.ExpReductionValid (weightFloor T) 8 := by
  intro _ lt
  have hfl : 0 ≤ weightFloor T := weightFloor_nonneg T hT
  have hle : weightFloor T ≤ 112 := le_of_lt lt
  have arg : reducedArgument (-weightFloor T) 8 = (-weightFloor T)/256 := by
    unfold reducedArgument
    norm_num
  rw [arg, abs_div, abs_neg, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 256),
    abs_of_nonneg hfl]
  exact (div_le_div_of_nonneg_right hle (by norm_num)).trans (by norm_num)

theorem expUp_spec (T : ℚ) (hT : 0 ≤ T) : Real.exp (-(T:ℝ)) ≤ (expUp T : ℝ) := by
  have holds := UnifiedOrbitals.negative_exp_contains (weightFloor T) 8
    (expUp_reduction_valid T hT)
  have hle : Real.exp (-(T:ℝ)) ≤ Real.exp (-(weightFloor T : ℝ)) :=
    Real.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast weightFloor_le T))
  exact hle.trans holds.2

theorem expUp_pos (T : ℚ) (hT : 0 ≤ T) : 0 < expUp T := by
  have h := (Real.exp_pos (-(T:ℝ))).trans_le (expUp_spec T hT)
  exact_mod_cast h

theorem expUp_nonneg (T : ℚ) (hT : 0 ≤ T) : 0 ≤ expUp T := (expUp_pos T hT).le

def pairRate (a b : Term) : ℚ := a.exponent + b.exponent
def pairMu (a b : Term) : ℚ := a.exponent * b.exponent / pairRate a b
def pairCentre (a b : Term) (axis : Fin 3) : ℚ :=
  (a.exponent * a.centre axis + b.exponent * b.centre axis) / pairRate a b
def pairDistSq (a b : Term) : ℚ :=
  (a.centre 0 - b.centre 0)^2 + (a.centre 1 - b.centre 1)^2 +
    (a.centre 2 - b.centre 2)^2

theorem pairRate_pos (a b : Term) (ha : 0 < a.exponent) (hb : 0 < b.exponent) :
    0 < pairRate a b := add_pos ha hb

theorem pairRate_nonneg (a b : Term) (ha : 0 ≤ a.exponent) (hb : 0 ≤ b.exponent) :
    0 ≤ pairRate a b := add_nonneg ha hb

theorem pairMu_nonneg (a b : Term) (ha : 0 ≤ a.exponent) (hb : 0 ≤ b.exponent) :
    0 ≤ pairMu a b :=
  div_nonneg (mul_nonneg ha hb) (pairRate_nonneg a b ha hb)

theorem pairDistSq_nonneg (a b : Term) : 0 ≤ pairDistSq a b := by
  unfold pairDistSq
  positivity

theorem pairCentre_real (a b : Term) (axis : Fin 3) :
    (pairCentre a b axis : ℝ) = GaussianPair.centre (a.exponent : ℝ) (b.exponent : ℝ)
      (a.centre axis : ℝ) (b.centre axis : ℝ) := by
  unfold pairCentre pairRate GaussianPair.centre
  push_cast
  ring

def pairSTerms (a b : Term) : Prop := sPowers a ∧ sPowers b

instance (a b : Term) : Decidable (pairSTerms a b) := by
  unfold pairSTerms sPowers
  infer_instance

def axisMoment (na nb : ℕ) (dA dB beta : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (na+1), ∑ j ∈ Finset.range (nb+1),
    (Nat.choose na i : ℚ) * dA^(na-i) * (Nat.choose nb j : ℚ) * dB^(nb-j) *
      gaussMoment (i+j) beta

theorem axisMoment_nonneg (na nb : ℕ) (dA dB beta : ℚ)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB) : 0 ≤ axisMoment na nb dA dB beta := by
  unfold axisMoment
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have g := gaussMoment_nonneg (i+j) beta
  positivity

def pairAxisMoment (a b : Term) (axis : Fin 3) : ℚ :=
  axisMoment (a.powers axis) (b.powers axis)
    |pairCentre a b axis - a.centre axis| |pairCentre a b axis - b.centre axis|
    (pairRate a b / 2)

theorem pairAxisMoment_nonneg (a b : Term) (axis : Fin 3) :
    0 ≤ pairAxisMoment a b axis :=
  axisMoment_nonneg _ _ _ _ _ (abs_nonneg _) (abs_nonneg _)

def pairMomentProduct (a b : Term) : ℚ :=
  pairAxisMoment a b 0 * pairAxisMoment a b 1 * pairAxisMoment a b 2

theorem pairMomentProduct_nonneg (a b : Term) : 0 ≤ pairMomentProduct a b := by
  unfold pairMomentProduct
  have h0 := pairAxisMoment_nonneg a b 0
  have h1 := pairAxisMoment_nonneg a b 1
  have h2 := pairAxisMoment_nonneg a b 2
  positivity

def halvedCoefficient (a b : Term) : ℚ :=
  |a.weight * b.weight| * expUp (pairMu a b * pairDistSq a b / 2) *
    pairMomentProduct a b

theorem halvedCoefficient_nonneg (a b : Term)
    (ha : 0 ≤ a.exponent) (hb : 0 ≤ b.exponent) : 0 ≤ halvedCoefficient a b := by
  unfold halvedCoefficient
  have h := expUp_nonneg (pairMu a b * pairDistSq a b / 2)
    (div_nonneg (mul_nonneg (pairMu_nonneg a b ha hb) (pairDistSq_nonneg a b))
      (by norm_num))
  exact mul_nonneg (mul_nonneg (abs_nonneg _) h) (pairMomentProduct_nonneg a b)

def absTerm (t : Term) : Term :=
  ⟨|t.weight|, t.exponent, t.centre, fun _ => 0⟩

theorem absTerm_weight (t : Term) : (absTerm t).weight = |t.weight| := rfl
theorem absTerm_exponent (t : Term) : (absTerm t).exponent = t.exponent := rfl
theorem absTerm_centre (t : Term) : (absTerm t).centre = t.centre := rfl
theorem absTerm_powers (t : Term) : (absTerm t).powers = fun _ => 0 := rfl

def halvedLeft (a b : Term) : Term :=
  ⟨halvedCoefficient a b, a.exponent / 2, a.centre, fun _ => 0⟩

def halvedRight (_a b : Term) : Term :=
  ⟨1, b.exponent / 2, b.centre, fun _ => 0⟩

theorem halvedLeft_weight (a b : Term) :
    (halvedLeft a b).weight = halvedCoefficient a b := rfl
theorem halvedLeft_exponent (a b : Term) :
    (halvedLeft a b).exponent = a.exponent / 2 := rfl
theorem halvedLeft_centre (a b : Term) :
    (halvedLeft a b).centre = a.centre := rfl
theorem halvedLeft_powers (a b : Term) :
    (halvedLeft a b).powers = fun _ => 0 := rfl

theorem halvedRight_weight (a b : Term) : (halvedRight a b).weight = 1 := rfl
theorem halvedRight_exponent (a b : Term) :
    (halvedRight a b).exponent = b.exponent / 2 := rfl
theorem halvedRight_centre (a b : Term) :
    (halvedRight a b).centre = b.centre := rfl
theorem halvedRight_powers (a b : Term) :
    (halvedRight a b).powers = fun _ => 0 := rfl

def pairEnvelope (a b : Term) : Term × Term :=
  if pairSTerms a b then
    (absTerm a, absTerm b)
  else
    (halvedLeft a b, halvedRight a b)

theorem pairEnvelope_sPowers (a b : Term) :
    sPowers (pairEnvelope a b).1 ∧ sPowers (pairEnvelope a b).2 := by
  unfold pairEnvelope
  by_cases h : pairSTerms a b
  · rw [if_pos h]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem pairEnvelope_exponents_positive (a b : Term)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent) :
    0 < (pairEnvelope a b).1.exponent ∧ 0 < (pairEnvelope a b).2.exponent := by
  unfold pairEnvelope
  by_cases h : pairSTerms a b
  · rw [if_pos h]
    exact ⟨ha, hb⟩
  · rw [if_neg h]
    exact ⟨by show 0 < a.exponent/2; linarith,
      by show 0 < b.exponent/2; linarith⟩

def pairKappa (a b : Term) : ℚ :=
  if pairSTerms a b then |a.weight * b.weight| * expUp (pairMu a b * pairDistSq a b)
  else halvedCoefficient a b * expUp (pairMu a b * pairDistSq a b / 2)

theorem pairKappa_nonneg (a b : Term) (ha : 0 ≤ a.exponent) (hb : 0 ≤ b.exponent) :
    0 ≤ pairKappa a b := by
  unfold pairKappa
  split_ifs with h
  · have h' := expUp_nonneg (pairMu a b * pairDistSq a b)
      (mul_nonneg (pairMu_nonneg a b ha hb) (pairDistSq_nonneg a b))
    positivity
  · have h' := expUp_nonneg (pairMu a b * pairDistSq a b / 2)
      (div_nonneg (mul_nonneg (pairMu_nonneg a b ha hb) (pairDistSq_nonneg a b))
        (by norm_num))
    exact mul_nonneg (halvedCoefficient_nonneg a b ha hb) h'

def pairRateM (a b : Term) : ℚ :=
  if pairSTerms a b then pairRate a b else pairRate a b / 2

theorem pairRateM_pos (a b : Term) (ha : 0 < a.exponent) (hb : 0 < b.exponent) :
    0 < pairRateM a b := by
  unfold pairRateM
  split_ifs
  · exact pairRate_pos a b ha hb
  · linarith [pairRate_pos a b ha hb]

theorem pairRateM_ge (a b : Term) (ha : (1/64 : ℚ) ≤ a.exponent)
    (hb : (1/64 : ℚ) ≤ b.exponent) : (1/64 : ℚ) ≤ pairRateM a b := by
  unfold pairRateM pairRate
  split_ifs <;> linarith

theorem pairEnvelope_rate (a b : Term) :
    ((pairEnvelope a b).1.exponent + (pairEnvelope a b).2.exponent : ℚ) =
      pairRateM a b := by
  unfold pairEnvelope pairRateM
  by_cases h : pairSTerms a b
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    show a.exponent / 2 + b.exponent / 2 = (a.exponent + b.exponent) / 2
    ring

def pairPhi (a b : Term) : ℚ :=
  (Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) : ℚ) / 2^32

theorem pairPhi_nonneg (a b : Term) : 0 ≤ pairPhi a b := by
  unfold pairPhi
  positivity

theorem pairPhi_pow_le (a b : Term) (h : 0 < pairRateM a b) :
    pairPhi a b ^ 4 ≤ pairRateM a b := by
  unfold pairPhi
  have hM : (Int.toNat ⌊pairRateM a b * weightScaleSq⌋ : ℚ) ≤
      pairRateM a b * weightScaleSq := by
    have hnn : (0 : ℤ) ≤ ⌊pairRateM a b * weightScaleSq⌋ :=
      Int.floor_nonneg.mpr
        (mul_nonneg h.le (by unfold weightScaleSq; norm_num))
    have e : (Int.toNat ⌊pairRateM a b * weightScaleSq⌋ : ℤ) =
        ⌊pairRateM a b * weightScaleSq⌋ := Int.toNat_of_nonneg hnn
    calc (Int.toNat ⌊pairRateM a b * weightScaleSq⌋ : ℚ)
        = (⌊pairRateM a b * weightScaleSq⌋ : ℚ) := by
          exact_mod_cast e
      _ ≤ pairRateM a b * weightScaleSq := Int.floor_le _
  have sqsq : (Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) : ℚ)^4 ≤
      pairRateM a b * weightScaleSq := by
    have step1 : Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) *
        Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) ≤
        Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋) := Nat.sqrt_le _
    have step2 : Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋) *
        Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋) ≤
        Int.toNat ⌊pairRateM a b * weightScaleSq⌋ := Nat.sqrt_le _
    have chain : (Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)))^4 ≤
        Int.toNat ⌊pairRateM a b * weightScaleSq⌋ := by
      calc (Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)))^4
          = (Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) *
              Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)))^2 := by
            ring
        _ ≤ (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋) *
              Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) :=
            pow_le_pow_left₀ (Nat.zero_le _) step1 _ |>.trans_eq (pow_two _)
        _ ≤ Int.toNat ⌊pairRateM a b * weightScaleSq⌋ := step2
    exact_mod_cast (le_trans (by exact_mod_cast chain : (Nat.sqrt (Nat.sqrt
        (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) : ℚ)^4 ≤
        Int.toNat ⌊pairRateM a b * weightScaleSq⌋) hM)
  have scale : (2^32 : ℚ)^4 = weightScaleSq := by unfold weightScaleSq; norm_num
  calc ((Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) : ℚ) / 2^32)^4
      = (Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) : ℚ)^4 /
        weightScaleSq := by rw [div_pow, scale]
    _ ≤ pairRateM a b * weightScaleSq / weightScaleSq :=
        div_le_div_of_nonneg_right sqsq
          (by unfold weightScaleSq; norm_num)
    _ = pairRateM a b :=
        mul_div_cancel_right₀ _
          (by unfold weightScaleSq; norm_num : (weightScaleSq : ℚ) ≠ 0)

theorem pairPhi_pos (a b : Term) (hrate : (1/64 : ℚ) ≤ pairRateM a b) :
    0 < pairPhi a b := by
  unfold pairPhi
  apply div_pos _ (by norm_num)
  have hM : (2^122 : ℤ) ≤ ⌊pairRateM a b * weightScaleSq⌋ := by
    apply Int.le_floor.mpr
    have h : (2^122 : ℚ) ≤ pairRateM a b * weightScaleSq := by
      calc (2^122 : ℚ) = (1/64) * 2^128 := by norm_num
        _ ≤ pairRateM a b * 2^128 :=
            mul_le_mul_of_nonneg_right hrate (by norm_num)
    have e : ((2^122 : ℤ) : ℚ) = (2^122 : ℚ) := by norm_num
    rw [e]
    exact h
  have hN : (2^122 : ℕ) ≤ Int.toNat ⌊pairRateM a b * weightScaleSq⌋ := by
    have e : (Int.toNat (2^122 : ℤ)) = 2^122 := by decide
    have := Int.toNat_le_toNat hM
    rwa [e] at this
  have s1 : (2^61 : ℕ) ≤ Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋) := by
    rw [Nat.le_sqrt]
    calc (2^61 : ℕ) * 2^61 = 2^122 := by norm_num
      _ ≤ Int.toNat ⌊pairRateM a b * weightScaleSq⌋ := hN
  have s2 : (2^30 : ℕ) ≤
      Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) := by
    rw [Nat.le_sqrt]
    calc (2^30 : ℕ) * 2^30 = 2^60 := by norm_num
      _ ≤ 2^61 := by norm_num
      _ ≤ Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋) := s1
  have : (0 : ℚ) < Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) := by
    have h : (0 : ℕ) < Nat.sqrt (Nat.sqrt (Int.toNat ⌊pairRateM a b * weightScaleSq⌋)) :=
      lt_of_lt_of_le (by norm_num : (0:ℕ) < 2^30) s2
    exact_mod_cast h
  exact this

def pairC0 : ℚ := 498/100

theorem pairC0_pos : (0 : ℚ) < pairC0 := by unfold pairC0; norm_num

def pairTau (a b : Term) : ℚ :=
  weightCeil (pairC0 * pairKappa a b / (pairRateM a b * pairPhi a b))

theorem pairTau_nonneg (a b : Term) (ha : 0 ≤ a.exponent) (hb : 0 ≤ b.exponent)
    (hrate : 0 < pairRateM a b) (hphi : 0 < pairPhi a b) : 0 ≤ pairTau a b := by
  unfold pairTau
  apply weightCeil_nonneg
  apply div_nonneg (mul_nonneg pairC0_pos.le (pairKappa_nonneg a b ha hb))
    (mul_nonneg hrate.le hphi.le)

theorem pairTau_ge (a b : Term) (_hrate : 0 < pairRateM a b) (_hphi : 0 < pairPhi a b) :
    (pairC0 * pairKappa a b : ℝ) / (pairRateM a b * pairPhi a b) ≤ (pairTau a b : ℝ) := by
  have h := le_weightCeil (pairC0 * pairKappa a b / (pairRateM a b * pairPhi a b))
  have hR : ((pairC0 * pairKappa a b / (pairRateM a b * pairPhi a b) : ℚ) : ℝ) ≤
      (pairTau a b : ℝ) := by
    unfold pairTau
    exact_mod_cast h
  calc (pairC0 * pairKappa a b : ℝ) / (pairRateM a b * pairPhi a b)
      = ((pairC0 * pairKappa a b / (pairRateM a b * pairPhi a b) : ℚ) : ℝ) := by
        rw [Rat.cast_div, Rat.cast_mul, Rat.cast_mul]
    _ ≤ (pairTau a b : ℝ) := hR

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
