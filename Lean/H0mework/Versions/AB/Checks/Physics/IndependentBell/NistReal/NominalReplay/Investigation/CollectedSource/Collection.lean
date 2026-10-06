import Mathlib.Tactic

/-!
Finite real optical subfamily of cs-r0001. The primitive data are two normalized source
mode amplitudes and local transmission/loss columns. All collection powers are generated.
Complex spectral phase and general complex effects are handled by the two Python paths;
this file proves the real finite-mode mechanism, not a NIST source occurrence.
-/

set_option autoImplicit false

namespace P23.Collection

open scoped BigOperators
noncomputable section

structure Preparation where
  c : ℝ
  s : ℝ
  unit : c ^ 2 + s ^ 2 = 1

structure Source (A B : Type*) [Fintype A] [Fintype B] where
  f : Bool → A → B → ℝ
  normalized : ∀ p, ∑ i, ∑ j, f p i j ^ 2 = 1

structure Optic (I : Type*) where
  t : Bool → I → ℝ
  l : Bool → I → ℝ
  unit : ∀ p i, t p i ^ 2 + l p i ^ 2 = 1

variable {A B : Type*} [Fintype A] [Fintype B]

def port {I : Type*} (o : Optic I) (lost p : Bool) (i : I) : ℝ :=
  if lost then o.l p i else o.t p i

def branch (f : Source A B) (a : Optic A) (b : Optic B)
    (p x y : Bool) (i : A) (j : B) : ℝ :=
  f.f p i j * port a x p i * port b y p j

def power (f : Source A B) (a : Optic A) (b : Optic B) (p x y : Bool) : ℝ :=
  ∑ i, ∑ j, branch f a b p x y i j ^ 2

def singleA (f : Source A B) (a : Optic A) (p : Bool) : ℝ :=
  ∑ i, ∑ j, (f.f p i j * a.t p i) ^ 2

def singleB (f : Source A B) (b : Optic B) (p : Bool) : ℝ :=
  ∑ i, ∑ j, (f.f p i j * b.t p j) ^ 2

theorem power_nonnegative (f : Source A B) (a : Optic A) (b : Optic B)
    (p x y : Bool) : 0 ≤ power f a b p x y := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem alice_partition (f : Source A B) (a : Optic A) (b : Optic B) (p x : Bool) :
    power f a b p x false + power f a b p x true =
      ∑ i, ∑ j, (f.f p i j * port a x p i) ^ 2 := by
  simp only [power, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [branch, port]
  linear_combination (f.f p i j * (if x then a.l p i else a.t p i)) ^ 2 * b.unit p j

theorem bob_partition (f : Source A B) (a : Optic A) (b : Optic B) (p y : Bool) :
    power f a b p false y + power f a b p true y =
      ∑ i, ∑ j, (f.f p i j * port b y p j) ^ 2 := by
  simp only [power, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [branch, port]
  linear_combination (f.f p i j * (if y then b.l p j else b.t p j)) ^ 2 * a.unit p i

theorem alice_includes_partner_loss (f : Source A B) (a : Optic A) (b : Optic B) (p : Bool) :
    singleA f a p = power f a b p false false + power f a b p false true := by
  simpa [singleA, port] using (alice_partition f a b p false).symm

theorem bob_includes_partner_loss (f : Source A B) (a : Optic A) (b : Optic B) (p : Bool) :
    singleB f b p = power f a b p false false + power f a b p true false := by
  simpa [singleB, port] using (bob_partition f a b p false).symm

theorem four_branches_conserve (f : Source A B) (a : Optic A) (b : Optic B) (p : Bool) :
    (power f a b p false false + power f a b p false true) +
      (power f a b p true false + power f a b p true true) = 1 := by
  rw [alice_partition, alice_partition, ← f.normalized p]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [port]
  linear_combination f.f p i j ^ 2 * a.unit p i

/-- Supported HH/VV block of the real non-normalized joint object. -/
structure JointObject where
  hh : ℝ
  vv : ℝ
  hv : ℝ

def overlap (f : Source A B) (a : Optic A) (b : Optic B) : ℝ :=
  ∑ i, ∑ j, branch f a b false false false i j * branch f a b true false false i j

def omegaAB (p : Preparation) (f : Source A B) (a : Optic A) (b : Optic B) : JointObject :=
  ⟨p.c ^ 2 * power f a b false false false,
   p.s ^ 2 * power f a b true false false, p.c * p.s * overlap f a b⟩

def omegaA (p : Preparation) (f : Source A B) (a : Optic A) : ℝ × ℝ :=
  (p.c ^ 2 * singleA f a false, p.s ^ 2 * singleA f a true)

def omegaB (p : Preparation) (f : Source A B) (b : Optic B) : ℝ × ℝ :=
  (p.c ^ 2 * singleB f b false, p.s ^ 2 * singleB f b true)

def jointRead (o : JointObject) (x y : ℝ) : ℝ := o.hh*x^2 + o.vv*y^2 + 2*o.hv*x*y

theorem joint_read_from_source (p : Preparation) (f : Source A B) (a : Optic A) (b : Optic B)
    (x y : ℝ) :
    jointRead (omegaAB p f a b) x y =
      ∑ i, ∑ j, (p.c * branch f a b false false false i j * x +
        p.s * branch f a b true false false i j * y) ^ 2 := by
  dsimp [jointRead, omegaAB, overlap, power]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem joint_positive (p : Preparation) (f : Source A B) (a : Optic A) (b : Optic B)
    (x y : ℝ) : 0 ≤ jointRead (omegaAB p f a b) x y := by
  rw [joint_read_from_source]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem omegaA_generated_loss (p : Preparation) (f : Source A B) (a : Optic A) (b : Optic B) :
    (omegaA p f a).1 - (omegaAB p f a b).hh = p.c ^ 2 * power f a b false false true ∧
    (omegaA p f a).2 - (omegaAB p f a b).vv = p.s ^ 2 * power f a b true false true := by
  dsimp [omegaA, omegaAB]
  rw [alice_includes_partner_loss f a b false, alice_includes_partner_loss f a b true]
  constructor <;> ring

theorem omegaB_generated_loss (p : Preparation) (f : Source A B) (a : Optic A) (b : Optic B) :
    (omegaB p f b).1 - (omegaAB p f a b).hh = p.c ^ 2 * power f a b false true false ∧
    (omegaB p f b).2 - (omegaAB p f a b).vv = p.s ^ 2 * power f a b true true false := by
  dsimp [omegaB, omegaAB]
  rw [bob_includes_partner_loss f a b false, bob_includes_partner_loss f a b true]
  constructor <;> ring

/-- The source ratio maps to collected populations; purity additionally needs saturated overlap. -/
theorem collected_ratio_squared (p : Preparation) (f : Source A B) (a : Optic A) (b : Optic B)
    (r : ℝ) (hr : p.s = r*p.c) :
    (omegaAB p f a b).vv * power f a b false false false =
      r^2 * (omegaAB p f a b).hh * power f a b true false false := by
  dsimp [omegaAB]
  rw [hr]
  ring

def population (c s h v : ℝ) : ℝ := c^2*h+s^2*v

/-- Cross multiplication exposes the missing branch-resolved calibration without division. -/
theorem proportional_marginal_residual (c s ah av ch cv : ℝ) :
    c^2*ah*population c s ch cv - c^2*ch*population c s ah av =
      c^2*s^2*(ah*cv-av*ch) := by
  unfold population
  ring

def etaA (pb pp ua : ℝ) : ℝ := ua*pp/pb
def etaB (pa pp ub : ℝ) : ℝ := ub*pp/pa
def effectiveQ (q pa pb pp : ℝ) : ℝ := q*pa*pb/pp

theorem effective_rates (q pa pb pp ua ub : ℝ) (ha : pa ≠ 0) (hb : pb ≠ 0) (hp : pp ≠ 0) :
    effectiveQ q pa pb pp * etaA pb pp ua = q*pa*ua ∧
    effectiveQ q pa pb pp * etaB pa pp ub = q*pb*ub ∧
    effectiveQ q pa pb pp * etaA pb pp ua * etaB pa pp ub = q*pp*ua*ub := by
  dsimp [effectiveQ, etaA, etaB]
  constructor
  · field_simp
  constructor <;> field_simp

/-- Uniqueness is a rate identity, with actual nonzero joint count as its only division guard. -/
theorem effectiveQ_unique (q ea eb sa sb j : ℝ)
    (ha : sa = q*ea) (hb : sb = q*eb) (hj : j = q*ea*eb) (hn : j ≠ 0) :
    q = sa*sb/j := by
  apply (eq_div_iff hn).2
  rw [ha, hb, hj]
  ring

def collectBin0 : Optic (Fin 2) where
  t _ i := if i = 0 then 1 else 0
  l _ i := if i = 0 then 0 else 1
  unit _ i := by by_cases h : i = 0 <;> simp [h]

def sourceI : Source (Fin 2) (Fin 2) where
  f _ _ _ := 1/2
  normalized _ := by norm_num [Fin.sum_univ_two]

def binPower (p : Bool) (i j : Fin 2) : ℝ :=
  if i = 0 then (if j = 0 then 1/4 else if p then 1/10 else 2/5)
  else (if j = 0 then (if p then 2/5 else 1/10) else 1/4)

def sourceII : Source (Fin 2) (Fin 2) where
  f p i j := Real.sqrt (binPower p i j)
  normalized p := by cases p <;> norm_num [binPower, Fin.sum_univ_two, Real.sq_sqrt, div_pow]

theorem calibrationI_powers :
    singleA sourceI collectBin0 false = 1/2 ∧ singleA sourceI collectBin0 true = 1/2 ∧
    singleB sourceI collectBin0 false = 1/2 ∧ singleB sourceI collectBin0 true = 1/2 := by
  norm_num [singleA, singleB, sourceI, collectBin0, Fin.sum_univ_two]

theorem calibrationII_powers :
    singleA sourceII collectBin0 false = 13/20 ∧ singleA sourceII collectBin0 true = 7/20 ∧
    singleB sourceII collectBin0 false = 7/20 ∧ singleB sourceII collectBin0 true = 13/20 := by
  norm_num [singleA, singleB, sourceII, binPower, collectBin0, Fin.sum_univ_two, Real.sq_sqrt, div_pow]

theorem same_collected_joint (p : Preparation) :
    omegaAB p sourceI collectBin0 collectBin0 = omegaAB p sourceII collectBin0 collectBin0 := by
  norm_num [omegaAB, power, overlap, branch, port, sourceI, sourceII, binPower,
    collectBin0, Fin.sum_univ_two, Real.sqrt_div, Real.sqrt_one]

/-- Same complete joint family, while the missing loss branch is strictly nonzero. -/
theorem strict_missing_single (p : Preparation) (hc : p.c ≠ 0) :
    (omegaAB p sourceII collectBin0 collectBin0).hh < (omegaA p sourceII collectBin0).1 := by
  have hpos : 0 < p.c ^ 2 := sq_pos_of_ne_zero hc
  norm_num [omegaAB, omegaA, power, singleA, branch, port, sourceII, binPower,
    collectBin0, Fin.sum_univ_two, Real.sq_sqrt, div_pow] at *
  nlinarith

end
end P23.Collection
