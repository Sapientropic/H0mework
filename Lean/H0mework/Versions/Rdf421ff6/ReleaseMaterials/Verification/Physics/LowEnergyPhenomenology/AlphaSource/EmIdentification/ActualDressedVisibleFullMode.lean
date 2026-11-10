import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualDressedVisiblePoleOwn.ActualDressedRationalVisiblePole
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualDressedPoleWardMode
open Polynomial ActualDressedVisiblePole
open scoped Matrix BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def sourceVanishingOrders (V : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ) : Finset ℕ :=
  Finset.univ.image (fun i => if V i = 0 then D.rootMultiplicity a else (V i).rootMultiplicity a)

theorem source_vanishing_orders_nonempty (V : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ) :
    (sourceVanishingOrders V D a).Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty

/-- The order is generated from every full source coordinate, including coordinates with zero numerator. -/
def sourceCancellationOrder (V : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ) : ℕ :=
  (sourceVanishingOrders V D a).min' (source_vanishing_orders_nonempty V D a)

def sourcePoleMode (V : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ) : ι → ℂ :=
  fun i => (V i /ₘ (X-C a)^sourceCancellationOrder V D a).eval a

private theorem cancellation_le (V : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ) (i : ι) :
    sourceCancellationOrder V D a ≤ if V i=0 then D.rootMultiplicity a else (V i).rootMultiplicity a := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

private theorem power_divides_coordinate (V : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ) (i : ι) :
    (X-C a)^sourceCancellationOrder V D a ∣ V i := by
  by_cases zero : V i=0
  · rw [zero]; exact dvd_zero _
  · have bound := cancellation_le V D a i
    rw [if_neg zero] at bound
    exact (le_rootMultiplicity_iff zero).mp bound

private theorem power_division (P : ℂ[X]) (a : ℂ) (k : ℕ) (divides : (X-C a)^k ∣ P) :
    (X-C a)^k*(P /ₘ (X-C a)^k)=P := by
  have monic := (monic_X_sub_C a).pow k
  have equation := modByMonic_add_div P ((X-C a)^k)
  rw [(modByMonic_eq_zero_iff_dvd monic).mpr divides, zero_add] at equation
  exact equation

private theorem visible_numerator_not_divisible (N D : ℂ[X]) (a : ℂ)
    (root : a ∈ visibleRoots (readFraction N D)) :
    ¬(X-C a)^D.rootMultiplicity a ∣ N := by
  have dnonzero : D ≠ 0 := by
    intro zero
    simp [zero, readFraction, visibleRoots] at root
  intro divides
  obtain ⟨L, hL⟩ := divides
  let R := readFraction N D
  have equation : R.num*D=N*R.denom := reduced_cross_identity N D dnonzero
  have cancelled : R.num*(D /ₘ (X-C a)^D.rootMultiplicity a)=L*R.denom := by
    apply mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero a))
    calc
      _=R.num*((X-C a)^D.rootMultiplicity a*(D /ₘ (X-C a)^D.rootMultiplicity a)) := by ring
      _=R.num*D := by rw [pow_mul_divByMonic_rootMultiplicity_eq]
      _=N*R.denom := equation
      _=((X-C a)^D.rootMultiplicity a*L)*R.denom := by rw [hL]
      _=_ := by ring
  have value := congrArg (Polynomial.eval a) cancelled
  rw [eval_mul, eval_mul, (visible_root_iff R a).mp root, mul_zero] at value
  exact mul_ne_zero (visible_numerator_nonzero R a root)
    (eval_divByMonic_pow_rootMultiplicity_ne_zero a dnonzero) value

/-- A canonical observer-visible pole forces an uncancelled full numerator coordinate. -/
theorem source_cancellation_order_lt (V : ι → ℂ[X]) (D : ℂ[X]) (fd : ι → ℂ) (a : ℂ)
    (root : a ∈ visibleRoots (readFraction (dotProduct (fun i => C (fd i)) V) D)) :
    sourceCancellationOrder V D a < D.rootMultiplicity a := by
  by_contra lower
  have bound := Nat.le_of_not_lt lower
  apply visible_numerator_not_divisible _ D a root
  unfold dotProduct
  apply Finset.dvd_sum
  intro i _
  exact dvd_mul_of_dvd_right ((pow_dvd_pow (X-C a) bound).trans
    (power_divides_coordinate V D a i)) _

theorem source_pole_mode_nonzero (V : ι → ℂ[X]) (D : ℂ[X]) (fd : ι → ℂ) (a : ℂ)
    (root : a ∈ visibleRoots (readFraction (dotProduct (fun i => C (fd i)) V) D)) :
    sourcePoleMode V D a ≠ 0 := by
  have lower := source_cancellation_order_lt V D fd a root
  have inside := Finset.min'_mem (sourceVanishingOrders V D a) (source_vanishing_orders_nonempty V D a)
  obtain ⟨i, _, attained⟩ := Finset.mem_image.mp inside
  have nonzero : V i ≠ 0 := by
    intro zero
    simp only [zero] at attained
    change D.rootMultiplicity a=sourceCancellationOrder V D a at attained
    omega
  rw [if_neg nonzero] at attained
  change (V i).rootMultiplicity a=sourceCancellationOrder V D a at attained
  intro zero
  have value := congrFun zero i
  change (V i /ₘ (X-C a)^sourceCancellationOrder V D a).eval a=0 at value
  rw [← attained] at value
  exact eval_divByMonic_pow_rootMultiplicity_ne_zero a nonzero value

private theorem denominator_quotient_root (D : ℂ[X]) (a : ℂ) (k : ℕ)
    (lower : k < D.rootMultiplicity a) : (D /ₘ (X-C a)^k).eval a=0 := by
  have divides : (X-C a)^(k+1) ∣ D :=
    (pow_dvd_pow (X-C a) (Nat.succ_le_of_lt lower)).trans (pow_rootMultiplicity_dvd D a)
  obtain ⟨L, hL⟩ := divides
  have first := power_division D a k
    ((pow_dvd_pow (X-C a) lower.le).trans (pow_rootMultiplicity_dvd D a))
  have quotient : D /ₘ (X-C a)^k=(X-C a)*L := by
    apply mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero a))
    rw [first, hL, pow_succ, mul_assoc]
  rw [quotient, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]

/-- The source vector, after its generated local common-factor removal, solves the full homogeneous polynomial pencil. -/
theorem source_visible_full_kernel (H : Matrix ι ι ℂ[X]) (V F : ι → ℂ[X]) (D : ℂ[X])
    (fd : ι → ℂ) (a : ℂ) (equation : H*ᵥV=D • F)
    (root : a ∈ visibleRoots (readFraction (dotProduct (fun i => C (fd i)) V) D)) :
    H.map (Polynomial.eval a)*ᵥsourcePoleMode V D a=0 := by
  let k := sourceCancellationOrder V D a
  let P : ℂ[X] := (X-C a)^k
  let W : ι → ℂ[X] := fun i => V i /ₘ P
  have pnonzero : P ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero a)
  have coordinate (i : ι) : P*W i=V i := power_division _ a k (power_divides_coordinate V D a i)
  have lower := source_cancellation_order_lt V D fd a root
  have ddivide : P*(D /ₘ P)=D := power_division D a k
    ((pow_dvd_pow (X-C a) lower.le).trans (pow_rootMultiplicity_dvd D a))
  have paid : H*ᵥW=(D /ₘ P) • F := by
    have replacement : V=P • W := by funext i;exact (coordinate i).symm
    rw [replacement, Matrix.mulVec_smul] at equation
    funext i
    change (H*ᵥW) i=(D /ₘ P)*F i
    apply mul_left_cancel₀ pnonzero
    calc
      _=D*F i := congrFun equation i
      _=(P*(D /ₘ P))*F i := congrArg (fun x : ℂ[X] => x*F i) ddivide.symm
      _=P*((D /ₘ P)*F i) := mul_assoc _ _ _
  funext i
  have evaluated := congrArg (Polynomial.eval a) (congrFun paid i)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at evaluated
  rw [eval_finsetSum] at evaluated
  simp only [eval_mul] at evaluated
  simpa only [sourcePoleMode, k, P, W, Matrix.mulVec, dotProduct, Matrix.map_apply,
    denominator_quotient_root D a k lower, zero_mul, Pi.zero_apply] using evaluated

end LowEnergy.ActualDressedPoleWardMode
