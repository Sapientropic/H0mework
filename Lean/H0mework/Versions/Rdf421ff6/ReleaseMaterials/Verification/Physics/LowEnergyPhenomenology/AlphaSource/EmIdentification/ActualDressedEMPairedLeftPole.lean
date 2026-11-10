import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMOriginalLeftClockChain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMPolePairEnergy
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedEMTensorClock ActualDressedOrderedStatic
open ActualDressedZeroClockFrequency ActualDressedZeroClockVector ActualDressedEMZeroClockColumns
open ActualDressedEMClockDispersion ActualDressedEMQuantumThreshold ActualEMCarrierOwn
open ActualDressedEMFullPoleFlux PreparationVacuumPhysicalPoleSheet
open LowEnergy.ActualDressedPoleWardMode LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] zeroClockPencil zeroClockEMRow zeroClockFrequencyDenominator
  sourceLeftClockChain emInsertion correctedPhysicalClock zeroClockClearing emColumnDenominatorTail

def emLeftCancellationOrder (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) : ℕ :=
  sourceCancellationOrder (zeroClockEMRow event eps n mu) (zeroClockFrequencyDenominator event eps n) a

def emFullRowPoleOrder (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) : ℕ :=
  (zeroClockFrequencyDenominator event eps n).rootMultiplicity a-emLeftCancellationOrder event eps n mu a

def emCancelledLeftRow (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) : Fin 289→ℂ[X] :=
  fun i => zeroClockEMRow event eps n mu i /ₘ (X-C a)^emLeftCancellationOrder event eps n mu a

def emCancelledLeftClockChain (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) : Fin 289→ℂ[X] :=
  fun i => sourceLeftClockChain event eps n mu i /ₘ (X-C a)^emLeftCancellationOrder event eps n mu a

def actualEMZeroClockLeftMode (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) : Fin 289→ℂ :=
  sourcePoleMode (zeroClockEMRow event eps n mu) (zeroClockFrequencyDenominator event eps n) a

def emPhysicalPairedLeftMode (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) : Fin 289→ℂ :=
  ((eps^2 : ℂ)^emFullRowPoleOrder event eps n mu a) •
    (fun i => actualEMZeroClockLeftMode event eps n mu a i/(emColumnDenominatorTail event eps n a).eval a)

/-- The defect is read from original cross-clock coefficients after the same full-row pole factor is removed. -/
def emPhysicalPairedLeftDefect (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) : Fin 289→ℂ :=
  fun i => (eps^2 : ℂ)^emFullRowPoleOrder event eps n mu a*
    (emCancelledLeftClockChain event eps n mu a i).eval a/
      ((emColumnDenominatorTail event eps n a).eval a*(zeroClockClearing event eps n).eval a)

attribute [local irreducible] emLeftCancellationOrder emCancelledLeftRow emCancelledLeftClockChain
  emPhysicalPairedLeftMode emPhysicalPairedLeftDefect emFullRowPoleOrder

private theorem left_root (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    a∈visibleRoots (readFraction (dotProduct (fun i => C (emInsertion i nu)) (zeroClockEMRow event eps n mu))
      (zeroClockFrequencyDenominator event eps n)) := by
  rw [actual_zero_clock_em_row_observer]
  exact root

theorem source_em_left_mode_nonzero (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    actualEMZeroClockLeftMode event eps n mu a≠0 :=
  source_pole_mode_nonzero _ _ _ _ (left_root event eps n mu nu a root)

theorem source_em_left_pole_order_positive (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    0<emFullRowPoleOrder event eps n mu a := by
  unfold emFullRowPoleOrder emLeftCancellationOrder
  exact Nat.sub_pos_iff_lt.mpr (source_cancellation_order_lt _ _ _ _ (left_root event eps n mu nu a root))

private theorem coordinate_factor {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : ι→ℂ[X]) (D : ℂ[X]) (a : ℂ) (i : ι) : (X-C a)^sourceCancellationOrder V D a∣V i := by
  by_cases zero : V i=0
  · rw [zero];exact dvd_zero _
  · have bound : sourceCancellationOrder V D a ≤ if V i=0 then D.rootMultiplicity a else (V i).rootMultiplicity a :=
      Finset.min'_le (sourceVanishingOrders V D a) _
        (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    rw [if_neg zero] at bound
    exact (le_rootMultiplicity_iff zero).mp bound

private theorem power_division (P : ℂ[X]) (a : ℂ) (k : ℕ) (factor : (X-C a)^k∣P) :
    (X-C a)^k*(P /ₘ (X-C a)^k)=P := by
  have equation := modByMonic_add_div P ((X-C a)^k)
  rw [(modByMonic_eq_zero_iff_dvd ((monic_X_sub_C a).pow k)).mpr factor,zero_add] at equation
  exact equation

private theorem cancel_left_chain {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ[X]) (V B E : ι→ℂ[X]) (D d : ℂ[X]) (a : ℂ) (k : ℕ)
    (hV : ∀i,(X-C a)^k∣V i) (hD : (X-C a)^k∣D)
    (equation : H.transpose*ᵥV+B=D • (d • E)) :
    H.transpose*ᵥ(fun i => V i /ₘ (X-C a)^k)+(fun i => B i /ₘ (X-C a)^k)=
      (D /ₘ (X-C a)^k) • (d • E) := by
  let P : ℂ[X] := (X-C a)^k
  have pNonzero : P≠0 := pow_ne_zero _ (X_sub_C_ne_zero a)
  have hB (i : ι) : P∣B i := by
    have left : P∣(H.transpose*ᵥV) i := by
      apply Finset.dvd_sum
      intro j _
      exact dvd_mul_of_dvd_right (hV j) _
    have right : P∣D*(d*E i) := dvd_mul_of_dvd_left hD _
    have coordinate := congrFun equation i
    change (H.transpose*ᵥV) i+B i=D*(d*E i) at coordinate
    have same : B i=D*(d*E i)-(H.transpose*ᵥV) i := by linear_combination coordinate
    rw [same]
    exact dvd_sub right left
  have vFactor : V=P • (fun i => V i /ₘ P) := by
    funext i
    exact (power_division _ a k (hV i)).symm
  have bFactor : B=P • (fun i => B i /ₘ P) := by
    funext i
    exact (power_division _ a k (hB i)).symm
  have dFactor : D=P*(D /ₘ P) := (power_division _ a k hD).symm
  rw [vFactor,bFactor,dFactor,Matrix.mulVec_smul] at equation
  funext i
  apply mul_left_cancel₀ pNonzero
  have paid := congrFun equation i
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,mul_assoc,P] using paid

/-- The source clock defect is cancelled with the actual left row, retaining the complete original balance. -/
theorem actual_em_cancelled_left_equation (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    (zeroClockPencil event eps n).transpose*ᵥemCancelledLeftRow event eps n mu a+
      emCancelledLeftClockChain event eps n mu a=
      (zeroClockFrequencyDenominator event eps n /ₘ (X-C a)^emLeftCancellationOrder event eps n mu a) •
        (zeroClockClearing event eps n • fun i => C (emInsertion i mu)) := by
  have lower := (source_cancellation_order_lt _ _ _ _ (left_root event eps n mu nu a root)).le
  have hV : ∀i,(X-C a)^emLeftCancellationOrder event eps n mu a∣zeroClockEMRow event eps n mu i := by
    simpa only [emLeftCancellationOrder] using coordinate_factor (zeroClockEMRow event eps n mu)
      (zeroClockFrequencyDenominator event eps n) a
  have hD : (X-C a)^emLeftCancellationOrder event eps n mu a∣zeroClockFrequencyDenominator event eps n := by
    simpa only [emLeftCancellationOrder] using
      ((pow_dvd_pow (X-C a) lower).trans (pow_rootMultiplicity_dvd (zeroClockFrequencyDenominator event eps n) a))
  have source := cancel_left_chain (zeroClockPencil event eps n) (zeroClockEMRow event eps n mu)
    (sourceLeftClockChain event eps n mu) (fun i => C (emInsertion i mu))
    (zeroClockFrequencyDenominator event eps n) (zeroClockClearing event eps n) a
    (emLeftCancellationOrder event eps n mu a) hV hD (actual_zero_clock_em_left_chain event eps n mu)
  funext i
  simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,emCancelledLeftRow,emCancelledLeftClockChain,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun source i

private theorem denominator_after_cancellation (D : ℂ[X]) (a : ℂ) (k : ℕ) (lower : k≤D.rootMultiplicity a) :
    D /ₘ (X-C a)^k=(X-C a)^(D.rootMultiplicity a-k)*(D /ₘ (X-C a)^D.rootMultiplicity a) := by
  apply mul_left_cancel₀ (pow_ne_zero k (X_sub_C_ne_zero a))
  rw [power_division D a k ((pow_dvd_pow (X-C a) lower).trans (pow_rootMultiplicity_dvd D a)),
    ←mul_assoc,←pow_add,Nat.add_sub_of_le lower,pow_mul_divByMonic_rootMultiplicity_eq]

/-- The actual nonzero left mode has a source-generated kernel defect; no left-kernel target is a premise. -/
theorem actual_em_left_mode_source_defect (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    ((zeroClockPencil event eps n).map (eval a)).transpose*ᵥactualEMZeroClockLeftMode event eps n mu a=
      -(fun i => (emCancelledLeftClockChain event eps n mu a i).eval a) := by
  have equation := congrArg (fun v : Fin 289→ℂ[X] => fun i => (v i).eval a)
    (actual_em_cancelled_left_equation event eps n mu nu a root)
  have lower := source_cancellation_order_lt _ _ _ _ (left_root event eps n mu nu a root)
  have zero : (zeroClockFrequencyDenominator event eps n /ₘ (X-C a)^emLeftCancellationOrder event eps n mu a).eval a=0 := by
    rw [emLeftCancellationOrder]
    rw [denominator_after_cancellation _ a _ lower.le,eval_mul,eval_pow,eval_sub,eval_X,eval_C,sub_self,
      zero_pow (Nat.sub_pos_iff_lt.mpr lower).ne',zero_mul]
  funext i
  have paid := congrFun equation i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
    eval_add,eval_finsetSum,eval_mul,zero,zero_mul] at paid
  change (∑j,(zeroClockPencil event eps n j i).eval a*actualEMZeroClockLeftMode event eps n mu a j)=
    -(emCancelledLeftClockChain event eps n mu a i).eval a
  simpa only [actualEMZeroClockLeftMode,sourcePoleMode,emCancelledLeftRow,emLeftCancellationOrder] using
    (eq_neg_iff_add_eq_zero.mpr paid)

private theorem scaled_left_quotient {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v B : ι→ℂ) (alpha T d : ℂ)
    (source : H.transpose*ᵥv= -B) :
    Matrix.transpose (fun i j => H i j/d)*ᵥ(alpha • fun i => v i/T)=
      -(fun i => alpha*B i/(T*d)) := by
  have factor : Matrix.transpose (fun i j => H i j/d)*ᵥ(alpha • fun i => v i/T)=
      (alpha/(T*d)) • (H.transpose*ᵥv) := by
    funext i
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [factor,source]
  funext i
  simp only [Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
  ring

/-- This physical paired-left restriction retains its complete source clock-chain defect. -/
theorem actual_em_physical_paired_left_defect (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    (correctedPhysicalClock event eps (sourceFrequency eps s) n).transpose*ᵥ
      emPhysicalPairedLeftMode event eps n mu (s : ℂ)=
        -emPhysicalPairedLeftDefect event eps n mu (s : ℂ) := by
  have point : sourceFrequency eps s/eps^2=s := by
    unfold sourceFrequency
    exact mul_div_cancel_left₀ s (pow_ne_zero 2 eps_ne)
  have paid := actual_corrected_physical_threshold event eps (sourceFrequency eps s) n eps_ne
    (by simpa only [point] using regular)
  rw [point] at paid
  rw [paid]
  have scaled := scaled_left_quotient ((zeroClockPencil event eps n).map (eval (s : ℂ)))
    (actualEMZeroClockLeftMode event eps n mu (s : ℂ))
    (fun i => (emCancelledLeftClockChain event eps n mu (s : ℂ) i).eval (s : ℂ))
    ((eps^2 : ℂ)^emFullRowPoleOrder event eps n mu (s : ℂ))
    ((emColumnDenominatorTail event eps n (s : ℂ)).eval (s : ℂ))
    ((zeroClockClearing event eps n).eval (s : ℂ))
    (actual_em_left_mode_source_defect event eps n mu nu (s : ℂ) root)
  funext i
  simpa only [zeroClockThresholdPencil,emPhysicalPairedLeftMode,emPhysicalPairedLeftDefect,
    Matrix.mulVec,dotProduct,Matrix.transpose_apply,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,Pi.neg_apply]
      using congrFun scaled i

theorem source_em_physical_left_nonzero (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (eps_ne : eps≠0) (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emPhysicalPairedLeftMode event eps n mu a≠0 := by
  have mode := source_em_left_mode_nonzero event eps n mu nu a root
  have tail := source_em_denominator_tail_nonzero event eps n mu nu a root
  have alpha : (eps^2 : ℂ)^emFullRowPoleOrder event eps n mu a≠0 :=
    pow_ne_zero _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr eps_ne))
  intro vanish
  apply mode
  funext i
  have coordinate := congrFun vanish i
  simp only [emPhysicalPairedLeftMode,Pi.smul_apply,Pi.zero_apply,smul_eq_mul] at coordinate
  exact (div_eq_zero_iff.mp ((mul_eq_zero.mp coordinate).resolve_left alpha)).resolve_right tail

/-- Exact left-kernel recognition is itself a condition on the original cancelled clock-chain source. -/
theorem actual_source_left_kernel_condition (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    (correctedPhysicalClock event eps (sourceFrequency eps s) n).transpose*ᵥ
      emPhysicalPairedLeftMode event eps n mu (s : ℂ)=0 ↔
        emPhysicalPairedLeftDefect event eps n mu (s : ℂ)=0 := by
  rw [actual_em_physical_paired_left_defect event eps s n mu nu eps_ne regular root,neg_eq_zero]

end LowEnergy.GaussComposite.ActualDressedEMPolePairEnergy
