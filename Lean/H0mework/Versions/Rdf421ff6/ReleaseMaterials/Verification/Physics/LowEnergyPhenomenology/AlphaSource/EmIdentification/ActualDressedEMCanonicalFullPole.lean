import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCorrectedPhysicalClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMFullPoleFlux
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open LowEnergy.ActualDressedPoleWardMode LowEnergy.ActualDressedVisiblePole
open ActualEMCarrierOwn Filter Set
open scoped Matrix BigOperators Topology

def emColumnCancellationOrder (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) : ℕ :=
  sourceCancellationOrder (zeroClockEMColumn event eps n nu) (zeroClockFrequencyDenominator event eps n) a

def emFullColumnPoleOrder (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) : ℕ :=
  (zeroClockFrequencyDenominator event eps n).rootMultiplicity a-emColumnCancellationOrder event eps n nu a

def emColumnDenominatorTail (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (a : ℂ) : ℂ[X] :=
  zeroClockFrequencyDenominator event eps n /ₘ (X-C a)^(zeroClockFrequencyDenominator event eps n).rootMultiplicity a

def emCancelledFullColumn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) :
    Fin 289 → ℂ[X] :=
  fun i => zeroClockEMColumn event eps n nu i /ₘ (X-C a)^emColumnCancellationOrder event eps n nu a

def emNormalizedFullPoleMode (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) :
    Fin 289 → ℂ :=
  fun i => actualEMZeroClockMode event eps n nu a i/(emColumnDenominatorTail event eps n a).eval a

private theorem column_root (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    a∈visibleRoots (readFraction
      (dotProduct (fun i => C (emInsertion i mu)) (zeroClockEMColumn event eps n nu))
      (zeroClockFrequencyDenominator event eps n)) := by
  rw [actual_zero_clock_em_column_observer]
  exact root

theorem source_em_full_pole_order_positive (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    0<emFullColumnPoleOrder event eps n nu a :=
  Nat.sub_pos_iff_lt.mpr (source_cancellation_order_lt _ _ _ _ (column_root event eps n mu nu a root))

theorem source_em_denominator_tail_nonzero (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    (emColumnDenominatorTail event eps n a).eval a≠0 := by
  have observed := column_root event eps n mu nu a root
  have nonzero : zeroClockFrequencyDenominator event eps n≠0 := by
    intro zero
    simp [zero,readFraction,visibleRoots] at observed
  exact eval_divByMonic_pow_rootMultiplicity_ne_zero a nonzero

private theorem coordinate_factor {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ) (i : ι) :
    (X-C a)^sourceCancellationOrder V D a∣V i := by
  by_cases zero : V i=0
  · rw [zero];exact dvd_zero _
  · have bound : sourceCancellationOrder V D a ≤
        if V i=0 then D.rootMultiplicity a else (V i).rootMultiplicity a :=
      Finset.min'_le (sourceVanishingOrders V D a)
      (if V i=0 then D.rootMultiplicity a else (V i).rootMultiplicity a)
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    rw [if_neg zero] at bound
    exact (le_rootMultiplicity_iff zero).mp bound

private theorem power_division (P : ℂ[X]) (a : ℂ) (k : ℕ) (factor : (X-C a)^k∣P) :
    (X-C a)^k*(P /ₘ (X-C a)^k)=P := by
  have equation := modByMonic_add_div P ((X-C a)^k)
  rw [(modByMonic_eq_zero_iff_dvd ((monic_X_sub_C a).pow k)).mpr factor,zero_add] at equation
  exact equation

private theorem cancelled_column_equation {ι : Type*} [Fintype ι] [Nonempty ι]
    (H : Matrix ι ι ℂ[X]) (V F : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ)
    (lower : sourceCancellationOrder V D a ≤ D.rootMultiplicity a)
    (equation : H*ᵥV=D • F) :
    H*ᵥ(fun i => V i /ₘ (X-C a)^sourceCancellationOrder V D a)=
      (D /ₘ (X-C a)^sourceCancellationOrder V D a) • F := by
  let k := sourceCancellationOrder V D a
  let P : ℂ[X] := (X-C a)^k
  let W : ι → ℂ[X] := fun i => V i /ₘ P
  have pNonzero : P≠0 := pow_ne_zero _ (X_sub_C_ne_zero a)
  have vector : V=P • W := by
    funext i
    exact (power_division _ a k (coordinate_factor _ _ a i)).symm
  have denominator : P*(D /ₘ P)=D :=
    power_division _ a k ((pow_dvd_pow (X-C a) lower).trans (pow_rootMultiplicity_dvd _ a))
  rw [vector,Matrix.mulVec_smul] at equation
  funext i
  change (H*ᵥW) i=(D /ₘ P)*F i
  apply mul_left_cancel₀ pNonzero
  calc
    _=D*F i := congrFun equation i
    _=(P*(D /ₘ P))*F i := congrArg (fun x : ℂ[X] => x*F i) denominator.symm
    _=_ := mul_assoc _ _ _

private theorem canonical_full_pole_limit {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ) (nonzero : D≠0)
    (lower : sourceCancellationOrder V D a < D.rootMultiplicity a) :
    Tendsto (fun z : ℂ => (z-a)^(D.rootMultiplicity a-sourceCancellationOrder V D a) •
      (fun i => (readFraction (V i) D).num.eval z/(readFraction (V i) D).denom.eval z))
      (nhdsWithin a ({a}ᶜ))
      (𝓝 (fun i => sourcePoleMode V D a i/(D /ₘ (X-C a)^D.rootMultiplicity a).eval a)) := by
  let k := sourceCancellationOrder V D a
  let q := D.rootMultiplicity a-k
  let tail := D /ₘ (X-C a)^D.rootMultiplicity a
  have tailNonzero : tail.eval a≠0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a nonzero
  have order : D.rootMultiplicity a=k+q := by
    dsimp only [k,q]
    omega
  have dFactor : (X-C a)^D.rootMultiplicity a*tail=D := pow_mul_divByMonic_rootMultiplicity_eq D a
  have continuousTail : Continuous (fun z : ℂ => tail.eval z) := by fun_prop
  have tailChart : ∀ᶠ z : ℂ in 𝓝 a, tail.eval z≠0 :=
    (continuousTail.tendsto a).eventually (eventually_ne_nhds tailNonzero)
  apply tendsto_pi_nhds.2
  intro i
  let W := V i /ₘ (X-C a)^k
  have vFactor : (X-C a)^k*W=V i :=
    power_division _ a k (coordinate_factor _ _ a i)
  have continuousW : Continuous (fun z : ℂ => W.eval z) := by fun_prop
  have limit := (continuousW.continuousAt.div continuousTail.continuousAt tailNonzero).tendsto.mono_left
    (show nhdsWithin a ({a}ᶜ)≤𝓝 a from inf_le_left)
  change Tendsto (fun z : ℂ => (z-a)^q*((readFraction (V i) D).num.eval z/
    (readFraction (V i) D).denom.eval z)) (nhdsWithin a ({a}ᶜ)) (𝓝 (W.eval a/tail.eval a))
  apply Tendsto.congr' _ limit
  filter_upwards [tailChart.filter_mono inf_le_left,self_mem_nhdsWithin] with z tailRegular away
  have zNonzero : z-a≠0 := sub_ne_zero.mpr (by simpa only [mem_compl_iff,mem_singleton_iff] using away)
  have dRegular : D.eval z≠0 := by
    rw [← dFactor,eval_mul,eval_pow,eval_sub,eval_X,eval_C]
    exact mul_ne_zero (pow_ne_zero _ zNonzero) tailRegular
  have canonical := reduced_read_at_regular (V i) D z dRegular
  symm
  change (z-a)^q*((readFraction (V i) D).num.eval z/
    (readFraction (V i) D).denom.eval z)=W.eval z/tail.eval z
  rw [canonical,← vFactor,← dFactor,eval_mul,eval_mul,eval_pow,eval_pow,eval_sub,eval_X,eval_C,order,pow_add]
  field_simp [zNonzero,tailRegular]

private theorem denominator_after_cancellation (D : ℂ[X]) (a : ℂ) (k : ℕ)
    (lower : k ≤ D.rootMultiplicity a) :
    D /ₘ (X-C a)^k=(X-C a)^(D.rootMultiplicity a-k)*(D /ₘ (X-C a)^D.rootMultiplicity a) := by
  apply mul_left_cancel₀ (pow_ne_zero k (X_sub_C_ne_zero a))
  rw [power_division D a k ((pow_dvd_pow (X-C a) lower).trans (pow_rootMultiplicity_dvd D a)),
    ← mul_assoc,← pow_add,Nat.add_sub_of_le lower,pow_mul_divByMonic_rootMultiplicity_eq]

private theorem divided_vector_nonzero {ι : Type*} (v : ι → ℂ) (d : ℂ)
    (nonzero : v≠0) (regular : d≠0) : (fun i => v i/d)≠0 := by
  intro zero
  apply nonzero
  funext i
  have value := congrFun zero i
  change v i/d=0 at value
  exact (div_eq_zero_iff.mp value).resolve_right regular

/-- The source common factor is removed from the full column equation before evaluating a pole. -/
theorem actual_em_cancelled_column_equation (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    zeroClockPencil event eps n*ᵥemCancelledFullColumn event eps n nu a=
      (zeroClockFrequencyDenominator event eps n /ₘ (X-C a)^emColumnCancellationOrder event eps n nu a) •
        (zeroClockClearing event eps n • fun i => C (emInsertion i nu)) :=
  cancelled_column_equation _ _ _ _ a
    (source_cancellation_order_lt _ _ _ _ (column_root event eps n mu nu a root)).le
    (actual_zero_clock_em_threshold_equation event eps n nu balanced finite)

/-- Every column pole order appears in the original forcing identity, with its complete denominator tail. -/
theorem actual_em_pole_forcing_identity (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    zeroClockPencil event eps n*ᵥemCancelledFullColumn event eps n nu a=
      (X-C a)^emFullColumnPoleOrder event eps n nu a •
        ((emColumnDenominatorTail event eps n a*zeroClockClearing event eps n) •
          fun i => C (emInsertion i nu)) := by
  have equation := actual_em_cancelled_column_equation event eps n mu nu a balanced finite root
  have lower := source_cancellation_order_lt _ _ _ _ (column_root event eps n mu nu a root)
  have bound : emColumnCancellationOrder event eps n nu a ≤
      (zeroClockFrequencyDenominator event eps n).rootMultiplicity a := lower.le
  rw [denominator_after_cancellation _ a _ bound] at equation
  simpa only [emFullColumnPoleOrder,emColumnDenominatorTail,smul_smul,mul_assoc] using equation

theorem source_em_normalized_full_pole_nonzero (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emNormalizedFullPoleMode event eps n nu a≠0 :=
  divided_vector_nonzero _ _
    (source_pole_mode_nonzero _ _ _ _ (column_root event eps n mu nu a root))
    (source_em_denominator_tail_nonzero event eps n mu nu a root)

/-- The original canonical full-column read has a source-normalized leading pole vector. -/
theorem source_em_canonical_full_pole_limit (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    Tendsto (fun z : ℂ => (z-a)^emFullColumnPoleOrder event eps n nu a •
      (fun i => (zeroClockEMColumnFraction event eps n nu i).num.eval z/
        (zeroClockEMColumnFraction event eps n nu i).denom.eval z))
      (nhdsWithin a ({a}ᶜ)) (𝓝 (emNormalizedFullPoleMode event eps n nu a)) := by
  have nonzero : zeroClockFrequencyDenominator event eps n≠0 := by
    have observed := column_root event eps n mu nu a root
    intro zero
    simp [zero,readFraction,visibleRoots] at observed
  exact canonical_full_pole_limit _ _ a nonzero
    (source_cancellation_order_lt _ _ _ _ (column_root event eps n mu nu a root))

end LowEnergy.GaussComposite.ActualDressedEMFullPoleFlux
