import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMFullPoleTaylor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMTaylorPoleFlux
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMFullPoleFlux LowEnergy.ActualDressedVisiblePole LowEnergy.ActualDressedPoleWardMode
open ActualEMCarrierOwn Filter Set
open scoped Matrix BigOperators Topology

private def commonPrincipal (W T : ℂ[X]) (a : ℂ) (q : ℕ) : ℂ[X] :=
  (W*bezoutLeft T ((X-C a)^q)) %ₘ (X-C a)^q

private def commonAnalytic (W T : ℂ[X]) (a : ℂ) (q : ℕ) : ℂ[X] :=
  W*bezoutRight T ((X-C a)^q)+((W*bezoutLeft T ((X-C a)^q)) /ₘ (X-C a)^q)*T

def emFullPrincipalPolynomial (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) : Fin 289 → ℂ[X] :=
  fun i => commonPrincipal (emCancelledFullColumn event eps n nu a i)
    (emColumnDenominatorTail event eps n a) a (emFullColumnPoleOrder event eps n nu a)

def emFullAnalyticColumnNumerator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) : Fin 289 → ℂ[X] :=
  fun i => commonAnalytic (emCancelledFullColumn event eps n nu a i)
    (emColumnDenominatorTail event eps n a) a (emFullColumnPoleOrder event eps n nu a)

def emFullPrincipalCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289 → ℂ :=
  fun i => (taylor a (emFullPrincipalPolynomial event eps n nu a i)).coeff r

def emPhysicalPrincipalCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289 → ℂ :=
  (((eps^2 : ℝ) : ℂ)^(emFullColumnPoleOrder event eps n nu a-r)) •
    emFullPrincipalCoefficient event eps n nu a r

def emFullPhysicalResidue (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) : Fin 289 → ℂ :=
  ((eps^2 : ℝ) : ℂ) •
    emFullPrincipalCoefficient event eps n nu a (emFullColumnPoleOrder event eps n nu a-1)

private theorem coprime_linear (T : ℂ[X]) (a : ℂ) (regular : T.eval a≠0) : IsCoprime T (X-C a) := by
  have division := modByMonic_add_div T (X-C a)
  rw [modByMonic_X_sub_C_eq_C_eval] at division
  have balance : T-(X-C a)*(T /ₘ (X-C a))=C (T.eval a) := by linear_combination -division
  refine ⟨C ((T.eval a)⁻¹),-C ((T.eval a)⁻¹)*(T /ₘ (X-C a)),?_⟩
  calc
    _=C ((T.eval a)⁻¹)*(T-(X-C a)*(T /ₘ (X-C a))) := by ring
    _=C ((T.eval a)⁻¹)*C (T.eval a) := congrArg (fun P : ℂ[X] => C ((T.eval a)⁻¹)*P) balance
    _=1 := by rw [← C_mul,inv_mul_cancel₀ regular,C_1]

private theorem common_principal_identity (W T : ℂ[X]) (a : ℂ) (q : ℕ) (regular : T.eval a≠0) :
    W=commonPrincipal W T a q*T+(X-C a)^q*commonAnalytic W T a q := by
  have bezout := source_bezout T ((X-C a)^q) ((coprime_linear T a regular).pow_right)
  have division := modByMonic_add_div (W*bezoutLeft T ((X-C a)^q)) ((X-C a)^q)
  unfold commonPrincipal commonAnalytic
  linear_combination -W*bezout-T*division

private theorem common_principal_degree (W T : ℂ[X]) (a : ℂ) (q : ℕ) :
    (commonPrincipal W T a q).degree<(q : WithBot ℕ) := by
  have bound := degree_modByMonic_lt (W*bezoutLeft T ((X-C a)^q)) ((monic_X_sub_C a).pow q)
  simpa only [commonPrincipal,degree_pow,degree_X_sub_C,nsmul_eq_mul,mul_one] using bound

private theorem common_principal_expansion (W T : ℂ[X]) (a z : ℂ) (q : ℕ)
    (atRoot : T.eval a≠0) (regular : T.eval z≠0) (away : z≠a) :
    W.eval z/((z-a)^q*T.eval z)=
      (∑r∈Finset.range q, (taylor a (commonPrincipal W T a q)).coeff r*(z-a)^r/(z-a)^q)+
        (commonAnalytic W T a q).eval z/T.eval z := by
  have decomposition := congrArg (Polynomial.eval z) (common_principal_identity W T a q atRoot)
  simp only [eval_add,eval_mul,eval_pow,eval_sub,eval_X,eval_C] at decomposition
  have expansion : (commonPrincipal W T a q).eval z=
      ∑r∈Finset.range q, (taylor a (commonPrincipal W T a q)).coeff r*(z-a)^r := by
    by_cases zero : commonPrincipal W T a q=0
    · simp only [zero,map_zero,coeff_zero,eval_zero,zero_mul,Finset.sum_const_zero]
    · have bound : (taylor a (commonPrincipal W T a q)).natDegree<q := by
        rw [natDegree_taylor]
        exact (natDegree_lt_iff_degree_lt zero).mpr (common_principal_degree W T a q)
      have value := (taylor a (commonPrincipal W T a q)).eval_eq_sum_range' bound (z-a)
      rw [taylor_eval_sub] at value
      exact value
  rw [← Finset.sum_div,← expansion, decomposition]
  field_simp [regular,pow_ne_zero q (sub_ne_zero.mpr away)]

private theorem coordinate_factor {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : ι → ℂ[X]) (D : ℂ[X]) (a : ℂ) (i : ι) :
    (X-C a)^sourceCancellationOrder V D a∣V i := by
  by_cases zero : V i=0
  · rw [zero];exact dvd_zero _
  · have bound : sourceCancellationOrder V D a ≤
        if V i=0 then D.rootMultiplicity a else (V i).rootMultiplicity a :=
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    rw [if_neg zero] at bound
    exact (le_rootMultiplicity_iff zero).mp bound

private theorem full_column_read {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : ι → ℂ[X]) (D : ℂ[X]) (a z : ℂ) (i : ι)
    (lower : sourceCancellationOrder V D a < D.rootMultiplicity a)
    (regular : (D /ₘ (X-C a)^D.rootMultiplicity a).eval z≠0) (away : z≠a) :
    (readFraction (V i) D).num.eval z/(readFraction (V i) D).denom.eval z=
      (V i /ₘ (X-C a)^sourceCancellationOrder V D a).eval z/
        ((z-a)^(D.rootMultiplicity a-sourceCancellationOrder V D a)*
          (D /ₘ (X-C a)^D.rootMultiplicity a).eval z) := by
  let k := sourceCancellationOrder V D a
  let q := D.rootMultiplicity a-k
  let W := V i /ₘ (X-C a)^k
  let tail := D /ₘ (X-C a)^D.rootMultiplicity a
  change (readFraction (V i) D).num.eval z/(readFraction (V i) D).denom.eval z=
    W.eval z/((z-a)^q*tail.eval z)
  have coordinate := modByMonic_add_div (V i) ((X-C a)^k)
  rw [(modByMonic_eq_zero_iff_dvd ((monic_X_sub_C a).pow k)).mpr (coordinate_factor V D a i),zero_add] at coordinate
  have denominator := pow_mul_divByMonic_rootMultiplicity_eq D a
  have vValue : (V i).eval z=(z-a)^k*W.eval z := by
    have value := congrArg (Polynomial.eval z) coordinate.symm
    simpa only [eval_mul,eval_pow,eval_sub,eval_X,eval_C] using value
  have dValue : D.eval z=(z-a)^D.rootMultiplicity a*tail.eval z := by
    have value := congrArg (Polynomial.eval z) denominator.symm
    simpa only [eval_mul,eval_pow,eval_sub,eval_X,eval_C] using value
  have dRegular : D.eval z≠0 := by
    rw [dValue]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr away)) regular
  rw [reduced_read_at_regular _ _ z dRegular,vValue,dValue]
  have order : D.rootMultiplicity a=k+q := by dsimp only [k,q];omega
  rw [order,pow_add]
  field_simp [regular,pow_ne_zero k (sub_ne_zero.mpr away)]

/-- The common full-column principal polynomial preserves every lower pole term and its analytic remainder. -/
theorem source_em_complete_full_column_principal (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a z : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (regular : (emColumnDenominatorTail event eps n a).eval z≠0) (away : z≠a) (i : Fin 289) :
    (zeroClockEMColumnFraction event eps n nu i).num.eval z/
      (zeroClockEMColumnFraction event eps n nu i).denom.eval z=
      (∑r∈Finset.range (emFullColumnPoleOrder event eps n nu a),
        emFullPrincipalCoefficient event eps n nu a r i*(z-a)^r/(z-a)^emFullColumnPoleOrder event eps n nu a)+
      (emFullAnalyticColumnNumerator event eps n nu a i).eval z/(emColumnDenominatorTail event eps n a).eval z := by
  have observed : a∈visibleRoots (readFraction
      (dotProduct (fun j => C (emInsertion j mu)) (zeroClockEMColumn event eps n nu))
      (zeroClockFrequencyDenominator event eps n)) := by
    rw [actual_zero_clock_em_column_observer]
    exact root
  exact (full_column_read _ _ a z i (source_cancellation_order_lt _ _ _ _ observed) regular away).trans
    (common_principal_expansion _ _ a z _ (source_em_denominator_tail_nonzero event eps n mu nu a root) regular away)

private theorem common_principal_leading (W T : ℂ[X]) (a : ℂ) (q : ℕ)
    (regular : T.eval a≠0) (positive : 0<q) :
    (taylor a (commonPrincipal W T a q)).coeff 0=W.eval a/T.eval a := by
  have value := congrArg (Polynomial.eval a) (common_principal_identity W T a q regular)
  simp only [eval_add,eval_mul,eval_pow,eval_sub,eval_X,eval_C,sub_self,zero_pow positive.ne',zero_mul,add_zero] at value
  rw [taylor_coeff_zero]
  exact (eq_div_iff regular).mpr value.symm

theorem source_em_full_principal_degree (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) (i : Fin 289) :
    (emFullPrincipalPolynomial event eps n nu a i).degree<
      (emFullColumnPoleOrder event eps n nu a : WithBot ℕ) :=
  common_principal_degree _ _ a _

theorem source_em_full_principal_decomposition (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emCancelledFullColumn event eps n nu a=
      emColumnDenominatorTail event eps n a • emFullPrincipalPolynomial event eps n nu a+
        (X-C a)^emFullColumnPoleOrder event eps n nu a • emFullAnalyticColumnNumerator event eps n nu a := by
  funext i
  have paid := common_principal_identity (emCancelledFullColumn event eps n nu a i)
    (emColumnDenominatorTail event eps n a) a (emFullColumnPoleOrder event eps n nu a)
    (source_em_denominator_tail_nonzero event eps n mu nu a root)
  simpa only [emFullPrincipalPolynomial,emFullAnalyticColumnNumerator,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using paid

/-- Principal and analytic columns jointly pay the original complete forcing equation. -/
theorem actual_em_full_principal_column_forcing (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emColumnDenominatorTail event eps n a • (zeroClockPencil event eps n*ᵥemFullPrincipalPolynomial event eps n nu a)+
      (X-C a)^emFullColumnPoleOrder event eps n nu a •
        (zeroClockPencil event eps n*ᵥemFullAnalyticColumnNumerator event eps n nu a)=
      (X-C a)^emFullColumnPoleOrder event eps n nu a •
        ((emColumnDenominatorTail event eps n a*zeroClockClearing event eps n) • fun i => C (emInsertion i nu)) := by
  rw [← Matrix.mulVec_smul,← Matrix.mulVec_smul,← Matrix.mulVec_add,
    ← source_em_full_principal_decomposition event eps n mu nu a root]
  exact actual_em_pole_forcing_identity event eps n mu nu a balanced finite root

theorem source_em_full_principal_leading (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emFullPrincipalCoefficient event eps n nu a 0=emNormalizedFullPoleMode event eps n nu a := by
  funext i
  exact common_principal_leading _ _ a _
    (source_em_denominator_tail_nonzero event eps n mu nu a root)
    (source_em_full_pole_order_positive event eps n mu nu a root)

private theorem physical_negative_power (A beta x : ℂ) (q r : ℕ)
    (bound : r≤q) (regular : beta≠0) (away : x≠0) :
    A*x^r/x^q=beta^(q-r)*A*(beta*x)^r/(beta*x)^q := by
  have betaPower : beta^q=beta^r*beta^(q-r) := by
    rw [← pow_add,Nat.add_sub_of_le bound]
  rw [mul_pow,mul_pow,betaPower]
  field_simp [regular,away]

private theorem physical_principal_sum (A : ℕ → ℂ) (B beta s a : ℂ) (q : ℕ)
    (regular : beta≠0) (away : s≠a) :
    (∑r∈Finset.range q, A r*(s-a)^r/(s-a)^q)+B=
      (∑r∈Finset.range q, beta^(q-r)*A r*(beta*(s-a))^r/(beta*(s-a))^q)+B := by
  congr 1
  apply Finset.sum_congr rfl
  intro r member
  exact physical_negative_power _ _ _ _ r (Finset.mem_range.mp member).le regular (sub_ne_zero.mpr away)

/-- Each canonical full-column pole term uses its own paid physical-frequency power. -/
theorem source_em_complete_physical_column_principal (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) (nonzero : eps≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (regular : (emColumnDenominatorTail event eps n a).eval (s : ℂ)≠0)
    (away : (s : ℂ)≠a) (i : Fin 289) :
    (zeroClockEMColumnFraction event eps n nu i).num.eval (s : ℂ)/
      (zeroClockEMColumnFraction event eps n nu i).denom.eval (s : ℂ)=
      (∑r∈Finset.range (emFullColumnPoleOrder event eps n nu a),
        emPhysicalPrincipalCoefficient event eps n nu a r i*
          ((sourceFrequency eps s : ℂ)-((eps^2 : ℝ) : ℂ)*a)^r/
            ((sourceFrequency eps s : ℂ)-((eps^2 : ℝ) : ℂ)*a)^emFullColumnPoleOrder event eps n nu a)+
      (emFullAnalyticColumnNumerator event eps n nu a i).eval (s : ℂ)/
        (emColumnDenominatorTail event eps n a).eval (s : ℂ) := by
  have ordinary := source_em_complete_full_column_principal event eps n mu nu a (s : ℂ) root regular away i
  have betaRegular : ((eps^2 : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 nonzero)
  have clock : (sourceFrequency eps s : ℂ)-((eps^2 : ℝ) : ℂ)*a=
      ((eps^2 : ℝ) : ℂ)*((s : ℂ)-a) := by
    simp only [sourceFrequency,Complex.ofReal_mul]
    ring
  have value := physical_principal_sum (fun r => emFullPrincipalCoefficient event eps n nu a r i)
    ((emFullAnalyticColumnNumerator event eps n nu a i).eval (s : ℂ)/(emColumnDenominatorTail event eps n a).eval (s : ℂ))
    ((eps^2 : ℝ) : ℂ) (s : ℂ) a (emFullColumnPoleOrder event eps n nu a) betaRegular away
  simpa only [← clock,emPhysicalPrincipalCoefficient,Pi.smul_apply,smul_eq_mul] using ordinary.trans value

/-- Actual original Green columns return to the complete physically normalized principal and analytic columns. -/
theorem actual_em_complete_physical_column_principal (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) (nonzero : eps≠0)
    (finite : EMColumnsClockFinite event eps n)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (regular : (emColumnDenominatorTail event eps n a).eval (s : ℂ)≠0) (away : (s : ℂ)≠a) :
    Tendsto (fun sigma : ℝ => correctedEMColumn event eps s sigma n nu)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (fun i =>
        (∑r∈Finset.range (emFullColumnPoleOrder event eps n nu a),
          emPhysicalPrincipalCoefficient event eps n nu a r i*
            ((sourceFrequency eps s : ℂ)-((eps^2 : ℝ) : ℂ)*a)^r/
              ((sourceFrequency eps s : ℂ)-((eps^2 : ℝ) : ℂ)*a)^emFullColumnPoleOrder event eps n nu a)+
        (emFullAnalyticColumnNumerator event eps n nu a i).eval (s : ℂ)/
          (emColumnDenominatorTail event eps n a).eval (s : ℂ))) := by
  have denominator := pow_mul_divByMonic_rootMultiplicity_eq (zeroClockFrequencyDenominator event eps n) a
  have chart : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0 := by
    rw [← denominator,eval_mul,eval_pow,eval_sub,eval_X,eval_C]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr away)) regular
  have actual := actual_zero_clock_em_column event eps s n nu chart finite
  have same : zeroClockEMColumnRead event eps s n nu=(fun i =>
      (∑r∈Finset.range (emFullColumnPoleOrder event eps n nu a),
        emPhysicalPrincipalCoefficient event eps n nu a r i*
          ((sourceFrequency eps s : ℂ)-((eps^2 : ℝ) : ℂ)*a)^r/
            ((sourceFrequency eps s : ℂ)-((eps^2 : ℝ) : ℂ)*a)^emFullColumnPoleOrder event eps n nu a)+
      (emFullAnalyticColumnNumerator event eps n nu a i).eval (s : ℂ)/
        (emColumnDenominatorTail event eps n a).eval (s : ℂ)) := by
    funext i
    exact source_em_complete_physical_column_principal event eps s n mu nu a nonzero root regular away i
  rw [same] at actual
  exact actual

end LowEnergy.GaussComposite.ActualDressedEMTaylorPoleFlux
