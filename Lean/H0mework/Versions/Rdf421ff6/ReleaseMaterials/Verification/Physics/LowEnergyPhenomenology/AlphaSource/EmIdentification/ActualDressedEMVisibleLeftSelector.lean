import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMOriginalLeftPoleSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMVisiblePoleTransport
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector ActualDressedEMZeroClockColumns
open ActualDressedEMPolePairEnergy ActualEMCarrierOwn ActualDressedEMFullPoleFlux
open LowEnergy.ActualDressedVisiblePole LowEnergy.ActualDressedPoleWardMode
open scoped Matrix BigOperators
attribute [local irreducible] zeroClockEMRow zeroClockFrequencyDenominator emInsertion
 emLeftCancellationOrder emFullRowPoleOrder emCancelledLeftRow emColumnDenominatorTail

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


private theorem series_visible_coefficient {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : ι→ℂ[X]) (D : ℂ[X]) (fd : ι→ℂ) (a : ℂ)
    (root : a∈visibleRoots (readFraction (dotProduct (fun i => C (fd i)) V) D)) :
    ∃r<D.rootMultiplicity a-sourceCancellationOrder V D a,
      dotProduct fd (fun i => PowerSeries.coeff r
        ((taylor a (V i /ₘ (X-C a)^sourceCancellationOrder V D a) : PowerSeries ℂ)*
          (taylor a (D /ₘ (X-C a)^D.rootMultiplicity a) : PowerSeries ℂ)⁻¹))≠0 := by
  let k := sourceCancellationOrder V D a
  let q := D.rootMultiplicity a-k
  let W : ι→ℂ[X] := fun i => V i /ₘ (X-C a)^k
  let T : PowerSeries ℂ := (taylor a (D /ₘ (X-C a)^D.rootMultiplicity a) : PowerSeries ℂ)
  let S : PowerSeries ℂ := dotProduct (fun i => PowerSeries.C (fd i))
    (fun i => (taylor a (W i) : PowerSeries ℂ)*T⁻¹)
  let N : ℂ[X] := dotProduct (fun i => C (fd i)) W
  have dNonzero : D≠0 := by intro hz;simp [hz,readFraction,visibleRoots] at root
  have tUnit : PowerSeries.constantCoeff T≠0 := by
    simpa only [T,Polynomial.constantCoeff_coe,taylor_coeff_zero] using
      eval_divByMonic_pow_rootMultiplicity_ne_zero a dNonzero
  have scalar (r : ℕ) : PowerSeries.coeff r S=
      dotProduct fd (fun i => PowerSeries.coeff r ((taylor a (W i) : PowerSeries ℂ)*T⁻¹)) := by
    simp only [S,dotProduct,map_sum,PowerSeries.coeff_C_mul]
  have product : S*T=(taylor a N : PowerSeries ℂ) := by
    let F : ℂ[X]→+*PowerSeries ℂ := Polynomial.coeToPowerSeries.ringHom.comp (taylorAlgHom a).toRingHom
    have Fval (P : ℂ[X]) : F P=(taylor a P : PowerSeries ℂ) := rfl
    have constant (z : ℂ) : F (C z)=PowerSeries.C z := by rw [Fval,taylor_C,Polynomial.coe_C]
    have mapped : (taylor a N : PowerSeries ℂ)=
        ∑i,PowerSeries.C (fd i)*(taylor a (W i) : PowerSeries ℂ) := by
      change F N=_
      change F (∑i,C (fd i)*W i)=_
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul,constant,Fval]
    rw [mapped]
    simp only [S,dotProduct,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, mul_assoc,PowerSeries.inv_mul_cancel _ tUnit,mul_one]
  by_contra absent
  have zeros : ∀r<q,PowerSeries.coeff r S=0 := by
    intro r hr
    rw [scalar]
    exact not_ne_iff.mp (fun nonzero => absent ⟨r,hr,nonzero⟩)
  have Nzero : ∀r<q,(taylor a N).coeff r=0 := by
    intro r hr
    rw [←Polynomial.coeff_coe,←product,PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have degree := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [zeros p.1 (by omega),zero_mul]
  have Nfactor : (X-C a)^q∣N := by
    rw [X_sub_C_pow_dvd_iff,←taylor_apply]
    exact Polynomial.X_pow_dvd_iff.mpr Nzero
  have fullFactor : dotProduct (fun i => C (fd i)) V=(X-C a)^k*N := by
    simp only [dotProduct,N,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [←power_division (V i) a k (coordinate_factor V D a i)]
    change C (fd i)*((X-C a)^k*W i)=(X-C a)^k*(C (fd i)*W i)
    ring
  apply visible_numerator_not_divisible _ D a root
  rw [fullFactor]
  have lower := (source_cancellation_order_lt V D fd a root).le
  have order : D.rootMultiplicity a=k+q := (Nat.add_sub_of_le lower).symm
  rw [order,pow_add]
  exact mul_dvd_mul_left _ Nfactor

/-- A visible source pole generates a nonzero detector read at one of its actual lower left coefficients. -/
theorem actual_em_visible_left_coefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (eps_ne : eps≠0) (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    ∃r<emFullRowPoleOrder event eps n mu a,
      dotProduct (fun i => emInsertion i nu) (emPhysicalLeftPoleCoefficient event eps n mu a r)≠0 := by
  have observed : a∈visibleRoots (readFraction
      (dotProduct (fun i => C (emInsertion i nu)) (zeroClockEMRow event eps n mu))
        (zeroClockFrequencyDenominator event eps n)) := by
    rw [actual_zero_clock_em_row_observer];exact root
  obtain ⟨r,lower,nonzero⟩ := series_visible_coefficient (zeroClockEMRow event eps n mu)
    (zeroClockFrequencyDenominator event eps n) (fun i => emInsertion i nu) a observed
  have raw : dotProduct (fun i => emInsertion i nu)
      (fun i => PowerSeries.coeff r (emLeftPoleSeries event eps n mu a i))≠0 := by
    simpa only [emLeftPoleSeries,emCancelledLeftRow,emLeftCancellationOrder,emColumnDenominatorTail] using nonzero
  have beta_ne : ((eps^2 : ℝ) : ℂ)≠0 := by exact_mod_cast pow_ne_zero 2 eps_ne
  refine ⟨r,?_,?_⟩
  · simpa only [emFullRowPoleOrder,emLeftCancellationOrder] using lower
  · have factor : dotProduct (fun i => emInsertion i nu) (emPhysicalLeftPoleCoefficient event eps n mu a r)=
        (((eps^2 : ℝ) : ℂ)^emFullRowPoleOrder event eps n mu a/((eps^2 : ℝ) : ℂ)^r)*
          dotProduct (fun i => emInsertion i nu) (fun i => PowerSeries.coeff r (emLeftPoleSeries event eps n mu a i)) := by
      simp only [emPhysicalLeftPoleCoefficient,dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [factor]
    exact mul_ne_zero (div_ne_zero (pow_ne_zero _ beta_ne) (pow_ne_zero _ beta_ne)) raw

/-- The selector is generated from the original visible read, without a prescribed left mode or nonzero energy. -/
def emVisibleLeftSelector (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (eps_ne : eps≠0) (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) : ℕ :=
  Nat.find (actual_em_visible_left_coefficient event eps n mu nu a eps_ne root)

theorem actual_em_visible_left_selector_spec (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (eps_ne : eps≠0) (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emVisibleLeftSelector event eps n mu nu a eps_ne root<emFullRowPoleOrder event eps n mu a ∧
      dotProduct (fun i => emInsertion i nu) (emPhysicalLeftPoleCoefficient event eps n mu a
        (emVisibleLeftSelector event eps n mu nu a eps_ne root))≠0 :=
  Nat.find_spec (actual_em_visible_left_coefficient event eps n mu nu a eps_ne root)

end LowEnergy.GaussComposite.ActualDressedEMVisiblePoleTransport
