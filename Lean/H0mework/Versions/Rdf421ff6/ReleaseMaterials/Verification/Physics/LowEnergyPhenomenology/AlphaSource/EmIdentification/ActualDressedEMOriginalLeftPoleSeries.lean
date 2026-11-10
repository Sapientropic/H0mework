import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMPairedEnergyTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMVisiblePoleTransport
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMFullPoleFlux ActualDressedEMPhysicalResidueFlux
open ActualDressedEMPolePairEnergy ActualEMCarrierOwn
open LowEnergy.ActualDressedVisiblePole LowEnergy.ActualDressedPoleWardMode
open scoped Matrix BigOperators
attribute [local irreducible] zeroClockPencil zeroClockClearing zeroClockFrequencyDenominator zeroClockEMRow
  emLeftCancellationOrder emFullRowPoleOrder emCancelledLeftRow emCancelledLeftClockChain
  emColumnDenominatorTail emCorrectedPoleSeries emInsertion

def emLeftPoleSeries (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) : Fin 289→PowerSeries ℂ :=
  fun i => (taylor a (emCancelledLeftRow event eps n mu a i) : PowerSeries ℂ)*
    (taylor a (emColumnDenominatorTail event eps n a) : PowerSeries ℂ)⁻¹

def emLeftClockDefectSeries (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) : Fin 289→PowerSeries ℂ :=
  fun i => (taylor a (emCancelledLeftClockChain event eps n mu a i) : PowerSeries ℂ)*
    (taylor a (emColumnDenominatorTail event eps n a) : PowerSeries ℂ)⁻¹*
      (taylor a (zeroClockClearing event eps n) : PowerSeries ℂ)⁻¹

def emPhysicalLeftPoleCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289→ℂ :=
  fun i => ((eps^2 : ℝ) : ℂ)^emFullRowPoleOrder event eps n mu a*
    PowerSeries.coeff r (emLeftPoleSeries event eps n mu a i)/((eps^2 : ℝ) : ℂ)^r

def emPhysicalLeftClockDefectCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289→ℂ :=
  fun i => ((eps^2 : ℝ) : ℂ)^emFullRowPoleOrder event eps n mu a*
    PowerSeries.coeff r (emLeftClockDefectSeries event eps n mu a i)/((eps^2 : ℝ) : ℂ)^r

private theorem denominator_after_cancellation (D : ℂ[X]) (a : ℂ) (k : ℕ) (lower : k≤D.rootMultiplicity a) :
    D /ₘ (X-C a)^k=(X-C a)^(D.rootMultiplicity a-k)*(D /ₘ (X-C a)^D.rootMultiplicity a) := by
  have factor : (X-C a)^k*(D /ₘ (X-C a)^k)=D := by
    have division := modByMonic_add_div D ((X-C a)^k)
    rw [(modByMonic_eq_zero_iff_dvd ((monic_X_sub_C a).pow k)).mpr
      ((pow_dvd_pow (X-C a) lower).trans (pow_rootMultiplicity_dvd D a)),zero_add] at division
    exact division
  apply mul_left_cancel₀ (pow_ne_zero k (X_sub_C_ne_zero a))
  rw [factor,←mul_assoc,←pow_add,Nat.add_sub_of_le lower,pow_mul_divByMonic_rootMultiplicity_eq]

private theorem normalized_left_series {ι : Type*} [Fintype ι]
    (H : Matrix ι ι (PowerSeries ℂ)) (W B : ι→PowerSeries ℂ) (T d : PowerSeries ℂ) (E : ι→ℂ) (q : ℕ)
    (tUnit : PowerSeries.constantCoeff T≠0) (dUnit : PowerSeries.constantCoeff d≠0)
    (source : H.transpose*ᵥW+B=(PowerSeries.X : PowerSeries ℂ)^q • ((T*d) • fun i => PowerSeries.C (E i))) :
    Matrix.transpose (fun i j => H i j*d⁻¹)*ᵥ(fun i => W i*T⁻¹)+
      (fun i => B i*T⁻¹*d⁻¹)=(PowerSeries.X : PowerSeries ℂ)^q • (fun i => PowerSeries.C (E i)) := by
  funext i
  have factored : (Matrix.transpose (fun i j => H i j*d⁻¹)*ᵥ(fun i => W i*T⁻¹)) i+
      B i*T⁻¹*d⁻¹=((H.transpose*ᵥW) i+B i)*(T⁻¹*d⁻¹) := by
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,add_mul,Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · ring
  change (Matrix.transpose (fun i j => H i j*d⁻¹)*ᵥ(fun i => W i*T⁻¹)) i+
    B i*T⁻¹*d⁻¹=(PowerSeries.X : PowerSeries ℂ)^q*PowerSeries.C (E i)
  rw [factored]
  have paid := congrFun source i
  change (H.transpose*ᵥW) i+B i=(PowerSeries.X : PowerSeries ℂ)^q*((T*d)*PowerSeries.C (E i)) at paid
  rw [paid]
  calc
    _=(PowerSeries.X : PowerSeries ℂ)^q*PowerSeries.C (E i)*((T*T⁻¹)*(d*d⁻¹)) := by ring
    _=_ := by rw [PowerSeries.mul_inv_cancel _ tUnit,PowerSeries.mul_inv_cancel _ dUnit,mul_one,mul_one]

/-- The complete left series retains original sigma feedback and every frequency derivative of the mode. -/
theorem actual_em_original_left_pole_series (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (regular : (zeroClockClearing event eps n).eval a≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    (emCorrectedPoleSeries event eps n a).transpose*ᵥemLeftPoleSeries event eps n mu a+
      emLeftClockDefectSeries event eps n mu a=
      (PowerSeries.X : PowerSeries ℂ)^emFullRowPoleOrder event eps n mu a •
        (fun i => PowerSeries.C (emInsertion i mu)) := by
  have source := actual_em_cancelled_left_equation event eps n mu nu a root
  have lower := (source_cancellation_order_lt (zeroClockEMRow event eps n mu)
    (zeroClockFrequencyDenominator event eps n) (fun i => emInsertion i nu) a
      (by rw [actual_zero_clock_em_row_observer];exact root)).le
  have denominator := denominator_after_cancellation (zeroClockFrequencyDenominator event eps n) a _ lower
  have actualDenominator : zeroClockFrequencyDenominator event eps n /ₘ (X-C a)^emLeftCancellationOrder event eps n mu a=
      (X-C a)^emFullRowPoleOrder event eps n mu a*emColumnDenominatorTail event eps n a := by
    simpa only [emLeftCancellationOrder,emFullRowPoleOrder,emColumnDenominatorTail] using denominator
  rw [actualDenominator] at source
  let F : ℂ[X]→+*PowerSeries ℂ := Polynomial.coeToPowerSeries.ringHom.comp (taylorAlgHom a).toRingHom
  have Fval (P : ℂ[X]) : F P=(taylor a P : PowerSeries ℂ) := rfl
  have constant (z : ℂ) : F (C z)=PowerSeries.C z := by rw [Fval,taylor_C,Polynomial.coe_C]
  have rootPower : F ((X-C a)^emFullRowPoleOrder event eps n mu a)=
      (PowerSeries.X : PowerSeries ℂ)^emFullRowPoleOrder event eps n mu a := by
    rw [Fval]
    simp only [taylor_pow,map_sub,taylor_X,taylor_C,add_sub_cancel_right,Polynomial.coe_pow,Polynomial.coe_X]
  have mapped : Matrix.transpose (fun i j => F (zeroClockPencil event eps n i j))*ᵥ
      (fun i => F (emCancelledLeftRow event eps n mu a i))+
        (fun i => F (emCancelledLeftClockChain event eps n mu a i))=
      (PowerSeries.X : PowerSeries ℂ)^emFullRowPoleOrder event eps n mu a •
        ((F (emColumnDenominatorTail event eps n a)*F (zeroClockClearing event eps n)) •
          fun i => PowerSeries.C (emInsertion i mu)) := by
    funext i
    have paid := congrArg F (congrFun source i)
    simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      map_sum,map_mul,map_add,rootPower,constant,mul_assoc] using paid
  have result := normalized_left_series _ _ _ _ _ (fun i => emInsertion i mu) _
    (by simpa only [Fval,Polynomial.constantCoeff_coe,taylor_coeff_zero] using
      source_em_denominator_tail_nonzero event eps n mu nu a root)
    (by simpa only [Fval,Polynomial.constantCoeff_coe,taylor_coeff_zero] using regular) mapped
  funext i
  simpa only [emCorrectedPoleSeries,emLeftPoleSeries,emLeftClockDefectSeries,Fval,
    Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun result i

private theorem physical_factor {ι : Type*} [Fintype ι] (P V : ι→ℕ→ℂ) (B : ℂ) (beta : ℂ) (q k : ℕ) :
    (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,(P j p.1/beta^p.1)*(beta^q*V j p.2/beta^p.2))+
      beta^q*B/beta^k=
      (beta^q/beta^k)*((∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,P j p.1*V j p.2)+B) := by
  rw [mul_add,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have degree := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [div_mul_div_comm,←pow_add,degree]
    ring
  · ring

/-- Every lower left coefficient carries its complete original sigma and frequency chain. -/
theorem actual_em_physical_lower_left_chain (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (regular : (zeroClockClearing event eps n).eval a≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (k : ℕ) (lower : k<emFullRowPoleOrder event eps n mu a) (i : Fin 289) :
    (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
      emPhysicalCorrectedPoleCoefficient event eps n a p.1 j i*
        emPhysicalLeftPoleCoefficient event eps n mu a p.2 j)+
      emPhysicalLeftClockDefectCoefficient event eps n mu a k i=0 := by
  have source := congrArg (PowerSeries.coeff k)
    (congrFun (actual_em_original_left_pole_series event eps n mu nu a regular root) i)
  have forced : PowerSeries.coeff k ((PowerSeries.X : PowerSeries ℂ)^emFullRowPoleOrder event eps n mu a*
      PowerSeries.C (emInsertion i mu))=0 := by
    rw [PowerSeries.coeff_X_pow_mul',if_neg (Nat.not_le_of_lt lower)]
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_sum] at source
  rw [forced] at source
  have raw : (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
      emCorrectedPoleCoefficient event eps n a p.1 j i*PowerSeries.coeff p.2 (emLeftPoleSeries event eps n mu a j))+
      PowerSeries.coeff k (emLeftClockDefectSeries event eps n mu a i)=0 := by
    simpa only [PowerSeries.coeff_mul,emCorrectedPoleCoefficient] using source
  have result := physical_factor (fun j r => emCorrectedPoleCoefficient event eps n a r j i)
    (fun j r => PowerSeries.coeff r (emLeftPoleSeries event eps n mu a j))
    (PowerSeries.coeff k (emLeftClockDefectSeries event eps n mu a i)) ((eps^2 : ℝ) : ℂ)
    (emFullRowPoleOrder event eps n mu a) k
  rw [raw,mul_zero] at result
  simpa only [emPhysicalCorrectedPoleCoefficient,emPhysicalLeftPoleCoefficient,
    emPhysicalLeftClockDefectCoefficient] using result

end LowEnergy.GaussComposite.ActualDressedEMVisiblePoleTransport
