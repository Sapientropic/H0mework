import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMFullPrincipalColumn
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMPhysicalResidueFlux
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMFullPoleFlux ActualDressedEMTaylorPoleFlux LowEnergy.ActualDressedVisiblePole
open ActualEMCarrierOwn Filter Set
open scoped Matrix BigOperators Topology

def emCorrectedPoleSeries (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (a : ℂ) :
    Matrix (Fin 289) (Fin 289) (PowerSeries ℂ) :=
  fun i j => (taylor a (zeroClockPencil event eps n i j) : PowerSeries ℂ)*
    (taylor a (zeroClockClearing event eps n) : PowerSeries ℂ)⁻¹

def emNormalizedPoleColumnSeries (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) : Fin 289 → PowerSeries ℂ :=
  fun i => (taylor a (emCancelledFullColumn event eps n nu a i) : PowerSeries ℂ)*
    (taylor a (emColumnDenominatorTail event eps n a) : PowerSeries ℂ)⁻¹

def emCorrectedPoleCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : ℂ) (r : ℕ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => PowerSeries.coeff r (emCorrectedPoleSeries event eps n a i j)

def emNormalizedPoleColumnCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289 → ℂ :=
  fun i => PowerSeries.coeff r (emNormalizedPoleColumnSeries event eps n nu a i)

def emPhysicalCorrectedPoleCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : ℂ) (r : ℕ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => emCorrectedPoleCoefficient event eps n a r i j/((eps^2 : ℝ) : ℂ)^r

def emPhysicalNormalizedPoleColumnCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289 → ℂ :=
  fun i => ((eps^2 : ℝ) : ℂ)^emFullColumnPoleOrder event eps n nu a*
    emNormalizedPoleColumnCoefficient event eps n nu a r i/((eps^2 : ℝ) : ℂ)^r

private theorem normalized_series_forcing {ι : Type*} [Fintype ι]
    (H : Matrix ι ι (PowerSeries ℂ)) (W : ι → PowerSeries ℂ) (T d : PowerSeries ℂ)
    (fd : ι → ℂ) (q : ℕ) (tRegular : PowerSeries.constantCoeff T≠0) (dRegular : PowerSeries.constantCoeff d≠0)
    (equation : H*ᵥW=(PowerSeries.X : PowerSeries ℂ)^q • ((T*d) • fun i => PowerSeries.C (fd i))) :
    (fun i j => H i j*d⁻¹)*ᵥ(fun i => W i*T⁻¹)=
      (PowerSeries.X : PowerSeries ℂ)^q • (fun i => PowerSeries.C (fd i)) := by
  funext i
  have value := congrFun equation i
  simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul] at value ⊢
  calc
    _=(∑j, H i j*W j)*(T⁻¹*d⁻¹) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=((PowerSeries.X : PowerSeries ℂ)^q*((T*d)*PowerSeries.C (fd i)))*(T⁻¹*d⁻¹) := by rw [value]
    _=(PowerSeries.X : PowerSeries ℂ)^q*PowerSeries.C (fd i)*(T*T⁻¹)*(d*d⁻¹) := by ring
    _=_ := by rw [PowerSeries.mul_inv_cancel T tRegular,PowerSeries.mul_inv_cancel d dRegular,mul_one,mul_one]

private theorem normalized_polynomial_series {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ[X]) (W : ι → ℂ[X]) (T d : ℂ[X]) (fd : ι → ℂ) (a : ℂ) (q : ℕ)
    (tRegular : T.eval a≠0) (dRegular : d.eval a≠0)
    (equation : H*ᵥW=(X-C a)^q • ((T*d) • fun i => C (fd i))) :
    (fun i j => (taylor a (H i j) : PowerSeries ℂ)*(taylor a d : PowerSeries ℂ)⁻¹)*ᵥ
      (fun i => (taylor a (W i) : PowerSeries ℂ)*(taylor a T : PowerSeries ℂ)⁻¹)=
        (PowerSeries.X : PowerSeries ℂ)^q • (fun i => PowerSeries.C (fd i)) := by
  let F : ℂ[X] →+* PowerSeries ℂ :=
    Polynomial.coeToPowerSeries.ringHom.comp (taylorAlgHom a).toRingHom
  have Fval (P : ℂ[X]) : F P=(taylor a P : PowerSeries ℂ) := rfl
  have constant (z : ℂ) : F (C z)=PowerSeries.C z := by
    rw [Fval,taylor_C,Polynomial.coe_C]
  have mapped : (fun i j => F (H i j))*ᵥ(fun i => F (W i))=
      (PowerSeries.X : PowerSeries ℂ)^q • ((F T*F d) • fun i => PowerSeries.C (fd i)) := by
    funext i
    have value := congrArg F (congrFun equation i)
    have rootPower : F ((X-C a)^q)=(PowerSeries.X : PowerSeries ℂ)^q := by
      rw [Fval]
      simp only [taylor_pow,map_sub,taylor_X,taylor_C,
        add_sub_cancel_right,Polynomial.coe_pow,Polynomial.coe_X]
    simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,map_sum,map_mul,rootPower,constant] at value
    simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul] using value
  exact normalized_series_forcing _ _ _ _ fd q
    (by simpa only [Fval,Polynomial.constantCoeff_coe,taylor_coeff_zero] using tRegular)
    (by simpa only [Fval,Polynomial.constantCoeff_coe,taylor_coeff_zero] using dRegular)
    mapped

/-- Original clearing and denominator-tail units normalize the complete source equation. -/
theorem actual_em_normalized_full_pole_series (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (clearingRegular : (zeroClockClearing event eps n).eval a≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emCorrectedPoleSeries event eps n a*ᵥemNormalizedPoleColumnSeries event eps n nu a=
      (PowerSeries.X : PowerSeries ℂ)^emFullColumnPoleOrder event eps n nu a •
        (fun i => PowerSeries.C (emInsertion i nu)) :=
  normalized_polynomial_series _ _ _ _ _ a _
    (source_em_denominator_tail_nonzero event eps n mu nu a root) clearingRegular
    (actual_em_pole_forcing_identity event eps n mu nu a balanced finite root)

private theorem series_forced_coefficient {ι : Type*} [Fintype ι]
    (P : Matrix ι ι (PowerSeries ℂ)) (V : ι → PowerSeries ℂ) (fd : ι → ℂ) (q : ℕ)
    (equation : P*ᵥV=(PowerSeries.X : PowerSeries ℂ)^q • fun i => PowerSeries.C (fd i)) (i : ι) :
    (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal q, PowerSeries.coeff p.1 (P i j)*PowerSeries.coeff p.2 (V j))=fd i := by
  have value := congrArg (PowerSeries.coeff q) (congrFun equation i)
  simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,map_sum] at value
  have forced : PowerSeries.coeff q ((PowerSeries.X : PowerSeries ℂ)^q*PowerSeries.C (fd i))=fd i := by
    simpa only [zero_add,PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.constantCoeff_C] using
      PowerSeries.coeff_X_pow_mul (PowerSeries.C (fd i)) q 0
  rw [forced] at value
  simpa only [PowerSeries.coeff_mul] using value

private theorem physical_forced_coefficient {ι : Type*} [Fintype ι]
    (P : ι → ℕ → ℂ) (V : ι → ℕ → ℂ) (beta : ℂ) (q : ℕ) (regular : beta≠0) :
    (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal q, (P j p.1/beta^p.1)*(beta^q*V j p.2/beta^p.2))=
      (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal q, P j p.1*V j p.2) := by
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p member
  have degree : p.1+p.2=q := Finset.HasAntidiagonal.mem_antidiagonal.mp member
  rw [div_mul_div_comm,← pow_add,degree]
  calc
    _=(beta^q*(P j p.1*V j p.2))/beta^q := by congr 1;ring
    _=_ := by rw [mul_div_cancel_left₀ _ (pow_ne_zero q regular)]

/-- The forced physical order pays the full residue balance, retaining every principal order and the analytic column. -/
theorem actual_em_physical_full_pole_balance (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) (nonzero : eps≠0)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (clearingRegular : (zeroClockClearing event eps n).eval a≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) (i : Fin 289) :
    (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal (emFullColumnPoleOrder event eps n nu a),
      emPhysicalCorrectedPoleCoefficient event eps n a p.1 i j*
        emPhysicalNormalizedPoleColumnCoefficient event eps n nu a p.2 j)=emInsertion i nu := by
  have paid := series_forced_coefficient _ _ _ _
    (actual_em_normalized_full_pole_series event eps n mu nu a balanced finite clearingRegular root) i
  have converted := physical_forced_coefficient
    (fun j r => emCorrectedPoleCoefficient event eps n a r i j)
    (fun j r => emNormalizedPoleColumnCoefficient event eps n nu a r j)
    ((eps^2 : ℝ) : ℂ) (emFullColumnPoleOrder event eps n nu a)
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 nonzero))
  exact converted.trans paid

end LowEnergy.GaussComposite.ActualDressedEMPhysicalResidueFlux
