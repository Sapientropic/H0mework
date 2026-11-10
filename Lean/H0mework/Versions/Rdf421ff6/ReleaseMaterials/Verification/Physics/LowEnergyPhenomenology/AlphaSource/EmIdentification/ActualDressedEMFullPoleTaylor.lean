import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMCanonicalFullPole
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMTaylorPoleFlux
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMFullPoleFlux LowEnergy.ActualDressedVisiblePole ActualEMCarrierOwn
open scoped Matrix BigOperators

def emPoleClockCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : ℂ) (r : ℕ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => (taylor a (zeroClockPencil event eps n i j)).coeff r

def emPoleCancelledColumnCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289 → ℂ :=
  fun i => (taylor a (emCancelledFullColumn event eps n nu a i)).coeff r

def emPoleForcingCoefficient (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : ℂ) (r : ℕ) : ℂ :=
  (taylor a (emColumnDenominatorTail event eps n a*zeroClockClearing event eps n)).coeff r

private theorem taylor_column_forcing {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ[X]) (W : ι → ℂ[X]) (T : ℂ[X]) (fd : ι → ℂ) (a : ℂ) (q r : ℕ)
    (equation : H*ᵥW=(X-C a)^q • (T • fun i => C (fd i))) (i : ι) :
    (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal r, (taylor a (H i j)).coeff p.1*(taylor a (W j)).coeff p.2)=
      if q≤r then (taylor a T).coeff (r-q)*fd i else 0 := by
  have value := congrArg (fun P : ℂ[X] => (taylor a P).coeff r) (congrFun equation i)
  simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,map_sum,finsetSum_coeff,
    taylor_mul] at value
  have shifted : taylor a ((X-C a)^q)=X^q := by
    rw [taylor_pow,map_sub,taylor_X,taylor_C,add_sub_cancel_right]
  rw [shifted,coeff_X_pow_mul'] at value
  simp only [taylor_C,coeff_mul_C] at value
  simpa only [coeff_mul] using value

/-- Every source order, including the forced order and all higher terms, is retained. -/
theorem actual_em_full_pole_taylor_forcing (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) (r : ℕ) (i : Fin 289) :
    (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal r,
      emPoleClockCoefficient event eps n a p.1 i j*
        emPoleCancelledColumnCoefficient event eps n nu a p.2 j)=
      if emFullColumnPoleOrder event eps n nu a≤r then
        emPoleForcingCoefficient event eps n a (r-emFullColumnPoleOrder event eps n nu a)*emInsertion i nu
      else 0 :=
  taylor_column_forcing _ _ _ _ a _ r
    (actual_em_pole_forcing_identity event eps n mu nu a balanced finite root) i

def physicalClockPolynomial (eps : ℝ) (P : ℂ[X]) : ℂ[X] :=
  P.comp (C (((eps^2 : ℝ) : ℂ)⁻¹)*X)

private theorem physical_taylor (P : ℂ[X]) (beta a : ℂ) (regular : beta≠0) :
    taylor (beta*a) (P.comp (C beta⁻¹*X))=(taylor a P).comp (C beta⁻¹*X) := by
  simp only [taylor_apply,comp_assoc,mul_comp,C_comp,X_comp,add_comp]
  congr 1
  have constant : C beta⁻¹*C (beta*a)=C a := by
    rw [← C_mul,← mul_assoc,inv_mul_cancel₀ regular,one_mul]
  rw [mul_add,constant]

/-- The original physical omega=eps^2*s scales every full source Taylor order. -/
theorem actual_em_physical_clock_taylor_coefficient (eps : ℝ) (P : ℂ[X]) (a : ℂ)
    (nonzero : eps≠0) (r : ℕ) :
    (taylor (((eps^2 : ℝ) : ℂ)*a) (physicalClockPolynomial eps P)).coeff r=
      (taylor a P).coeff r/((eps^2 : ℝ) : ℂ)^r := by
  have regular : ((eps^2 : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 nonzero)
  rw [physicalClockPolynomial,physical_taylor P _ a regular,comp_C_mul_X_coeff]
  rw [inv_pow,div_eq_mul_inv]

private theorem scaled_convolution {ι : Type*} [Fintype ι]
    (A B : ι → ℕ → ℂ) (beta : ℂ) (r : ℕ) :
    (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal r, A j p.1/beta^p.1*(B j p.2/beta^p.2))=
      (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal r, A j p.1*B j p.2)/beta^r := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p member
  have degree : p.1+p.2=r := Finset.HasAntidiagonal.mem_antidiagonal.mp member
  rw [div_mul_div_comm,← pow_add,degree]

/-- The same complete matrix equation is transported to every original physical clock order. -/
theorem actual_em_physical_pole_taylor_forcing (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) (nonzero : eps≠0)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) (r : ℕ) (i : Fin 289) :
    (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal r,
      (taylor (((eps^2 : ℝ) : ℂ)*a) (physicalClockPolynomial eps (zeroClockPencil event eps n i j))).coeff p.1*
      (taylor (((eps^2 : ℝ) : ℂ)*a) (physicalClockPolynomial eps (emCancelledFullColumn event eps n nu a j))).coeff p.2)=
      if emFullColumnPoleOrder event eps n nu a≤r then
        (emPoleForcingCoefficient event eps n a (r-emFullColumnPoleOrder event eps n nu a)*emInsertion i nu)/
          ((eps^2 : ℝ) : ℂ)^r
      else 0 := by
  simp_rw [actual_em_physical_clock_taylor_coefficient eps _ a nonzero]
  rw [scaled_convolution]
  change ((∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal r,
    emPoleClockCoefficient event eps n a p.1 i j*emPoleCancelledColumnCoefficient event eps n nu a p.2 j)/
    ((eps^2 : ℝ) : ℂ)^r)=_
  rw [actual_em_full_pole_taylor_forcing event eps n mu nu a balanced finite root r i]
  split_ifs <;> simp only [zero_div]

end LowEnergy.GaussComposite.ActualDressedEMTaylorPoleFlux
