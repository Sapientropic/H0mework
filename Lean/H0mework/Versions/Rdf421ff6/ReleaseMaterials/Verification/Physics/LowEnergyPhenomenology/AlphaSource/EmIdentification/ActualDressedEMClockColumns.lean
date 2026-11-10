import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedZeroClockFullMode

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMZeroClockColumns
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open LowEnergy.GaussComposite.ActualDressedPoleWardMode LowEnergy.ActualDressedPoleWardMode
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedZeroClockFrequency
open ActualDressedZeroClockVector ActualEMCurrentSplit ActualEMCarrierOwn
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator commonDeterminant
  commonEMTensorNumerator emInsertion correctedGreen

/-- Four original forcing columns of the same whole dressed adjugate, before any observer. -/
def commonEMSourceColumn (event : DressedEvent) (n : PhysicalMomentum) (nu : Fin 4) :
    Fin 289 → Parameters := commonDenominator event n •
      ((commonClearedPencil event n).adjugate*ᵥfun i => MvPolynomial.C (emInsertion i nu))

def fullClockEMColumn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (nu : Fin 4) :
    Fin 289 → (ℂ[X])[X] := fun i => frequencyClockSlice eps (commonEMSourceColumn event n nu i)

def zeroClockEMColumn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (nu : Fin 4) :
    Fin 289 → ℂ[X] :=
  fun i => (fullClockEMColumn event eps n nu i).coeff (frequencyClockOrder event eps n)

def zeroClockEMColumnFraction (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (nu : Fin 4) :
    Fin 289 → RatFunc ℂ :=
  fun i => readFraction (zeroClockEMColumn event eps n nu i) (zeroClockFrequencyDenominator event eps n)

def EMColumnsClockFinite (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Prop :=
  ∀nu i, X^frequencyClockOrder event eps n∣fullClockEMColumn event eps n nu i

def correctedEMColumn (event : DressedEvent) (eps s sigma : ℝ) (n : PhysicalMomentum) (nu : Fin 4) :
    Fin 289 → ℂ := correctedGreen event eps s sigma n*ᵥfun i => emInsertion i nu

theorem actual_common_em_column_equation (event : DressedEvent) (n : PhysicalMomentum) (nu : Fin 4) :
    commonClearedPencil event n*ᵥcommonEMSourceColumn event n nu=
      commonDeterminant event n • (commonDenominator event n • fun i => MvPolynomial.C (emInsertion i nu)) := by
  unfold commonEMSourceColumn commonDeterminant
  rw [Matrix.mulVec_smul,Matrix.mulVec_mulVec,Matrix.mul_adjugate,
    Matrix.smul_mulVec,Matrix.one_mulVec]
  exact smul_comm _ _ _

theorem actual_common_em_column_observer (event : DressedEvent) (n : PhysicalMomentum) (mu nu : Fin 4) :
    dotProduct (fun i => MvPolynomial.C (emInsertion i mu)) (commonEMSourceColumn event n nu)=
      commonEMTensorNumerator event n mu nu := by
  unfold commonEMSourceColumn commonEMTensorNumerator
  rw [dotProduct_smul,smul_eq_mul]

private theorem mapped_equation {α β ι : Type*} [CommRing α] [CommRing β] [Fintype ι]
    (f : α →+* β) (H : Matrix ι ι α) (V F : ι → α) (D : α) (paid : H*ᵥV=D • F) :
    H.map f*ᵥ(fun i => f (V i))=f D • (fun i => f (F i)) := by
  have mapped := congrArg (fun v : ι → α => fun i => f (v i)) paid
  funext i
  simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,map_sum,map_mul,
    Pi.smul_apply,smul_eq_mul] using congrFun mapped i

theorem actual_full_clock_em_column_equation (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4) :
    fullClockPencil event eps n*ᵥfullClockEMColumn event eps n nu=
      frequencyClockDeterminant event eps n • (fullClockClearing event eps n •
        fun i => Polynomial.C (Polynomial.C (emInsertion i nu))) := by
  have paid := mapped_equation (frequencyClockSlice eps) _ _ _ _
    (actual_common_em_column_equation event n nu)
  have constant (c : ℂ) : frequencyClockSlice eps (MvPolynomial.C c)=Polynomial.C (Polynomial.C c) := by
    simp [frequencyClockSlice]
  unfold fullClockPencil fullClockEMColumn frequencyClockDeterminant fullClockClearing
  funext i
  simpa only [Pi.smul_apply,smul_eq_mul,map_mul,constant] using congrFun paid i

theorem actual_full_clock_em_column_observer (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) :
    dotProduct (fun i => Polynomial.C (Polynomial.C (emInsertion i mu)))
      (fullClockEMColumn event eps n nu)=frequencyClockEMNumerator event eps n mu nu := by
  have mapped := congrArg (frequencyClockSlice eps) (actual_common_em_column_observer event n mu nu)
  have constant (c : ℂ) : frequencyClockSlice eps (MvPolynomial.C c)=Polynomial.C (Polynomial.C c) := by
    simp [frequencyClockSlice]
  simpa only [fullClockEMColumn,frequencyClockEMNumerator,Matrix.map_apply,dotProduct,map_sum,map_mul,constant] using mapped

/-- The sixteen original EM numerators are literal detector reads of these four full columns. -/
theorem actual_zero_clock_em_column_observer (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) :
    dotProduct (fun i => Polynomial.C (emInsertion i mu)) (zeroClockEMColumn event eps n nu)=
      zeroClockFrequencyEMNumerator event eps n mu nu := by
  have coefficient := congrArg (fun P : (ℂ[X])[X] => P.coeff (frequencyClockOrder event eps n))
    (actual_full_clock_em_column_observer event eps n mu nu)
  simpa only [zeroClockEMColumn,zeroClockFrequencyEMNumerator,dotProduct,finsetSum_coeff,coeff_C_mul] using coefficient

theorem source_em_columns_pay_tensor_factors (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (finite : EMColumnsClockFinite event eps n) :
    ∀mu nu, X^frequencyClockOrder event eps n∣frequencyClockEMNumerator event eps n mu nu := by
  intro mu nu
  rw [← actual_full_clock_em_column_observer]
  unfold dotProduct
  apply Finset.dvd_sum
  intro i _
  exact dvd_mul_of_dvd_right (finite nu i) _

private theorem equation_coeff {ι : Type*} [Fintype ι]
    (H : Matrix ι ι (ℂ[X])[X]) (V : ι → (ℂ[X])[X]) (D d : (ℂ[X])[X])
    (fs : ι → ℂ) (paid : H*ᵥV=D • (d • fun i => Polynomial.C (Polynomial.C (fs i))))
    (k : ℕ) :
    (∑a ∈ Finset.HasAntidiagonal.antidiagonal k,
      (fun i j => (H i j).coeff a.1)*ᵥ(fun j => (V j).coeff a.2))=
      (D*d).coeff k • fun i => Polynomial.C (fs i) := by
  funext i
  have coefficient := congrArg (fun P : (ℂ[X])[X] => P.coeff k) (congrFun paid i)
  have left : ((H*ᵥV) i).coeff k=
      ∑j, ∑a ∈ Finset.HasAntidiagonal.antidiagonal k, (H i j).coeff a.1*(V j).coeff a.2 := by
    simp only [Matrix.mulVec,dotProduct,finsetSum_coeff,coeff_mul]
  have right : ((D • (d • fun j => Polynomial.C (Polynomial.C (fs j)))) i).coeff k=
      (D*d).coeff k*Polynomial.C (fs i) := by
    change (D*(d*Polynomial.C (Polynomial.C (fs i)))).coeff k=_
    rw [← mul_assoc,coeff_mul_C]
  rw [left,right] at coefficient
  simp only [Finset.sum_apply,Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  exact coefficient

/-- All 289 rows and every cross clock coefficient are kept for every original EM forcing column. -/
theorem actual_full_clock_em_coefficient_equation (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4) (k : ℕ) :
    (∑a ∈ Finset.HasAntidiagonal.antidiagonal k,
      (fun i j => (fullClockPencil event eps n i j).coeff a.1)*ᵥ
        (fun j => (fullClockEMColumn event eps n nu j).coeff a.2))=
      (frequencyClockDeterminant event eps n*fullClockClearing event eps n).coeff k •
        fun i => Polynomial.C (emInsertion i nu) :=
  equation_coeff _ _ _ _ _ (actual_full_clock_em_column_equation event eps n nu) k

end LowEnergy.GaussComposite.ActualDressedEMZeroClockColumns
