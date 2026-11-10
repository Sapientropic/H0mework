import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMTensorTransportRead

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMPolePairEnergy
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedUniformMaterialCoefficients ActualDressedEMTensorClock
open ActualDressedOrderedStatic ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMClockDispersion ActualDressedEMQuantumThreshold
open ActualEMCarrierOwn ActualDressedEMFullPoleFlux ActualDressedEMPhysicalResidueFlux
open LowEnergy.ActualDressedPoleWardMode LowEnergy.ActualDressedVisiblePole
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator commonDeterminant emInsertion
  fullClockPencil fullClockClearing frequencyClockDeterminant frequencyClockOrder clearingClockOrder

/-- The detector row is a restriction of the same complete original adjugate, with the original bilinear dual. -/
def commonEMSourceRow (event : DressedEvent) (n : PhysicalMomentum) (mu : Fin 4) : Fin 289→Parameters :=
  commonDenominator event n • ((commonClearedPencil event n).adjugate.transpose*ᵥ
    fun i => MvPolynomial.C (emInsertion i mu))

def fullClockEMRow (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) : Fin 289→(ℂ[X])[X] :=
  fun i => frequencyClockSlice eps (commonEMSourceRow event n mu i)

def zeroClockEMRow (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) : Fin 289→ℂ[X] :=
  fun i => (fullClockEMRow event eps n mu i).coeff (frequencyClockOrder event eps n)

theorem actual_common_em_row_equation (event : DressedEvent) (n : PhysicalMomentum) (mu : Fin 4) :
    (commonClearedPencil event n).transpose*ᵥcommonEMSourceRow event n mu=
      commonDeterminant event n • (commonDenominator event n • fun i => MvPolynomial.C (emInsertion i mu)) := by
  unfold commonEMSourceRow commonDeterminant
  rw [Matrix.mulVec_smul,Matrix.mulVec_mulVec,←Matrix.transpose_mul,Matrix.adjugate_mul,
    Matrix.transpose_smul,Matrix.transpose_one,Matrix.smul_mulVec,Matrix.one_mulVec]
  exact smul_comm _ _ _

private theorem transpose_observer {R ι : Type*} [CommSemiring R] [Fintype ι]
    (H : Matrix ι ι R) (d s : ι→R) : dotProduct s (H.transpose*ᵥd)=dotProduct d (H*ᵥs) := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_common_em_row_observer (event : DressedEvent) (n : PhysicalMomentum) (mu nu : Fin 4) :
    dotProduct (fun i => MvPolynomial.C (emInsertion i nu)) (commonEMSourceRow event n mu)=
      commonEMTensorNumerator event n mu nu := by
  unfold commonEMSourceRow commonEMTensorNumerator
  rw [dotProduct_smul,smul_eq_mul,transpose_observer]

theorem actual_full_clock_em_row_equation (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) :
    (fullClockPencil event eps n).transpose*ᵥfullClockEMRow event eps n mu=
      frequencyClockDeterminant event eps n • (fullClockClearing event eps n •
        fun i => C (C (emInsertion i mu))) := by
  have mapped := congrArg (fun v : Fin 289→Parameters => fun i => frequencyClockSlice eps (v i))
    (actual_common_em_row_equation event n mu)
  have constant (c : ℂ) : frequencyClockSlice eps (MvPolynomial.C c)=C (C c) := by
    simp [frequencyClockSlice]
  funext i
  simpa only [fullClockEMRow,fullClockPencil,frequencyClockDeterminant,fullClockClearing,
    Matrix.mulVec,dotProduct,Matrix.transpose_apply,Matrix.map_apply,map_sum,map_mul,
    Pi.smul_apply,smul_eq_mul,constant] using congrFun mapped i

theorem actual_full_clock_em_row_observer (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) :
    dotProduct (fun i => C (C (emInsertion i nu))) (fullClockEMRow event eps n mu)=
      frequencyClockEMNumerator event eps n mu nu := by
  have mapped := congrArg (frequencyClockSlice eps) (actual_common_em_row_observer event n mu nu)
  have constant (c : ℂ) : frequencyClockSlice eps (MvPolynomial.C c)=C (C c) := by simp [frequencyClockSlice]
  simpa only [fullClockEMRow,frequencyClockEMNumerator,Matrix.map_apply,dotProduct,map_sum,map_mul,constant] using mapped

/-- The same mu/nu observable generates both the source detector row and its original source column. -/
theorem actual_zero_clock_em_row_observer (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) :
    dotProduct (fun i => C (emInsertion i nu)) (zeroClockEMRow event eps n mu)=
      zeroClockFrequencyEMNumerator event eps n mu nu := by
  have coefficient := congrArg (fun P : (ℂ[X])[X] => P.coeff (frequencyClockOrder event eps n))
    (actual_full_clock_em_row_observer event eps n mu nu)
  simpa only [zeroClockEMRow,zeroClockFrequencyEMNumerator,dotProduct,finsetSum_coeff,coeff_C_mul] using coefficient

private theorem factor_product_coefficient {R : Type*} [CommRing R]
    (P Q : R[X]) (m b : ℕ) (pFactor : X^m∣P) (qFactor : X^b∣Q) :
    (P*Q).coeff (m+b)=P.coeff m*Q.coeff b := by
  obtain ⟨p,rfl⟩ := pFactor
  obtain ⟨q,rfl⟩ := qFactor
  have product : (X^m*p)*(X^b*q)=X^(m+b)*(p*q) := by rw [pow_add];ring
  have cp : (X^m*p).coeff m=p.coeff 0 := by simpa only [zero_add] using coeff_X_pow_mul p m 0
  have cq : (X^b*q).coeff b=q.coeff 0 := by simpa only [zero_add] using coeff_X_pow_mul q b 0
  rw [product,cp,cq]
  simpa only [zero_add] using (coeff_X_pow_mul (p*q) (m+b) 0).trans (mul_coeff_zero p q)

/-- Every damping cross coefficient other than the actual H0/Lm pair is retained as source clock-chain feedback. -/
def sourceLeftClockChain (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) : Fin 289→ℂ[X] :=
  ∑p∈(Finset.HasAntidiagonal.antidiagonal (clearingClockOrder event eps n+frequencyClockOrder event eps n)).erase
      (clearingClockOrder event eps n,frequencyClockOrder event eps n),
    (fun i j => (fullClockPencil event eps n j i).coeff p.1)*ᵥ
      (fun j => (fullClockEMRow event eps n mu j).coeff p.2)

attribute [local irreducible] fullClockEMRow

private theorem row_coefficient_equation {ι : Type*} [Fintype ι]
    (H : Matrix ι ι (ℂ[X])[X]) (V : ι→(ℂ[X])[X]) (D d : (ℂ[X])[X]) (E : ι→ℂ) (k : ℕ)
    (equation : H.transpose*ᵥV=D • (d • fun i => C (C (E i)))) :
    (∑p∈Finset.HasAntidiagonal.antidiagonal k,
      (fun i j => (H j i).coeff p.1)*ᵥ(fun j => (V j).coeff p.2))=
      (D*d).coeff k • fun i => C (E i) := by
  funext i
  have paid := congrArg (fun P : (ℂ[X])[X] => P.coeff k) (congrFun equation i)
  have left : ((H.transpose*ᵥV) i).coeff k=
      ∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,(H j i).coeff p.1*(V j).coeff p.2 := by
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,finsetSum_coeff,coeff_mul]
  have right : ((D • (d • fun j => C (C (E j)))) i).coeff k=(D*d).coeff k*C (E i) := by
    change (D*(d*C (C (E i)))).coeff k=_
    rw [←mul_assoc,coeff_mul_C]
  rw [left,right] at paid
  simp only [Finset.sum_apply,Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  exact paid

/-- No finite-left-row or left-kernel premise is used: the original full damping chain supplies the missing terms. -/
theorem actual_zero_clock_em_left_chain (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) :
    (zeroClockPencil event eps n).transpose*ᵥzeroClockEMRow event eps n mu+
      sourceLeftClockChain event eps n mu=
      zeroClockFrequencyDenominator event eps n • (zeroClockClearing event eps n • fun i => C (emInsertion i mu)) := by
  let b := clearingClockOrder event eps n
  let m := frequencyClockOrder event eps n
  have coefficient :
      (∑p∈Finset.HasAntidiagonal.antidiagonal (b+m),
        (fun i j => (fullClockPencil event eps n j i).coeff p.1)*ᵥ
          (fun j => (fullClockEMRow event eps n mu j).coeff p.2))=
      zeroClockFrequencyDenominator event eps n • (zeroClockClearing event eps n • fun i => C (emInsertion i mu)) := by
    have paid := row_coefficient_equation (fullClockPencil event eps n) (fullClockEMRow event eps n mu)
      (frequencyClockDeterminant event eps n) (fullClockClearing event eps n) (fun i => emInsertion i mu)
      (b+m) (actual_full_clock_em_row_equation event eps n mu)
    have right := factor_product_coefficient (frequencyClockDeterminant event eps n)
      (fullClockClearing event eps n) m b (source_frequency_clock_factor event eps n)
      (source_clearing_clock_factor event eps n)
    rw [Nat.add_comm b m] at paid
    rw [right] at paid
    simpa only [zeroClockFrequencyDenominator,zeroClockClearing,smul_smul,smul_eq_mul,Nat.add_comm b m,b,m] using paid
  have member : (b,m)∈Finset.HasAntidiagonal.antidiagonal (b+m) := by simp
  rw [←Finset.sum_erase_add _ _ member] at coefficient
  have matrix : (zeroClockPencil event eps n).transpose=
      (fun i j => (fullClockPencil event eps n j i).coeff b) := rfl
  have row : zeroClockEMRow event eps n mu=(fun j => (fullClockEMRow event eps n mu j).coeff m) := rfl
  rw [matrix,row]
  unfold sourceLeftClockChain
  funext i
  have value := congrFun coefficient i
  simp only [Pi.add_apply] at value ⊢
  exact (add_comm _ _).trans value

end LowEnergy.GaussComposite.ActualDressedEMPolePairEnergy
