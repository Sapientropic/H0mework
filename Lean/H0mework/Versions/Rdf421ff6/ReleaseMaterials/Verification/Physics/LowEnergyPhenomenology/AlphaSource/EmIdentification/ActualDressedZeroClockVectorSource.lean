import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualDressedZeroClockFrequencyOwn.ActualDressedZeroClockPropagation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedZeroClockVector
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open LowEnergy.GaussComposite.ActualDressedPoleWardMode LowEnergy.ActualDressedPoleWardMode
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedZeroClockFrequency
open ActualCompositeFieldCurrent
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator commonDeterminant sourceCommonVector

def fullClockPencil (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) (ℂ[X])[X] := (commonClearedPencil event n).map (frequencyClockSlice eps)

def fullClockClearing (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  frequencyClockSlice eps (commonDenominator event n)

def fullClockSourceVector (event : DressedEvent) (eps : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) : Fin 289 → (ℂ[X])[X] :=
  fun i => frequencyClockSlice eps (sourceCommonVector event n ps sL sR i)

def zeroClockSourceVector (event : DressedEvent) (eps : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) : Fin 289 → ℂ[X] :=
  fun i => (fullClockSourceVector event eps n ps sL sR i).coeff (frequencyClockOrder event eps n)

def zeroClockVectorFraction (event : DressedEvent) (eps : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) : Fin 289 → RatFunc ℂ :=
  fun i => readFraction (zeroClockSourceVector event eps n ps sL sR i)
    (zeroClockFrequencyDenominator event eps n)

def clearingClockOrder (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℕ :=
  (fullClockClearing event eps n).natTrailingDegree

def zeroClockClearing (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℂ[X] :=
  (fullClockClearing event eps n).coeff (clearingClockOrder event eps n)

def zeroClockPencil (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ[X] :=
  fun i j => (fullClockPencil event eps n i j).coeff (clearingClockOrder event eps n)

def FullVectorClockFinite (event : DressedEvent) (eps : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) : Prop :=
  ∀i, X^frequencyClockOrder event eps n∣fullClockSourceVector event eps n ps sL sR i

def PencilClockBalanced (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Prop :=
  ∀i j, X^clearingClockOrder event eps n∣fullClockPencil event eps n i j

private theorem mapped_equation {α β ι : Type*} [CommRing α] [CommRing β] [Fintype ι]
    (f : α →+* β) (H : Matrix ι ι α) (V F : ι → α) (D : α) (paid : H*ᵥV=D • F) :
    H.map f*ᵥ(fun i => f (V i))=f D • (fun i => f (F i)) := by
  have mapped := congrArg (fun v : ι → α => fun i => f (v i)) paid
  funext i
  simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,map_sum,map_mul,
    Pi.smul_apply,smul_eq_mul] using congrFun mapped i

/-- The whole original adjugate/source relation is retained before any clock coefficient. -/
theorem actual_full_clock_equation (event : DressedEvent) (eps : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) :
    fullClockPencil event eps n*ᵥfullClockSourceVector event eps n ps sL sR=
      frequencyClockDeterminant event eps n • (fullClockClearing event eps n •
        fun i => Polynomial.C (Polynomial.C (ActualCompositeFieldCurrent.compositeCurrent ps sL sR i))) := by
  have paid := mapped_equation (frequencyClockSlice eps) _ _ _ _
    (actual_common_full_equation event n ps sL sR)
  have constant (c : ℂ) : frequencyClockSlice eps (MvPolynomial.C c)=Polynomial.C (Polynomial.C c) := by
    simp [frequencyClockSlice]
  unfold fullClockPencil fullClockSourceVector frequencyClockDeterminant fullClockClearing
  funext i
  simpa only [Pi.smul_apply,smul_eq_mul,map_mul,constant] using congrFun paid i

private theorem observer_coeff {ι : Type*} [Fintype ι] (fd : ι → ℂ)
    (V : ι → (ℂ[X])[X]) (k : ℕ) :
    (dotProduct (fun i => Polynomial.C (Polynomial.C (fd i))) V).coeff k=
      dotProduct (fun i => Polynomial.C (fd i)) (fun i => (V i).coeff k) := by
  simp only [dotProduct,finsetSum_coeff,coeff_C_mul]

theorem actual_zero_clock_vector_observer (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    dotProduct (fun i => Polynomial.C (ActualCompositeFieldCurrent.compositeCurrent pd dL dR i))
      (zeroClockSourceVector event eps n ps sL sR)=zeroClockFrequencyProbeNumerator event eps n pd ps dL dR sL sR := by
  have mapped := congrArg (frequencyClockSlice eps) (actual_common_observer_vector event n pd ps dL dR sL sR)
  have constant (c : ℂ) : frequencyClockSlice eps (MvPolynomial.C c)=Polynomial.C (Polynomial.C c) := by
    simp [frequencyClockSlice]
  have observed : dotProduct (fun i => Polynomial.C (Polynomial.C (ActualCompositeFieldCurrent.compositeCurrent pd dL dR i)))
      (fullClockSourceVector event eps n ps sL sR)=frequencyClockProbeNumerator event eps n pd ps dL dR sL sR := by
    simpa only [fullClockSourceVector,frequencyClockProbeNumerator,dotProduct,map_sum,map_mul,constant] using mapped
  have coefficient := congrArg (fun P : (ℂ[X])[X] => P.coeff (frequencyClockOrder event eps n)) observed
  exact (observer_coeff _ _ _).symm.trans coefficient

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

/-- Every clock cross coefficient stays in the original full 289-row module identity. -/
theorem actual_full_clock_coefficient_equation (event : DressedEvent) (eps : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg) (k : ℕ) :
    (∑a ∈ Finset.HasAntidiagonal.antidiagonal k,
      (fun i j => (fullClockPencil event eps n i j).coeff a.1)*ᵥ
        (fun j => (fullClockSourceVector event eps n ps sL sR j).coeff a.2))=
      (frequencyClockDeterminant event eps n*fullClockClearing event eps n).coeff k •
        fun i => Polynomial.C (ActualCompositeFieldCurrent.compositeCurrent ps sL sR i) :=
  equation_coeff _ _ _ _ _ (actual_full_clock_equation event eps n ps sL sR) k

end LowEnergy.GaussComposite.ActualDressedZeroClockVector
