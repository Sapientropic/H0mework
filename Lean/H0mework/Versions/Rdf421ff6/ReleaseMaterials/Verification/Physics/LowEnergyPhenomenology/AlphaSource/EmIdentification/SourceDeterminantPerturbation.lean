import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualQuantumBinaryReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMTensorSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceQuantumCoefficientErrorOwn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet
open GaussComposite.ActualDressedFullCoulomb GaussComposite.ActualDressedSylvester
open GaussComposite.ActualDressedFrequencyHalf GaussComposite.ActualDressedUniformMaterialCoefficients
open GaussComposite.ActualDressedEMTensorClock ActualMixedNoetherTimePriceOwn
open scoped BigOperators Matrix

private theorem product_error {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℂ)
    (M E : ℝ) (m0 : 0 ≤ M) (e0 : 0 ≤ E)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ M) (he : ∀ i ∈ s, ‖a i-b i‖ ≤ E) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ (M+E)^s.card-M^s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s absent ih =>
    have bi := hb i (Finset.mem_insert_self i s)
    have ei := he i (Finset.mem_insert_self i s)
    have old := ih (fun j hj => hb j (Finset.mem_insert_of_mem hj))
      (fun j hj => he j (Finset.mem_insert_of_mem hj))
    have ai : ‖a i‖ ≤ M+E := by
      calc
        ‖a i‖ = ‖a i-b i+b i‖ := by congr 1; ring
        _ ≤ ‖a i-b i‖+‖b i‖ := norm_add_le _ _
        _ ≤ E+M := add_le_add ei bi
        _ = M+E := add_comm _ _
    have bp : ‖∏ j ∈ s,b j‖ ≤ M^s.card := by
      exact (Finset.norm_prod_le s b).trans (by
        simpa using Finset.prod_le_prod (fun j _ => norm_nonneg (b j))
          (fun j hj => hb j (Finset.mem_insert_of_mem hj)))
    have difference : a i*(∏ j ∈ s,a j)-b i*(∏ j ∈ s,b j)=
        a i*((∏ j ∈ s,a j)-(∏ j ∈ s,b j))+(a i-b i)*(∏ j ∈ s,b j) := by ring
    rw [Finset.prod_insert absent,Finset.prod_insert absent,difference,Finset.card_insert_of_notMem absent]
    calc
      _ ≤ ‖a i‖*‖(∏ j ∈ s,a j)-(∏ j ∈ s,b j)‖+‖a i-b i‖*‖∏ j ∈ s,b j‖ := by
        simpa only [norm_mul] using norm_add_le (a i*((∏ j ∈ s,a j)-(∏ j ∈ s,b j))) ((a i-b i)*(∏ j ∈ s,b j))
      _ ≤ (M+E)*((M+E)^s.card-M^s.card)+E*M^s.card :=
        add_le_add (mul_le_mul ai old (norm_nonneg _) (by positivity))
          (mul_le_mul ei bp (norm_nonneg _) e0)
      _ = (M+E)^(s.card+1)-M^(s.card+1) := by rw [pow_succ,pow_succ]; ring

private theorem determinant_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (M E : ℝ) (m0 : 0 ≤ M) (e0 : 0 ≤ E)
    (hb : ∀ i j, ‖B i j‖ ≤ M) (he : ∀ i j, ‖A i j-B i j‖ ≤ E) :
    ‖A.det-B.det‖ ≤ (Fintype.card (Equiv.Perm ι) : ℝ)*((M+E)^Fintype.card ι-M^Fintype.card ι) := by
  rw [Matrix.det_apply,Matrix.det_apply,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p : Equiv.Perm ι, ‖Equiv.Perm.sign p • (∏ i,A (p i) i)-Equiv.Perm.sign p • (∏ i,B (p i) i)‖ := norm_sum_le _ _
    _ = ∑ p : Equiv.Perm ι, ‖(∏ i,A (p i) i)-(∏ i,B (p i) i)‖ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [←smul_sub,norm_units_zsmul]
    _ ≤ ∑ _p : Equiv.Perm ι, ((M+E)^Fintype.card ι-M^Fintype.card ι) := by
      apply Finset.sum_le_sum
      intro p _
      exact product_error Finset.univ _ _ M E m0 e0 (fun i _ => hb (p i) i) (fun i _ => he (p i) i)
    _ = _ := by simp; ring

-- Only the original same-event quantum integral is replaced by its paid source window.
def sourceStaticCommonDenominator (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  MvPolynomial.eval (irValues eps sigma 0) (commonDenominator event n)

def sourceStaticClearedWindow (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  sourceStaticCommonDenominator event eps sigma n •
    (GaussComposite.ActualEMAction.emOriginalJacobi (frequencyRay eps 0 n)-
      (sigma : ℂ) • originalQuantumBinaryWindow event ((eps^2 : ℝ) • n) (sigma : ℂ) bits)

def sourceStaticEntryError (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (i j : Fin 289) : ℝ :=
  ‖sourceStaticCommonDenominator event eps sigma n‖*|sigma| *
    ((896*sourceCompleteCubicNoetherPrice event ((eps^2 : ℝ) • n) (fieldUnit i) (fieldUnit j)/sigma^4)*(1/2 : ℝ)^bits)

def sourceClearedErrorMass (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ) : ℝ :=
  ∑ i,∑ j,max 0 (sourceStaticEntryError event eps sigma n bits i j)

def sourceClearedWindowMass (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ) : ℝ :=
  ∑ i,∑ j,‖sourceStaticClearedWindow event eps sigma n bits i j‖

def sourceClearedDeterminantError (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ) (order : ℕ) : ℝ :=
  (Nat.factorial order : ℝ)*((sourceClearedWindowMass event eps sigma n bits+sourceClearedErrorMass event eps sigma n bits)^order-
    (sourceClearedWindowMass event eps sigma n bits)^order)

attribute [local irreducible] dressedStaticPolarization frequencyHalfPolarization commonClearedPencil
  commonDenominator sourceStaticCommonDenominator sourceStaticClearedWindow
  originalQuantumBinaryWindow sourceStaticEntryError sourceClearedErrorMass sourceClearedWindowMass

private theorem static_original_pi (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) :
    frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps 0 n)
      (dampedFourierClock (sourceFrequency eps 0) sigma)=dressedStaticPolarization event ((eps^2 : ℝ) • n) (sigma : ℂ) := by
  have clock : dampedFourierClock (sourceFrequency eps 0) sigma=(sigma : ℂ) := by
    simp [dampedFourierClock,sourceFrequency]
  rw [clock]
  funext i j
  unfold frequencyHalfPolarization
  exact dressed_static_polarization_actual event ((eps^2 : ℝ) • n)
    (frequencyRay eps 0 n) (by simp [frequencyRay,physicalFrequencyMomentum]) (sigma : ℂ) positive i j

 theorem sourceStaticClearedWindow_entry_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) (i j : Fin 289) :
    ‖(commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma 0)) i j-
      sourceStaticClearedWindow event eps sigma n bits i j‖ ≤ sourceStaticEntryError event eps sigma n bits i j := by
  have cleared := actual_common_ir_pencil_clear event n eps sigma 0 positive
  have same := GaussComposite.ActualDressedFrequencyHalf.damped_source_sheet_response event eps 0 sigma n positive
  rw [same,static_original_pi event eps sigma n positive] at cleared
  have difference : (commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma 0)) i j-
      sourceStaticClearedWindow event eps sigma n bits i j=
    -(sourceStaticCommonDenominator event eps sigma n*(sigma : ℂ)*
      (dressedStaticPolarization event ((eps^2 : ℝ) • n) (sigma : ℂ) i j-originalQuantumBinaryWindow event ((eps^2 : ℝ) • n) (sigma : ℂ) bits i j)) := by
    rw [←cleared]
    unfold sourceStaticClearedWindow sourceStaticCommonDenominator
    simp only [Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
    ring
  rw [difference,norm_neg,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  unfold sourceStaticEntryError
  exact mul_le_mul_of_nonneg_left (actualFullQuantum_binary_source_error event ((eps^2 : ℝ) • n)
    (sigma : ℂ) positive small bits i j) (by positivity)

private theorem entry_le_mass (a : Fin 289 → Fin 289 → ℝ) (positive : ∀ i j,0 ≤ a i j) (i j : Fin 289) :
    a i j ≤ ∑ r,∑ s,a r s :=
  (Finset.single_le_sum (fun k _ => positive i k) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun r _ => Finset.sum_nonneg (fun s _ => positive r s)) (Finset.mem_univ i))

private theorem source_mass_data (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ) :
    0 ≤ sourceClearedWindowMass event eps sigma n bits ∧ 0 ≤ sourceClearedErrorMass event eps sigma n bits ∧
    (∀ i j,‖sourceStaticClearedWindow event eps sigma n bits i j‖ ≤ sourceClearedWindowMass event eps sigma n bits) ∧
    (∀ i j,sourceStaticEntryError event eps sigma n bits i j ≤ sourceClearedErrorMass event eps sigma n bits) := by
  unfold sourceClearedWindowMass sourceClearedErrorMass
  refine ⟨Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>norm_nonneg _)),
    Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>le_max_left _ _)),?_,?_⟩
  · exact fun i j=>entry_le_mass _ (fun r s=>norm_nonneg _) i j
  · intro i j
    exact (le_max_right _ _).trans (entry_le_mass _ (fun r s=>le_max_left _ _) i j)

theorem actual_source_symbolic_denominator_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) :
    ‖MvPolynomial.eval (irValues eps sigma 0) (GaussComposite.ActualDressedVisiblePole.commonDeterminant event n)-
      (sourceStaticClearedWindow event eps sigma n bits).det‖ ≤ sourceClearedDeterminantError event eps sigma n bits 289 := by
  rw [GaussComposite.ActualDressedVisiblePole.common_determinant_eval]
  have mass:=source_mass_data event eps sigma n bits
  have paid:=determinant_error ((commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma 0)))
    (sourceStaticClearedWindow event eps sigma n bits) _ _ mass.1 mass.2.1 mass.2.2.1
    (fun i j=>(sourceStaticClearedWindow_entry_error event eps sigma n positive small bits i j).trans (mass.2.2.2 i j))
  simpa only [Fintype.card_perm,Fintype.card_fin,sourceClearedDeterminantError] using paid

theorem actual_source_adjugate_entry_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) (i j : Fin 289) :
    ‖((commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma 0))).adjugate i j-
      (sourceStaticClearedWindow event eps sigma n bits).adjugate i j‖ ≤ sourceClearedDeterminantError event eps sigma n bits 288 := by
  have mass:=source_mass_data event eps sigma n bits
  have paid:=determinant_error
    (((commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma 0))).submatrix j.succAbove i.succAbove)
    ((sourceStaticClearedWindow event eps sigma n bits).submatrix j.succAbove i.succAbove) _ _ mass.1 mass.2.1
    (fun r s=>mass.2.2.1 _ _)
    (fun r s=>(sourceStaticClearedWindow_entry_error event eps sigma n positive small bits _ _).trans (mass.2.2.2 _ _))
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,Matrix.adjugate_fin_succ_eq_det_submatrix,←mul_sub,norm_mul]
  have sign : ‖(-1 : ℂ)^(j+i : ℕ)‖=1 := by simp
  rw [sign,one_mul]
  simpa only [Fintype.card_perm,Fintype.card_fin,sourceClearedDeterminantError] using paid

end LowEnergy.ActualSourceQuantumCoefficientErrorOwn
