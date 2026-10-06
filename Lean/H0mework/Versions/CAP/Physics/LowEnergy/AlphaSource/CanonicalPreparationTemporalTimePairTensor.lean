import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalFourTermExtraction

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTemporalOrdering
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeForm GaussDensityCore
open PreparationScalarCoordinates CanonicalPreparationCore PreparationActualFactor
open PreparationVacuumLowerLeaves PreparationVacuumLowerTensor PreparationVacuumDensityTrace
open PreparationVacuumEnergyTail PreparationVacuumFactor PreparationVacuumWeylOrdering
open scoped BigOperators ContDiff Topology Matrix

def actualTimePairCoefficient (n : ℝ) (b : Fin 3 → ℝ) (a : SourcePair)
    (z : SourceCoordinateSlice) : ℝ :=
  match a with
  | Sum.inl _ => n/(sourceTime 0)*scalarWeight z/2
  | Sum.inr (Sum.inl (_,i,j)) => (originalElectricBlock n b z)⁻¹ i j/2
  | Sum.inr (Sum.inr (i,j)) => n/(sourceTime 0)*GaussCoframeKinetic.coefficient i j z

def actualTimePairPrincipal (n : ℝ) (b : Fin 3 → ℝ)
    (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  ∑ a : SourcePair,actualTimePairCoefficient n b a z*p (sourceLeft a z)*p (sourceRight a z)

def actualTimePairTensor (n : ℝ) (b : Fin 3 → ℝ) (i k : Fin 100)
    (z : SourceCoordinateSlice) : ℝ :=
  ∑ a : SourcePair,actualTimePairCoefficient n b a z*
    rawCovector i (sourceLeft a z)*rawCovector k (sourceRight a z)

theorem originalElectricInverse_symmetric (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart)
    (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) (i j : Fin 3) :
    (originalElectricBlock n b z.val)⁻¹ i j=(originalElectricBlock n b z.val)⁻¹ j i := by
  rw [originalElectricInverse_generated n b z timeNonzero timelike]
  have middle : (n^2 • (1 : Matrix (Fin 3) (Fin 3) ℝ)-Matrix.vecMulVec b b).transpose=
      n^2 • (1 : Matrix (Fin 3) (Fin 3) ℝ)-Matrix.vecMulVec b b := by
    ext r s
    simp only [Matrix.transpose_apply,Matrix.sub_apply,Matrix.smul_apply,
      Matrix.one_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    by_cases equal : r=s
    · subst s
      rfl
    · simp only [equal,Ne.symm equal,if_false]
      ring
  have symmetry : (generatedElectricInverse n b z.val).transpose=generatedElectricInverse n b z.val := by
    unfold generatedElectricInverse
    simp only [Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_transpose,middle,Matrix.mul_assoc]
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j i) symmetry

theorem actualTimePairCoefficient_swap (n : ℝ) (b : Fin 3 → ℝ) (a : SourcePair)
    (z : physicalChart) (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    actualTimePairCoefficient n b (sourceSwap a) z.val=actualTimePairCoefficient n b a z.val := by
  rcases a with i|⟨a,i,j⟩|⟨i,j⟩
  · rfl
  · exact congrArg (fun r : ℝ => r/2) (originalElectricInverse_symmetric n b z timeNonzero timelike j i)
  · change n/sourceTime 0*GaussCoframeKinetic.coefficient j i z.val=
      n/sourceTime 0*GaussCoframeKinetic.coefficient i j z.val
    rw [GaussCoframeKinetic.coefficient_symmetric j i]

theorem actualTimePairTensor_symmetric (n : ℝ) (b : Fin 3 → ℝ) (i k : Fin 100)
    (z : physicalChart) (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    actualTimePairTensor n b i k z.val=actualTimePairTensor n b k i z.val := by
  unfold actualTimePairTensor
  rw [←Equiv.sum_comp sourceSwap]
  simp only [actualTimePairCoefficient_swap n b _ z timeNonzero timelike,
    sourceSwap_left,sourceSwap_right]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem originalElectricPrincipal_generated (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart)
    (p : Cotangent) (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    (∑ i : Fin 3,∑ j : Fin 3,(originalElectricBlock n b z.val)⁻¹ i j*electricGram z.val p i j)/2=
      (n^2*T z.val p-∑ k : Fin 3,∑ l : Fin 3,b k*b l*S z.val p k l)/
        (2*n*(n^2-∑ r : Fin 3,b r^2)) := by
  rw [originalElectricInverse_generated n b z timeNonzero timelike]
  unfold generatedElectricInverse T S
  simp only [Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.sub_apply,Matrix.vecMulVec_apply,Matrix.one_apply,smul_eq_mul]
  simp [Fin.sum_univ_three]
  have hd : n^2-(b 0^2+b 1^2+b 2^2)≠0 := by simpa only [Fin.sum_univ_three] using timelike
  field_simp [timeNonzero,hd]
  ring

theorem actualTimePairPrincipal_original (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart)
    (p : Cotangent) (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    actualTimePairPrincipal n b z.val p=timelikePrincipal z.val p n b := by
  have gauge : (∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
      (originalElectricBlock n b z.val)⁻¹ i j/2*
        p (sourceLeft (Sum.inr (Sum.inl (a,i,j))) z.val)*
        p (sourceRight (Sum.inr (Sum.inl (a,i,j))) z.val))=
      (∑ i : Fin 3,∑ j : Fin 3,(originalElectricBlock n b z.val)⁻¹ i j*electricGram z.val p i j)/2 := by
    unfold electricGram electricMomentum sourceLeft sourceRight
    simp only [Finset.sum_div,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    ring
  have scalar : (∑ a : ScalarIndex,n/sourceTime 0*scalarWeight z.val/2*
      p (GaussCoreDifferential.direction (scalarDirection a) z.val)*
        p (GaussCoreDifferential.direction (scalarDirection a) z.val))=
      (n/sourceTime 0)*scalarQuadratic z.val p := by
    unfold scalarQuadratic scalarNormSquare scalarMomentum
    simp only [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have coframe : (∑ i : Fin 6,∑ j : Fin 6,n/sourceTime 0*GaussCoframeKinetic.coefficient i j z.val*
      p (GaussCoframeCore.coframeDirection i)*p (GaussCoframeCore.coframeDirection j))=
      (n/sourceTime 0)*coframeQuadratic z.val p := by
    unfold coframeQuadratic coframeMomentum
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have nongauge : (n/sourceTime 0)*scalarQuadratic z.val p+
      (n/sourceTime 0)*coframeQuadratic z.val p=n*A z.val p := by
    unfold scalarQuadratic scalarWeight A
    have nv := (volume_pos z).ne'
    have nn := source_time_nonzero
    field_simp
    ring
  have contraction : (∑ k : Fin 3,∑ l : Fin 3,b k*b l*S z.val p k l)=
      ∑ k : Fin 3,∑ l : Fin 3,b k*S z.val p k l*b l := by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  unfold actualTimePairPrincipal
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,actualTimePairCoefficient]
  rw [gauge,originalElectricPrincipal_generated n b z p timeNonzero timelike]
  simp only [sourceLeft,sourceRight]
  rw [scalar,coframe,contraction]
  rw [show (n/sourceTime 0)*scalarQuadratic z.val p+
      ((n^2*T z.val p-∑ k : Fin 3,∑ l : Fin 3,b k*S z.val p k l*b l)/
        (2*n*(n^2-∑ r : Fin 3,b r^2))+(n/sourceTime 0)*coframeQuadratic z.val p)=
    ((n/sourceTime 0)*scalarQuadratic z.val p+(n/sourceTime 0)*coframeQuadratic z.val p)+
      (n^2*T z.val p-∑ k : Fin 3,∑ l : Fin 3,b k*S z.val p k l*b l)/
        (2*n*(n^2-∑ r : Fin 3,b r^2)) by ring,nongauge]
  rfl

theorem actualTimePairTensor_polarization (n : ℝ) (b : Fin 3 → ℝ) (i k : Fin 100)
    (z : physicalChart) (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    actualTimePairTensor n b i k z.val=
      (actualTimePairPrincipal n b z.val (rawCovector i+rawCovector k)-
        actualTimePairPrincipal n b z.val (rawCovector i)-
          actualTimePairPrincipal n b z.val (rawCovector k))/2 := by
  have polarized : (actualTimePairPrincipal n b z.val (rawCovector i+rawCovector k)-
        actualTimePairPrincipal n b z.val (rawCovector i)-
          actualTimePairPrincipal n b z.val (rawCovector k))/2=
      (actualTimePairTensor n b i k z.val+actualTimePairTensor n b k i z.val)/2 := by
    unfold actualTimePairPrincipal actualTimePairTensor
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp only [add_apply]
    ring
  rw [polarized,actualTimePairTensor_symmetric n b i k z timeNonzero timelike]
  ring

theorem actualTimePairTensor_extraction (n : ℝ) (b : Fin 3 → ℝ) (i k : Fin 100)
    (z : physicalChart) (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    (actualTimePairTensor n b i k z.val : ℂ)=timeTensor n b i k z.val := by
  rw [actualTimePairTensor_polarization n b i k z timeNonzero timelike]
  simp only [actualTimePairPrincipal_original n b z _ timeNonzero timelike]
  exact (originalTimeTensor_polarization n b i k z.val timeNonzero timelike).symm

end LowEnergy.PreparationVacuumTemporalOrdering
