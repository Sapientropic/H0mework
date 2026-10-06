import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationRawTrace

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerTensor
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativeForm GaussLiveMomentum GaussCoreDifferential
open GaussScalarTransport GaussDensityCore PreparationScalarCoordinates
open PreparationVacuumLowerLeaves PreparationActualFactor PreparationVacuumDensityTrace
open scoped BigOperators ContDiff

-- The original70/36/6 directions with their actual quadratic action pairings.
abbrev SourcePair := ScalarIndex ⊕ ((LieIndex × (Fin 3 × Fin 3)) ⊕ (Fin 6 × Fin 6))

def sourceLeft (a : SourcePair) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  match a with
  | Sum.inl i => direction (scalarDirection i) z
  | Sum.inr (Sum.inl (a,i,_)) => direction (gaugeDirection i a) z
  | Sum.inr (Sum.inr (i,_)) => GaussCoframeCore.coframeDirection i

def sourceRight (a : SourcePair) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  match a with
  | Sum.inl i => direction (scalarDirection i) z
  | Sum.inr (Sum.inl (a,_,j)) => direction (gaugeDirection j a) z
  | Sum.inr (Sum.inr (_,j)) => GaussCoframeCore.coframeDirection j

def sourceCoefficient (a : SourcePair) (z : SourceCoordinateSlice) : ℝ :=
  match a with
  | Sum.inl _ => scalarWeight z/2
  | Sum.inr (Sum.inl (_,i,j)) => gaugeWeight z i j/2
  | Sum.inr (Sum.inr (i,j)) => GaussCoframeKinetic.coefficient i j z

def sourceSwap : SourcePair ≃ SourcePair where
  toFun := fun a => match a with
    | Sum.inl i => Sum.inl i
    | Sum.inr (Sum.inl (a,i,j)) => Sum.inr (Sum.inl (a,j,i))
    | Sum.inr (Sum.inr (i,j)) => Sum.inr (Sum.inr (j,i))
  invFun := fun a => match a with
    | Sum.inl i => Sum.inl i
    | Sum.inr (Sum.inl (a,i,j)) => Sum.inr (Sum.inl (a,j,i))
    | Sum.inr (Sum.inr (i,j)) => Sum.inr (Sum.inr (j,i))
  left_inv a := by rcases a with i|⟨a,i,j⟩|⟨i,j⟩ <;> rfl
  right_inv a := by rcases a with i|⟨a,i,j⟩|⟨i,j⟩ <;> rfl

theorem sourceSwap_left (a : SourcePair) (z : SourceCoordinateSlice) :
    sourceLeft (sourceSwap a) z=sourceRight a z := by
  rcases a with i|⟨a,i,j⟩|⟨i,j⟩ <;> rfl

theorem sourceSwap_right (a : SourcePair) (z : SourceCoordinateSlice) :
    sourceRight (sourceSwap a) z=sourceLeft a z := by
  rcases a with i|⟨a,i,j⟩|⟨i,j⟩ <;> rfl

theorem sourceSwap_coefficient (a : SourcePair) (z : SourceCoordinateSlice) :
    sourceCoefficient (sourceSwap a) z=sourceCoefficient a z := by
  rcases a with i|⟨a,i,j⟩|⟨i,j⟩
  · rfl
  · exact congrArg (fun c : ℝ => c/2) (gaugeWeight_symmetric z j i)
  · exact GaussCoframeKinetic.coefficient_symmetric j i z

theorem sourceLeft_smooth (a : SourcePair) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceLeft a) z.val := by
  rcases a with i|⟨a,i,j⟩|⟨i,j⟩
  · exact direction_smooth _ z
  · exact direction_smooth _ z
  · exact contDiffAt_const

theorem sourceRight_smooth (a : SourcePair) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceRight a) z.val := by
  rcases a with i|⟨a,i,j⟩|⟨i,j⟩
  · exact direction_smooth _ z
  · exact direction_smooth _ z
  · exact contDiffAt_const

theorem sourceCoefficient_smooth (a : SourcePair) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceCoefficient a) z.val := by
  rcases a with i|⟨a,i,j⟩|⟨i,j⟩
  · exact (scalarWeight_smooth z).div_const _
  · exact (gaugeWeight_smooth i j z).div_const _
  · exact GaussCoframeKinetic.coefficient_smooth i j z

def sourceTensor (i k : Fin 100) (z : SourceCoordinateSlice) : ℝ :=
  ∑ a : SourcePair,sourceCoefficient a z*
    rawCovector i (sourceLeft a z)*rawCovector k (sourceRight a z)

theorem sourceTensor_symmetric (i k : Fin 100) (z : SourceCoordinateSlice) :
    sourceTensor i k z=sourceTensor k i z := by
  unfold sourceTensor
  rw [←Equiv.sum_comp sourceSwap]
  simp only [sourceSwap_coefficient,sourceSwap_left,sourceSwap_right]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem originalPrincipal_pairs (z : SourceCoordinateSlice) (p : Cotangent) :
    nativePrincipal z p=∑ a : SourcePair,sourceCoefficient a z*p (sourceLeft a z)*p (sourceRight a z) := by
  have gauge : gaugeQuadratic z p=∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
      gaugeWeight z i j/2*p (direction (gaugeDirection i a) z)*p (direction (gaugeDirection j a) z) := by
    unfold gaugeQuadratic electricGram electricMomentum
    simp only [Finset.sum_div,Finset.mul_sum]
    have reorder : (∑ i : Fin 3,∑ j : Fin 3,∑ a : LieIndex,
        gaugeWeight z i j*(p (direction (gaugeDirection i a) z)*p (direction (gaugeDirection j a) z))/2)=
      ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
        gaugeWeight z i j*(p (direction (gaugeDirection i a) z)*p (direction (gaugeDirection j a) z))/2 := by
      calc
        _=∑ i : Fin 3,∑ a : LieIndex,∑ j : Fin 3,
          gaugeWeight z i j*(p (direction (gaugeDirection i a) z)*p (direction (gaugeDirection j a) z))/2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _=_ := by rw [Finset.sum_comm]
    rw [reorder]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,sourceCoefficient,sourceLeft,sourceRight]
  rw [nativePrincipal,gauge]
  unfold scalarQuadratic scalarWeight scalarNormSquare scalarMomentum coframeQuadratic coframeMomentum
  simp only [Finset.sum_div,Finset.mul_sum,pow_two]
  ring

theorem sourceTensor_original (i k : Fin 100) (z : SourceCoordinateSlice) :
    sourceTensor i k z=originalActionRawCoefficient i k z := by
  have polarized : originalActionRawCoefficient i k z=(sourceTensor i k z+sourceTensor k i z)/2 := by
    unfold originalActionRawCoefficient
    rw [originalPrincipal_pairs,originalPrincipal_pairs,originalPrincipal_pairs]
    unfold sourceTensor
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp only [add_apply]
    ring
  rw [polarized,sourceTensor_symmetric]
  ring

def sourceFlux (f : Profile) (z : SourceCoordinateSlice) (i : Fin 100) : ℂ :=
  ∑ a : SourcePair,(sourceCoefficient a z : ℂ)*
    (rawCovector i (sourceLeft a z) : ℂ)*fderiv ℝ f z (sourceRight a z)

def tensorFlux (f : Profile) (z : SourceCoordinateSlice) (i : Fin 100) : ℂ :=
  ∑ k : Fin 100,(sourceTensor i k z : ℂ)*fderiv ℝ f z (rawDirection k)

theorem originalFlux_tensor (f : Profile) (z : SourceCoordinateSlice) (i : Fin 100) :
    sourceFlux f z i=tensorFlux f z i := by
  unfold sourceFlux tensorFlux sourceTensor
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have read:=original_raw_read (sourceRight a z) (fderiv ℝ f z)
  rw [show (∑ k : Fin 100,(sourceCoefficient a z : ℂ)*
      (rawCovector i (sourceLeft a z) : ℂ)*
        (rawCovector k (sourceRight a z) : ℂ)*fderiv ℝ f z (rawDirection k))=
    (sourceCoefficient a z : ℂ)*(rawCovector i (sourceLeft a z) : ℂ)*
      (∑ k : Fin 100,(rawCovector k (sourceRight a z) : ℂ)*fderiv ℝ f z (rawDirection k)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring,read]

end LowEnergy.PreparationVacuumLowerTensor
