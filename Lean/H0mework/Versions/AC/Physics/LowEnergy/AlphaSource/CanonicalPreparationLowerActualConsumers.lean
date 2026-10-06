import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerRhoCorrectionJets

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerCorrections
open PreparationVacuumRationalW PreparationVacuumPrincipalBudget PreparationVacuumDensityBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumCentralBudget
open PreparationVacuumEngineBudget PreparationVacuumEngineSmooth PreparationVacuumClockSymbol
open PreparationVacuumWeylOrdering PreparationVacuumLowerLeaves PreparationVacuumEnergyTail
open PreparationScalarCoordinates PreparationActualFactor PreparationCoordinates
open GaussHistoryHilbert GaussCoreDifferential SourceQuantumConfigurationHilbert
open scoped BigOperators ContDiff Topology Matrix

abbrev NativeTensor := Configuration → Matrix (Fin 94) (Fin 94) ℝ

def partP (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) : RectSymbol 94 94 := if s=0 then scalarP n b else gaugeP n b

def partArray (s : Fin 2) : ArrayBound := if s=0 then scalarPArray else gaugePArray

def nativePart (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) : NativeTensor := fun z => partP s n b (fullCoordinates z,0)

def nativeHalf (F : NativeTensor) (z : Configuration) : ℝ :=
  ∑ i : Fin 94,∑ k : Fin 94,
    (F z i k*(rawHalfLog (Fin.natAdd 6 i) z*rawHalfLog (Fin.natAdd 6 k) z+
      fderiv ℝ (rawHalfLog (Fin.natAdd 6 k)) z (rawDirection (Fin.natAdd 6 i)))+
    fderiv ℝ (fun w => F w i k) z (rawDirection (Fin.natAdd 6 i))*rawHalfLog (Fin.natAdd 6 k) z)

def nativeQuarter (F : NativeTensor) (z : Configuration) : ℝ := (1/4 : ℝ)*
  ∑ i : Fin 94,∑ k : Fin 94,fderiv ℝ
    (fun w => fderiv ℝ (fun t => F t i k) w (rawDirection (Fin.natAdd 6 k))) z (rawDirection (Fin.natAdd 6 i))

def originalRhoHalfLeaf (j : Fin 13) : Configuration → ℝ :=
  nativeHalf (fun z i k => rawPrincipalCoefficient j (Fin.natAdd 6 i) (Fin.natAdd 6 k) z)

def originalRhoQuarterLeaf (j : Fin 13) : Configuration → ℝ :=
  nativeQuarter (fun z i k => rawPrincipalCoefficient j (Fin.natAdd 6 i) (Fin.natAdd 6 k) z)

def originalRhoTimeHalf (n : ℝ) (b : Fin 3 → ℝ) : Symbol := fun x =>
  ∑ j : Fin 13,originalTemporalWeights n b j*originalRhoHalfLeaf j (fullCoordinates.symm x.1)

def originalRhoTimeQuarter (n : ℝ) (b : Fin 3 → ℝ) : Symbol := fun x =>
  ∑ j : Fin 13,originalTemporalWeights n b j*originalRhoQuarterLeaf j (fullCoordinates.symm x.1)

theorem partP_smooth (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) : RectSmooth (partP s n b) := by
  have scalar := matrix_product_smooth
    (fun x => (scalarCoefficients x.1)ᵀ*scalarW n b x) (fun x => scalarCoefficients x.1)
    (matrix_product_smooth _ _ (fun i j => PreparationVacuumPrincipalBudget.sourceCoefficient_smooth _ i)
      (scalarW_smooth n b time)) (fun i j => PreparationVacuumPrincipalBudget.sourceCoefficient_smooth _ j)
  have gauge := matrix_product_smooth
    (fun x => (gaugeCoefficients x.1)ᵀ*gaugeW n b x) (fun x => gaugeCoefficients x.1)
    (matrix_product_smooth _ _ (fun i j => PreparationVacuumPrincipalBudget.sourceCoefficient_smooth _ i)
      (gaugeW_smooth n b time)) (fun i j => PreparationVacuumPrincipalBudget.sourceCoefficient_smooth _ j)
  fin_cases s <;> intro i k
  · exact contDiffOn_const.mul (scalar i k)
  · exact contDiffOn_const.mul (gauge i k)

theorem partArray_nonnegative (s : Fin 2) : ∀ m,0 ≤ partArray s m := by
  have sw : ∀ m,0 ≤ scalarWArray m := fun m => by unfold scalarWArray; positivity
  have gw : ∀ m,0 ≤ gaugeWArray m := fun m => by unfold gaugeWArray; positivity
  fin_cases s
  · intro m
    exact mul_nonneg (by norm_num) (productArray_nonnegative _ _
      (productArray_nonnegative _ _ scalarFactor_nonnegative sw) scalarFactor_nonnegative m)
  · intro m
    exact mul_nonneg (by norm_num) (productArray_nonnegative _ _
      (productArray_nonnegative _ _ gaugeFactor_nonnegative gw) gaugeFactor_nonnegative m)

theorem partP_budget (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (inputs : CoefficientInputs x M) : MatrixBound (partP s n b) M (partArray s) x := by
  fin_cases s
  · exact actual_scalarP_budget n b time M x hx box inputs
  · exact actual_gaugeP_budget n b time M x hx box inputs

theorem nativePart_pullback (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) (x : Phase) :
    nativePart s n b (fullCoordinates.symm x.1)=partP s n b x := by
  unfold nativePart
  rw [ContinuousLinearEquiv.apply_symm_apply]
  fin_cases s <;> rfl

private theorem native_matrix_product {a c d : ℕ}
    (A : Configuration → Matrix (Fin a) (Fin c) ℝ) (B : Configuration → Matrix (Fin c) (Fin d) ℝ)
    (z : Configuration) (asmooth : ∀ i k,ContDiffAt ℝ ∞ (fun w => A w i k) z)
    (bsmooth : ∀ k j,ContDiffAt ℝ ∞ (fun w => B w k j) z) (i j) :
    ContDiffAt ℝ ∞ (fun w => (A w*B w) i j) z := by
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum (fun k _ => (asmooth i k).mul (bsmooth k j))

private theorem native_coefficient_smooth (v : GaussLiveMomentum.Ambient) (k : Fin 94) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => PreparationVacuumPrincipalBudget.sourceCoefficient (fullCoordinates w) v k) z.val := by
  have same : (fun w => PreparationVacuumPrincipalBudget.sourceCoefficient (fullCoordinates w) v k)=
      (fun w => fullCoordinates (direction v w) (Fin.natAdd 6 k)) := by
    funext w
    unfold PreparationVacuumPrincipalBudget.sourceCoefficient
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [same]
  exact (ContinuousLinearMap.proj (Fin.natAdd 6 k) : (Fin 100 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp z.val
    (fullCoordinates.contDiff.contDiffAt.comp z.val (direction_smooth v z))

theorem nativePart_smooth (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (i k : Fin 94) (z : physicalChart) : ContDiffAt ℝ ∞ (fun w => nativePart s n b w i k) z.val := by
  have scalar (a c : Fin 70) : ContDiffAt ℝ ∞ (fun w => scalarW n b (fullCoordinates w,0) a c) z.val := by
    by_cases eq : a=c
    · subst c
      have smooth : ContDiffAt ℝ ∞ (fun w => -n*(GaussNativeEnergy.volume w)⁻¹) z.val :=
        contDiffAt_const.mul (GaussNativeEnergy.volume_smooth.contDiffAt.inv (GaussNativeEnergy.volume_pos z).ne')
      apply smooth.congr_of_eventuallyEq
      filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
      simpa [scalarW,PreparationVacuumRationalW.scalarWeight] using
        scalar_weight_formula n b ⟨w,hw⟩ (time_positive n b time).1.ne'
    · simp only [scalarW,Matrix.diagonal_apply_ne _ eq]
      exact contDiffAt_const
  have gauge (a c : Fin 36) : ContDiffAt ℝ ∞ (fun w => gaugeW n b (fullCoordinates w,0) a c) z.val := by
    have same : (fun w => gaugeW n b (fullCoordinates w,0) a c)=
        (fun w => (originalElectricBlock n b w)⁻¹ (spatialRow a) (spatialRow c)*rawGramInverse (nativeRow a) (nativeRow c)) := by
      funext w
      simp [gaugeW,actualElectric]
    rw [same]
    exact (PreparationVacuumTemporalOrdering.actualElectricInverse_smooth n b (time_positive n b time).1.ne'
      (time_positive n b time).2.ne' _ _ z).mul contDiffAt_const
  fin_cases s
  · exact contDiffAt_const.mul (native_matrix_product _ _ z.val
      (native_matrix_product _ _ z.val (fun a c => native_coefficient_smooth _ a z) scalar)
      (fun a c => native_coefficient_smooth _ c z) i k)
  · exact contDiffAt_const.mul (native_matrix_product _ _ z.val
      (native_matrix_product _ _ z.val (fun a c => native_coefficient_smooth _ a z) gauge)
      (fun a c => native_coefficient_smooth _ c z) i k)

private def configurationMap : Phase →L[ℝ] Configuration :=
  fullCoordinates.symm.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _)

private theorem native_derivative (f : Configuration → ℝ) (x : Phase) (i : Fin 94)
    (smooth : ContDiffAt ℝ ∞ f (fullCoordinates.symm x.1)) :
    fderiv ℝ (fun y => f (fullCoordinates.symm y.1)) x (qDirection (Fin.natAdd 6 i))=
      fderiv ℝ f (fullCoordinates.symm x.1) (rawDirection (Fin.natAdd 6 i)) := by
  have derivative := (smooth.differentiableAt (by simp)).hasFDerivAt.comp x configurationMap.hasFDerivAt
  change fderiv ℝ (f∘configurationMap) x (qDirection (Fin.natAdd 6 i))=_
  rw [derivative.fderiv]
  rfl

theorem nativePart_D (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (i k r : Fin 94) (x : Phase) (physical : x∈originalPhysicalPhase) :
    fderiv ℝ (fun w => nativePart s n b w i k) (fullCoordinates.symm x.1) (rawDirection (Fin.natAdd 6 r))=
      dq r (fun y => partP s n b y i k) x := by
  have derivative := native_derivative (fun w => nativePart s n b w i k) x r (nativePart_smooth s n b time i k ⟨_,physical⟩)
  have same : (fun y => nativePart s n b (fullCoordinates.symm y.1) i k)=(fun y => partP s n b y i k) := by
    funext y
    exact congrArg (fun M : Matrix (Fin 94) (Fin 94) ℝ => M i k) (nativePart_pullback s n b y)
  rw [same] at derivative
  exact derivative.symm

theorem nativePart_DD (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (i k r t : Fin 94) (x : Phase) (physical : x∈originalPhysicalPhase) :
    fderiv ℝ (fun w => fderiv ℝ (fun z => nativePart s n b z i k) w (rawDirection (Fin.natAdd 6 t)))
      (fullCoordinates.symm x.1) (rawDirection (Fin.natAdd 6 r))=
      dq r (dq t (fun y => partP s n b y i k)) x := by
  have smooth := DR_smooth (Fin.natAdd 6 t) (nativePart_smooth s n b time i k ⟨_,physical⟩)
  have derivative := native_derivative (fun w => fderiv ℝ (fun z => nativePart s n b z i k) w
    (rawDirection (Fin.natAdd 6 t))) x r smooth
  have same : (fun y => fderiv ℝ (fun z => nativePart s n b z i k) (fullCoordinates.symm y.1)
      (rawDirection (Fin.natAdd 6 t)))=ᶠ[𝓝 x]dq t (fun y => partP s n b y i k) := by
    filter_upwards [originalPhysicalPhase_open.mem_nhds physical] with y hy
    exact nativePart_D s n b time i k t y hy
  rw [same.fderiv_eq] at derivative
  exact derivative.symm

theorem nativeHalf_pullback (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (x : Phase) (physical : x∈originalPhysicalPhase) :
    nativeHalf (nativePart s n b) (fullCoordinates.symm x.1)=densityCorrection (partP s n b) x := by
  have quadratic : densityQuadratic (partP s n b) x=
      ∑ i : Fin 94,∑ k : Fin 94,partP s n b x i k*rawAmbient (Fin.natAdd 6 i) x*rawAmbient (Fin.natAdd 6 k) x := by
    unfold densityQuadratic
    simp only [Matrix.mul_apply,Matrix.transpose_apply,rhoColumn,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold nativeHalf densityCorrection densityDrift densityHessian
  rw [quadratic]
  simp only [nativePart_pullback,nativePart_D s n b time _ _ _ x physical]
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  unfold rawAmbient rawHessianAmbient
  ring

theorem nativeQuarter_pullback (s : Fin 2) (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (x : Phase) (physical : x∈originalPhysicalPhase) :
    nativeQuarter (nativePart s n b) (fullCoordinates.symm x.1)=weylCorrection (partP s n b) x := by
  unfold nativeQuarter weylCorrection
  simp only [nativePart_DD s n b time _ _ _ _ x physical]

theorem nativeTotal_recognition (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (z : physicalChart) (i k : Fin 94) :
    (∑ s : Fin 2,nativePart s n b z.val i k)=
      ∑ j : Fin 13,originalTemporalWeights n b j*rawPrincipalCoefficient j (Fin.natAdd 6 i) (Fin.natAdd 6 k) z.val := by
  let x : Phase := (fullCoordinates z.val,0)
  have physical : fullCoordinates.symm x.1∈physicalChart := by simp [x]
  have read := raw94_Qtime_recognition n b time x physical i k
  apply Complex.ofReal_injective
  simpa [x,totalP,nativePart,partP,Fin.sum_univ_two,timeTensor,leafP] using read

private theorem native_sum_D {ι : Type} [Fintype ι] (c : ι → ℝ) (F : ι → Configuration → ℝ)
    (z D : Configuration) (smooth : ∀ j,ContDiffAt ℝ ∞ (F j) z) :
    fderiv ℝ (fun w => ∑ j,c j*F j w) z D=∑ j,c j*fderiv ℝ (F j) z D := by
  rw [fderiv_fun_sum (fun j _ => (contDiffAt_const.mul (smooth j)).differentiableAt (by simp))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have derivative : fderiv ℝ (fun w => c j*F j w) z=c j • fderiv ℝ (F j) z :=
    ((smooth j).differentiableAt (by simp)).hasFDerivAt.const_mul (c j) |>.fderiv
  rw [derivative]
  rfl

private theorem native_sum_DD {ι : Type} [Fintype ι] (c : ι → ℝ) (F : ι → Configuration → ℝ)
    (z : physicalChart) (D E : Configuration) (smooth : ∀ j,∀ w : physicalChart,ContDiffAt ℝ ∞ (F j) w.val) :
    fderiv ℝ (fun w => fderiv ℝ (fun t => ∑ j,c j*F j t) w E) z.val D=
      ∑ j,c j*fderiv ℝ (fun w => fderiv ℝ (F j) w E) z.val D := by
  have same : (fun w => fderiv ℝ (fun t => ∑ j,c j*F j t) w E)=ᶠ[𝓝 z.val]
      (fun w => ∑ j,c j*fderiv ℝ (F j) w E) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact native_sum_D c F w E (fun j => smooth j ⟨w,hw⟩)
  rw [same.fderiv_eq]
  exact native_sum_D c (fun j w => fderiv ℝ (F j) w E) z.val D
    (fun j => ((smooth j z).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)

private theorem sum_rotate {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    (∑ i,∑ k,∑ j,f i k j)=∑ j,∑ i,∑ k,f i k j := by
  calc
    _ = ∑ i,∑ j,∑ k,f i k j := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

private theorem nativeHalf_sum {ι : Type} [Fintype ι] (c : ι → ℝ) (F : ι → NativeTensor)
    (smooth : ∀ j i k,∀ z : physicalChart,ContDiffAt ℝ ∞ (fun w => F j w i k) z.val)
    (z : physicalChart) :
    nativeHalf (fun w i k => ∑ j,c j*F j w i k) z.val=∑ j,c j*nativeHalf (F j) z.val := by
  have derivative (i k : Fin 94) := native_sum_D c (fun j w => F j w i k) z.val
    (rawDirection (Fin.natAdd 6 i)) (fun j => smooth j i k z)
  unfold nativeHalf
  simp only [derivative,Finset.sum_mul,←Finset.sum_add_distrib]
  have term (i k : Fin 94) (j : ι) :
      c j*F j z.val i k*(rawHalfLog (Fin.natAdd 6 i) z.val*rawHalfLog (Fin.natAdd 6 k) z.val+
        fderiv ℝ (rawHalfLog (Fin.natAdd 6 k)) z.val (rawDirection (Fin.natAdd 6 i)))+
        c j*fderiv ℝ (fun w => F j w i k) z.val (rawDirection (Fin.natAdd 6 i))*rawHalfLog (Fin.natAdd 6 k) z.val=
      c j*(F j z.val i k*(rawHalfLog (Fin.natAdd 6 i) z.val*rawHalfLog (Fin.natAdd 6 k) z.val+
        fderiv ℝ (rawHalfLog (Fin.natAdd 6 k)) z.val (rawDirection (Fin.natAdd 6 i)))+
        fderiv ℝ (fun w => F j w i k) z.val (rawDirection (Fin.natAdd 6 i))*rawHalfLog (Fin.natAdd 6 k) z.val) := by
    ring

  simp_rw [term]
  rw [sum_rotate]
  simp only [Finset.mul_sum]

private theorem nativeQuarter_sum {ι : Type} [Fintype ι] (c : ι → ℝ) (F : ι → NativeTensor)
    (smooth : ∀ j i k,∀ z : physicalChart,ContDiffAt ℝ ∞ (fun w => F j w i k) z.val)
    (z : physicalChart) :
    nativeQuarter (fun w i k => ∑ j,c j*F j w i k) z.val=∑ j,c j*nativeQuarter (F j) z.val := by
  unfold nativeQuarter
  simp only [native_sum_DD c (fun j w => F j w _ _) z _ _ (fun j w => smooth j _ _ w)]
  rw [sum_rotate]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem nativeHalf_congr (F G : NativeTensor)
    (same : ∀ z : physicalChart,∀ i k,F z.val i k=G z.val i k) (z : physicalChart) :
    nativeHalf F z.val=nativeHalf G z.val := by
  have derivative (i k : Fin 94) : fderiv ℝ (fun w => F w i k) z.val=fderiv ℝ (fun w => G w i k) z.val := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact same ⟨w,hw⟩ i k
  simp only [nativeHalf,same z,derivative]

private theorem nativeQuarter_congr (F G : NativeTensor)
    (same : ∀ z : physicalChart,∀ i k,F z.val i k=G z.val i k) (z : physicalChart) :
    nativeQuarter F z.val=nativeQuarter G z.val := by
  have derivative (i k : Fin 94) :
      (fun w => fderiv ℝ (fun t => F t i k) w (rawDirection (Fin.natAdd 6 k)))=ᶠ[𝓝 z.val]
      (fun w => fderiv ℝ (fun t => G t i k) w (rawDirection (Fin.natAdd 6 k))) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    have first : (fun t => F t i k)=ᶠ[𝓝 w](fun t => G t i k) := by
      filter_upwards [physicalChart.isOpen.mem_nhds hw] with t ht
      exact same ⟨t,ht⟩ i k
    rw [first.fderiv_eq]
  unfold nativeQuarter
  simp only [(derivative _ _).fderiv_eq]

theorem raw94_Qtime_half_extraction (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (z : physicalChart) :
    (∑ j : Fin 13,originalTemporalWeights n b j*originalRhoHalfLeaf j z.val)=
      nativeHalf (nativePart 0 n b) z.val+nativeHalf (nativePart 1 n b) z.val := by
  unfold originalRhoHalfLeaf
  rw [←nativeHalf_sum (originalTemporalWeights n b)
    (fun j w i k => rawPrincipalCoefficient j (Fin.natAdd 6 i) (Fin.natAdd 6 k) w)
    (fun j i k z => rawPrincipalCoefficient_smooth j _ _ z) z]
  rw [nativeHalf_congr _ (fun w i k => ∑ s : Fin 2,nativePart s n b w i k)
    (fun z i k => (nativeTotal_recognition n b time z i k).symm) z]
  have split := nativeHalf_sum (fun _ : Fin 2 => (1 : ℝ)) (fun s => nativePart s n b)
    (fun s i k z => nativePart_smooth s n b time i k z) z
  simpa [Fin.sum_univ_two] using split

theorem raw94_Qtime_quarter_extraction (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (z : physicalChart) :
    (∑ j : Fin 13,originalTemporalWeights n b j*originalRhoQuarterLeaf j z.val)=
      nativeQuarter (nativePart 0 n b) z.val+nativeQuarter (nativePart 1 n b) z.val := by
  unfold originalRhoQuarterLeaf
  rw [←nativeQuarter_sum (originalTemporalWeights n b)
    (fun j w i k => rawPrincipalCoefficient j (Fin.natAdd 6 i) (Fin.natAdd 6 k) w)
    (fun j i k z => rawPrincipalCoefficient_smooth j _ _ z) z]
  rw [nativeQuarter_congr _ (fun w i k => ∑ s : Fin 2,nativePart s n b w i k)
    (fun z i k => (nativeTotal_recognition n b time z i k).symm) z]
  have split := nativeQuarter_sum (fun _ : Fin 2 => (1 : ℝ)) (fun s => nativePart s n b)
    (fun s i k z => nativePart_smooth s n b time i k z) z
  simpa [Fin.sum_univ_two] using split

def originalRhoDensityArray (m : ℕ) : ℝ := densityArray scalarPArray m+densityArray gaugePArray m
def originalRhoWeylArray (m : ℕ) : ℝ := weylArray scalarPArray m+weylArray gaugePArray m

theorem actual_rho_half_budget (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (inputs : CoefficientInputs x (M+2)) : FiniteBound (originalRhoTimeHalf n b) M originalRhoDensityArray x := by
  have bound (s : Fin 2) := density_correction_budget (partP s n b) (partP_smooth s n b time)
    (partArray s) (partArray_nonnegative s) M x hx box (partP_budget s n b time (M+2) x hx box inputs)
  have sum := finite_add _ _ (densityCorrection_smooth _ (partP_smooth 0 n b time))
    (densityCorrection_smooth _ (partP_smooth 1 n b time)) _ _ M x hx (bound 0) (bound 1)
  have same : originalRhoTimeHalf n b=ᶠ[𝓝 x](fun y => densityCorrection (partP 0 n b) y+densityCorrection (partP 1 n b) y) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    have native := raw94_Qtime_half_extraction n b time ⟨_,hy.1.1⟩
    have formula : originalRhoTimeHalf n b y=nativeHalf (nativePart 0 n b) (fullCoordinates.symm y.1)+
        nativeHalf (nativePart 1 n b) (fullCoordinates.symm y.1) := native
    rw [formula,nativeHalf_pullback _ _ _ time _ hy.1.1,nativeHalf_pullback _ _ _ time _ hy.1.1]
  intro m hm w
  have read : jet m (originalRhoTimeHalf n b) w x=jet m
      (fun y => densityCorrection (partP 0 n b) y+densityCorrection (partP 1 n b) y) w x :=
    PreparationVacuumCoframeBudget.jet_germ same m w
  rw [read]
  exact sum m hm w

theorem actual_rho_quarter_budget (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (inputs : CoefficientInputs x (M+2)) : FiniteBound (originalRhoTimeQuarter n b) M originalRhoWeylArray x := by
  have bound (s : Fin 2) := weyl_correction_budget (partP s n b) (partP_smooth s n b time)
    (partArray s) M x hx (partP_budget s n b time (M+2) x hx box inputs)
  have sum := finite_add _ _ (weylCorrection_smooth _ (partP_smooth 0 n b time))
    (weylCorrection_smooth _ (partP_smooth 1 n b time)) _ _ M x hx (bound 0) (bound 1)
  have same : originalRhoTimeQuarter n b=ᶠ[𝓝 x](fun y => weylCorrection (partP 0 n b) y+weylCorrection (partP 1 n b) y) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    have native := raw94_Qtime_quarter_extraction n b time ⟨_,hy.1.1⟩
    have formula : originalRhoTimeQuarter n b y=nativeQuarter (nativePart 0 n b) (fullCoordinates.symm y.1)+
        nativeQuarter (nativePart 1 n b) (fullCoordinates.symm y.1) := native
    rw [formula,nativeQuarter_pullback _ _ _ time _ hy.1.1,nativeQuarter_pullback _ _ _ time _ hy.1.1]
  intro m hm w
  have read : jet m (originalRhoTimeQuarter n b) w x=jet m
      (fun y => weylCorrection (partP 0 n b) y+weylCorrection (partP 1 n b) y) w x :=
    PreparationVacuumCoframeBudget.jet_germ same m w
  rw [read]
  exact sum m hm w

end LowEnergy.PreparationVacuumLowerCorrections
