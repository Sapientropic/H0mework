import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMColumnThreshold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMZeroClockColumns
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open LowEnergy.GaussComposite.ActualDressedPoleWardMode LowEnergy.ActualDressedPoleWardMode
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedZeroClockFrequency
open ActualDressedZeroClockVector ActualDressedNativeConstraint ActualEMCurrentSplit ActualEMCarrierOwn
open ActualEMAction ActualEMDressedSchur PreparationVacuumPhysicalModeContact ActualDressedFrequencyHalf Filter Set
open scoped Topology Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator commonDeterminant
  commonEMSourceColumn frequencyResponsePencil frequencyHalfPolarization sourceCokernel emInsertion

private theorem specialized_clock_pole (N D : (ℂ[X])[X]) (m j : ℕ) (less : j < m)
    (dFactor : X^m∣D) (s : ℝ) (dRegular : (D.coeff m).eval (s : ℂ)≠0)
    (nRegular : (N.coeff j).eval (s : ℂ)≠0) :
    0<poleOrder (readFraction (clockSpecialize s N) (clockSpecialize s D)) 0 := by
  let Ne := clockSpecialize s N
  let De := clockSpecialize s D
  let R := readFraction Ne De
  have nCoefficient : Ne.coeff j≠0 := by simpa only [Ne,clockSpecialize,coe_mapRingHom,coeff_map,coe_evalRingHom] using nRegular
  have dCoefficient : De.coeff m≠0 := by simpa only [De,clockSpecialize,coe_mapRingHom,coeff_map,coe_evalRingHom] using dRegular
  have nNonzero : Ne≠0 := fun zero => nCoefficient (by rw [zero,coeff_zero])
  have dNonzero : De≠0 := fun zero => dCoefficient (by rw [zero,coeff_zero])
  have mappedFactor : X^m∣De := by
    have mapped := (_root_.map_dvd (clockSpecialize s)) dFactor
    simpa only [De,map_pow,clockSpecialize,coe_mapRingHom,Polynomial.map_X] using mapped
  have dOrder : m≤De.rootMultiplicity 0 := by
    apply (le_rootMultiplicity_iff dNonzero).mpr
    simpa only [map_zero,sub_zero] using mappedFactor
  have nOrder : Ne.rootMultiplicity 0≤j := by
    rw [rootMultiplicity_eq_natTrailingDegree']
    exact natTrailingDegree_le_of_ne_zero nCoefficient
  by_contra positive
  have zeroOrder : R.denom.rootMultiplicity 0=0 := Nat.eq_zero_of_not_pos positive
  have cross := reduced_cross_identity Ne De dNonzero
  have rightNonzero : Ne*R.denom≠0 := mul_ne_zero nNonzero (RatFunc.denom_ne_zero R)
  have leftNonzero : R.num*De≠0 := by rw [cross]; exact rightNonzero
  have lower := le_rootMultiplicity_mul 0 leftNonzero
  have same : (R.num*De).rootMultiplicity 0=Ne.rootMultiplicity 0 := by
    rw [cross,rootMultiplicity_mul rightNonzero,zeroOrder,add_zero]
  rw [same] at lower
  omega

private theorem source_clock_pole (N D : (ℂ[X])[X]) (m : ℕ) (dFactor : X^m∣D)
    (dNonzero : D.coeff m≠0) (failure : ¬X^m∣N) :
    ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
      0<poleOrder (readFraction (clockSpecialize s N) (clockSpecialize s D)) 0 := by
  have coefficient : ¬∀j < m, N.coeff j=0 := fun zero => failure (X_pow_dvd_iff.mpr zero)
  push Not at coefficient
  obtain ⟨j,less,nonzero⟩ := coefficient
  filter_upwards [source_static_punctured_chart _ dNonzero,source_static_punctured_chart _ nonzero] with s dRegular nRegular
  exact specialized_clock_pole N D m j less dFactor s dRegular nRegular

def EMTensorClockFinite (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Prop :=
  ∀mu nu, X^frequencyClockOrder event eps n∣frequencyClockEMNumerator event eps n mu nu

theorem source_em_tensor_clock_failure (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nonzero : frequencyClockDeterminant event eps n≠0) (failure : ¬EMTensorClockFinite event eps n) :
    ∃mu nu, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
      0<poleOrder (readFraction (clockSpecialize s (frequencyClockEMNumerator event eps n mu nu))
        (clockSpecialize s (frequencyClockDeterminant event eps n))) 0 := by
  classical
  have failed : ∃mu nu, ¬X^frequencyClockOrder event eps n∣frequencyClockEMNumerator event eps n mu nu := by
    simpa only [EMTensorClockFinite,not_forall] using failure
  obtain ⟨mu,nu,failed⟩ := failed
  exact ⟨mu,nu,source_clock_pole _ _ _ (source_frequency_clock_factor event eps n)
    (source_frequency_denominator_nonzero event eps n nonzero) failed⟩

theorem source_em_column_clock_failure (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nonzero : frequencyClockDeterminant event eps n≠0) (failure : ¬EMColumnsClockFinite event eps n) :
    ∃nu i, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
      0<poleOrder (readFraction (clockSpecialize s (fullClockEMColumn event eps n nu i))
        (clockSpecialize s (frequencyClockDeterminant event eps n))) 0 := by
  classical
  have failed : ∃nu i, ¬X^frequencyClockOrder event eps n∣fullClockEMColumn event eps n nu i := by
    simpa only [EMColumnsClockFinite,not_forall] using failure
  obtain ⟨nu,i,failed⟩ := failed
  exact ⟨nu,i,source_clock_pole _ _ _ (source_frequency_clock_factor event eps n)
    (source_frequency_denominator_nonzero event eps n nonzero) failed⟩

def zeroClockEMColumnPrincipalData (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) : Fin 289 → ℕ × List ℂ :=
  fun i => let R := zeroClockEMColumnFraction event eps n nu i
    (poleOrder R a,List.ofFn (fun k : Fin (poleOrder R a) => principalCoefficient R a k.val))

private theorem complete_negative_powers (R : RatFunc ℂ) (a z : ℂ) :
    (principalNumerator R a).eval z/(z-a)^poleOrder R a=
      ∑k ∈ Finset.range (poleOrder R a), principalCoefficient R a k*(z-a)^k/(z-a)^poleOrder R a := by
  by_cases zero : principalNumerator R a=0
  · simp [zero,principalCoefficient]
  · have bound : (taylor a (principalNumerator R a)).natDegree<poleOrder R a := by
      rw [natDegree_taylor]
      exact (natDegree_lt_iff_degree_lt zero).mpr (principal_degree R a)
    have expansion := (taylor a (principalNumerator R a)).eval_eq_sum_range' bound (z-a)
    rw [taylor_eval_sub] at expansion
    rw [expansion,Finset.sum_div]
    rfl

/-- All full-coordinate orders and analytic remainders survive a vanishing highest EM mode read. -/
theorem actual_zero_clock_em_column_principal (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ)
    (chart : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0)
    (finite : EMColumnsClockFinite event eps n) (away : (s : ℂ)≠a)
    (regular : ∀i, (rootRemainder (zeroClockEMColumnFraction event eps n nu i) a).eval (s : ℂ)≠0) :
    Tendsto (fun sigma : ℝ => correctedEMColumn event eps s sigma n nu)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (fun i =>
        (∑k ∈ Finset.range (poleOrder (zeroClockEMColumnFraction event eps n nu i) a),
          principalCoefficient (zeroClockEMColumnFraction event eps n nu i) a k*
            ((s : ℂ)-a)^k/((s : ℂ)-a)^poleOrder (zeroClockEMColumnFraction event eps n nu i) a)+
        (analyticNumerator (zeroClockEMColumnFraction event eps n nu i) a).eval (s : ℂ)/
          (rootRemainder (zeroClockEMColumnFraction event eps n nu i) a).eval (s : ℂ))) := by
  have value (i : Fin 289) := complete_principal_part (zeroClockEMColumnFraction event eps n nu i)
    a (s : ℂ) away (regular i)
  simp_rw [complete_negative_powers] at value
  have actual := actual_zero_clock_em_column event eps s n nu chart finite
  have same : zeroClockEMColumnRead event eps s n nu=(fun i =>
      (∑k ∈ Finset.range (poleOrder (zeroClockEMColumnFraction event eps n nu i) a),
        principalCoefficient (zeroClockEMColumnFraction event eps n nu i) a k*
          ((s : ℂ)-a)^k/((s : ℂ)-a)^poleOrder (zeroClockEMColumnFraction event eps n nu i) a)+
      (analyticNumerator (zeroClockEMColumnFraction event eps n nu i) a).eval (s : ℂ)/
        (rootRemainder (zeroClockEMColumnFraction event eps n nu i) a).eval (s : ℂ)) := by
    funext i
    exact value i
  rw [same] at actual
  exact actual

def actualEMZeroClockMode (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) : Fin 289 → ℂ :=
  sourcePoleMode (zeroClockEMColumn event eps n nu) (zeroClockFrequencyDenominator event eps n) a

/-- Each of the sixteen original canonical spectra generates its mode from its own full forcing column. -/
theorem actual_zero_clock_em_full_mode (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    actualEMZeroClockMode event eps n nu a≠0 ∧
      (zeroClockPencil event eps n).map (Polynomial.eval a)*ᵥactualEMZeroClockMode event eps n nu a=0 := by
  have observed : a∈visibleRoots (readFraction
      (dotProduct (fun i => Polynomial.C (emInsertion i mu)) (zeroClockEMColumn event eps n nu))
        (zeroClockFrequencyDenominator event eps n)) := by
    rw [actual_zero_clock_em_column_observer]
    exact root
  exact ⟨source_pole_mode_nonzero _ _ _ _ observed,
    source_visible_full_kernel _ _ _ _ _ _ (actual_zero_clock_em_threshold_equation event eps n nu balanced finite) observed⟩

private theorem divided_matrix_kernel {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) (d : ℂ) (v : ι → ℂ) (regular : d≠0) (kernel : H*ᵥv=0) :
    (fun i j => H i j/d)*ᵥv=0 := by
  funext i
  have coordinate := congrFun kernel i
  simp only [Matrix.mulVec,dotProduct,Pi.zero_apply] at coordinate ⊢
  have divided : (∑j, H i j/d*v j)=(∑j, H i j*v j)/d := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [regular]
  rw [divided,coordinate,zero_div]

theorem actual_zero_clock_em_threshold_kernel (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (clearingRegular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    zeroClockThresholdPencil event eps s n*ᵥactualEMZeroClockMode event eps n nu (s : ℂ)=0 :=
  divided_matrix_kernel _ _ _ clearingRegular
    (actual_zero_clock_em_full_mode event eps n mu nu (s : ℂ) balanced finite root).2

/-- The actual original P limit, its independent clearing chart and the full quantum response are retained. -/
theorem actual_zero_clock_em_mode_quantum_return (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (clearingRegular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let v := actualEMZeroClockMode event eps n nu (s : ℂ)
    Tendsto (fun sigma : ℝ => (sigma : ℂ) •
      (frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (emOriginalJacobi (frequencyRay eps s n)*ᵥv)) := by
  dsimp only
  let v := actualEMZeroClockMode event eps n nu (s : ℂ)
  have continuous : Continuous (fun M : Matrix (Fin 289) (Fin 289) ℂ => M*ᵥv) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have limit := (continuous.tendsto _).comp (actual_zero_clock_threshold_pencil event eps s n clearingRegular balanced)
  rw [actual_zero_clock_em_threshold_kernel event eps s n mu nu balanced finite clearingRegular root] at limit
  have constant : Tendsto (fun _ : ℝ => emOriginalJacobi (frequencyRay eps s n)*ᵥv)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (emOriginalJacobi (frequencyRay eps s n)*ᵥv)) := tendsto_const_nhds
  have full := constant.sub limit
  simp only [Function.comp_def,sub_zero] at full
  apply Tendsto.congr' _ full
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  rw [damped_source_sheet_response event eps s sigma n positive,Matrix.sub_mulVec,Matrix.smul_mulVec]
  abel

theorem actual_zero_clock_em_mode_nine_return (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (clearingRegular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) (j : Fin 9) :
    let v := actualEMZeroClockMode event eps n nu (s : ℂ)
    Tendsto (fun sigma : ℝ => (sigma : ℂ)*sourceCokernel (frequencyRay eps s n)
      (frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv) j)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (sourceCokernel (frequencyRay eps s n) (emOriginalJacobi (frequencyRay eps s n)*ᵥv) j)) := by
  dsimp only
  let v := actualEMZeroClockMode event eps n nu (s : ℂ)
  have continuous : Continuous (fun a : Fin 289 → ℂ => sourceCokernel (frequencyRay eps s n) a j) :=
    (continuous_apply j).comp ((sourceCokernel (frequencyRay eps s n)).toContinuousLinearMap.continuous)
  have limit := (continuous.tendsto _).comp
    (actual_zero_clock_em_mode_quantum_return event eps s n mu nu balanced finite clearingRegular root)
  simpa only [Function.comp_def,map_smul,Pi.smul_apply,smul_eq_mul] using limit

structure FullEMZeroClockMode (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) where
  mode : Fin 289 → ℂ
  generated : mode=actualEMZeroClockMode event eps n nu a
  nonzero : mode≠0
  homogeneous : (zeroClockPencil event eps n).map (Polynomial.eval a)*ᵥmode=0
  electromagnetic : ModeEMDisposition mode
  complete : mode=emInsertion*ᵥemCoordinateCurrent mode+emCurrentResidual mode
  residual : emInsertion.transpose*ᵥemCurrentResidual mode=0
  clearing : PoleClearingDisposition (zeroClockClearing event eps n) a
  observedPrincipal : FrequencyPrincipal eps (zeroClockFrequencyEMFraction event eps n mu nu) a
  columnPrincipals : Fin 289 → ℕ × List ℂ
  columnPrincipals_generated : columnPrincipals=zeroClockEMColumnPrincipalData event eps n nu a

def sourceFullEMZeroClockMode (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    FullEMZeroClockMode event eps n mu nu a := by
  let v := actualEMZeroClockMode event eps n nu a
  have paid := actual_zero_clock_em_full_mode event eps n mu nu a balanced finite root
  exact ⟨v,rfl,paid.1,paid.2,sourceModeEMDisposition v,
    (source_mode_full_decomposition v).1,(source_mode_full_decomposition v).2,
    sourcePoleClearingDisposition _ a,
    sourceFrequencyPrincipal eps (zeroClockFrequencyEMFraction event eps n mu nu) ⟨a,root⟩,
    zeroClockEMColumnPrincipalData event eps n nu a,rfl⟩

/-- Observer multiplicities are retained independently from each full column's cancellation order. -/
def sourceEMZeroClockModes (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n) :
    ∀mu nu : Fin 4, Multiset (Σa : ℂ, FullEMZeroClockMode event eps n mu nu a) :=
  fun mu nu => (visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)).attach.map
    (fun a => ⟨a.val,sourceFullEMZeroClockMode event eps n mu nu a.val balanced finite a.property⟩)

inductive EMColumnsClockReturn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Type
  | singular (zero : frequencyClockDeterminant event eps n=0)
  | tensorClock (nonzero : frequencyClockDeterminant event eps n≠0)
      (failure : ¬EMTensorClockFinite event eps n)
      (pole : ∃mu nu, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
        0<poleOrder (readFraction (clockSpecialize s (frequencyClockEMNumerator event eps n mu nu))
          (clockSpecialize s (frequencyClockDeterminant event eps n))) 0)
  | columnClock (nonzero : frequencyClockDeterminant event eps n≠0)
      (tensor : EMTensorClockFinite event eps n) (failure : ¬EMColumnsClockFinite event eps n)
      (pole : ∃nu i, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
        0<poleOrder (readFraction (clockSpecialize s (fullClockEMColumn event eps n nu i))
          (clockSpecialize s (frequencyClockDeterminant event eps n))) 0)
  | thresholdClock (nonzero : frequencyClockDeterminant event eps n≠0)
      (tensor : EMTensorClockFinite event eps n) (columns : EMColumnsClockFinite event eps n)
      (failure : ¬PencilClockBalanced event eps n)
      (pole : ∃i j, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
        0<poleOrder (readFraction (clockSpecialize s (fullClockPencil event eps n i j))
          (clockSpecialize s (fullClockClearing event eps n))) 0)
  | realized (nonzero : frequencyClockDeterminant event eps n≠0)
      (tensor : EMTensorClockFinite event eps n) (columns : EMColumnsClockFinite event eps n)
      (balanced : PencilClockBalanced event eps n)
      (modes : ∀mu nu : Fin 4, Multiset (Σa : ℂ, FullEMZeroClockMode event eps n mu nu a))
      (column_return : ∀s : ℝ, (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0 →
        ∀nu : Fin 4, Tendsto (fun sigma : ℝ => correctedEMColumn event eps s sigma n nu)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMColumnRead event eps s n nu)))
      (tensor_return : ∀s : ℝ, (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0 →
        Tendsto (fun sigma : ℝ => correctedEMTensor event eps s sigma n)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockFrequencyEMRead event eps s n)))
      (pencil_return : ∀s : ℝ, (zeroClockClearing event eps n).eval (s : ℂ)≠0 →
        Tendsto (fun sigma : ℝ => frequencyResponsePencil event ((eps^2 : ℝ) • n)
          (frequencyRay eps s n) (dampedFourierClock (sourceFrequency eps s) sigma))
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockThresholdPencil event eps s n)))

/-- This whole source return chooses no electron probe, root, simple pole, clearing chart or photon branch. -/
def sourceEMColumnsClockReturn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    EMColumnsClockReturn event eps n := by
  classical
  by_cases zero : frequencyClockDeterminant event eps n=0
  · exact .singular zero
  · by_cases tensor : EMTensorClockFinite event eps n
    · by_cases columns : EMColumnsClockFinite event eps n
      · by_cases balanced : PencilClockBalanced event eps n
        · exact .realized zero tensor columns balanced (sourceEMZeroClockModes event eps n balanced columns)
            (fun s regular nu => actual_zero_clock_em_column event eps s n nu regular columns)
            (fun s regular => actual_zero_clock_frequency_tensor event eps s n regular tensor)
            (fun s regular => actual_zero_clock_threshold_pencil event eps s n regular balanced)
        · exact .thresholdClock zero tensor columns balanced (source_pencil_clock_failure event eps n balanced)
      · exact .columnClock zero tensor columns (source_em_column_clock_failure event eps n zero columns)
    · exact .tensorClock zero tensor (source_em_tensor_clock_failure event eps n zero tensor)

end LowEnergy.GaussComposite.ActualDressedEMZeroClockColumns
