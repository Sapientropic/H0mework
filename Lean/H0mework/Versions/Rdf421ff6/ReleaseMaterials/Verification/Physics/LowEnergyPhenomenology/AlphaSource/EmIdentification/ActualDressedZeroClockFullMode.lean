import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedZeroClockThresholdReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedZeroClockVector
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open LowEnergy.GaussComposite.ActualDressedPoleWardMode LowEnergy.ActualDressedPoleWardMode
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedZeroClockFrequency
open ActualCompositeFieldCurrent ActualDressedNativeConstraint ActualEMCurrentSplit ActualEMCarrierOwn
open ActualEMAction ActualEMDressedSchur
open PreparationVacuumPhysicalModeContact ActualDressedFrequencyHalf Filter Set
open scoped Topology
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator commonDeterminant sourceCommonVector
  frequencyResponsePencil frequencyHalfPolarization sourceCokernel

private theorem specialized_clock_pole (N D : (ℂ[X])[X]) (m j : ℕ) (less : j < m)
    (dFactor : X^m∣D) (eps : ℝ) (dRegular : (D.coeff m).eval (eps : ℂ)≠0)
    (nRegular : (N.coeff j).eval (eps : ℂ)≠0) :
    0<poleOrder (readFraction (clockSpecialize eps N) (clockSpecialize eps D)) 0 := by
  let Ne := clockSpecialize eps N
  let De := clockSpecialize eps D
  let R := readFraction Ne De
  have nCoefficient : Ne.coeff j≠0 := by simpa only [Ne,clockSpecialize,coe_mapRingHom,coeff_map,coe_evalRingHom] using nRegular
  have dCoefficient : De.coeff m≠0 := by simpa only [De,clockSpecialize,coe_mapRingHom,coeff_map,coe_evalRingHom] using dRegular
  have nNonzero : Ne≠0 := fun zero => nCoefficient (by rw [zero,coeff_zero])
  have dNonzero : De≠0 := fun zero => dCoefficient (by rw [zero,coeff_zero])
  have mappedFactor : X^m∣De := by
    have mapped := (_root_.map_dvd (clockSpecialize eps)) dFactor
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
    ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      0<poleOrder (readFraction (clockSpecialize eps N) (clockSpecialize eps D)) 0 := by
  have coefficient : ¬∀ j < m, N.coeff j=0 := fun zero => failure (X_pow_dvd_iff.mpr zero)
  push Not at coefficient
  obtain ⟨j,less,nonzero⟩ := coefficient
  filter_upwards [source_static_punctured_chart _ dNonzero,source_static_punctured_chart _ nonzero] with eps dRegular nRegular
  exact specialized_clock_pole N D m j less dFactor eps dRegular nRegular

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

theorem source_full_vector_clock_failure (event : DressedEvent) (eps : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg)
    (nonzero : frequencyClockDeterminant event eps n≠0)
    (failure : ¬FullVectorClockFinite event eps n ps sL sR) :
    ∃i, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
      0<poleOrder (readFraction (clockSpecialize s (fullClockSourceVector event eps n ps sL sR i))
        (clockSpecialize s (frequencyClockDeterminant event eps n))) 0 := by
  classical
  have failed : ∃i, ¬X^frequencyClockOrder event eps n∣fullClockSourceVector event eps n ps sL sR i := by
    simpa only [FullVectorClockFinite,not_forall] using failure
  obtain ⟨i,failed⟩ := failed
  exact ⟨i,source_clock_pole _ _ _ (source_frequency_clock_factor event eps n)
    (source_frequency_denominator_nonzero event eps n nonzero) failed⟩

theorem source_full_clearing_nonzero (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    fullClockClearing event eps n≠0 := by
  have paid := ActualDressedUniformClockNonzero.actual_common_ir_denominator_nonzero event n eps 1 0 (by norm_num)
  rw [← frequency_damping_eval eps 0 1,← frequency_clock_specialize eps 0] at paid
  change (clockSpecialize 0 (fullClockClearing event eps n)).eval (1 : ℂ)≠0 at paid
  intro zero
  rw [zero,map_zero,eval_zero] at paid
  exact paid rfl

theorem source_pencil_clock_failure (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (failure : ¬PencilClockBalanced event eps n) :
    ∃i j, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
      0<poleOrder (readFraction (clockSpecialize s (fullClockPencil event eps n i j))
        (clockSpecialize s (fullClockClearing event eps n))) 0 := by
  classical
  have failed : ∃i j, ¬X^clearingClockOrder event eps n∣fullClockPencil event eps n i j := by
    simpa only [PencilClockBalanced,not_forall] using failure
  obtain ⟨i,j,failed⟩ := failed
  exact ⟨i,j,source_clock_pole _ _ _ (source_clearing_clock_factor event eps n)
    (coeff_natTrailingDegree_ne_zero.mpr (source_full_clearing_nonzero event eps n)) failed⟩

def zeroClockVectorPrincipalData (event : DressedEvent) (eps : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) (a : ℂ) : Fin 289 → ℕ × List ℂ :=
  fun i => let R := zeroClockVectorFraction event eps n ps sL sR i
    (poleOrder R a,List.ofFn (fun k : Fin (poleOrder R a) => principalCoefficient R a k.val))

/-- All lower EM-visible terms survive, even if the highest generated full mode has zero EM read. -/
theorem actual_zero_clock_vector_principal (event : DressedEvent) (eps s : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg) (a : ℂ)
    (chart : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0)
    (finite : FullVectorClockFinite event eps n ps sL sR) (away : (s : ℂ)≠a)
    (regular : ∀i, (rootRemainder (zeroClockVectorFraction event eps n ps sL sR i) a).eval (s : ℂ)≠0) :
    Tendsto (fun sigma : ℝ => correctedProbeResponse event eps s sigma n ps sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (fun i =>
        (∑k ∈ Finset.range (poleOrder (zeroClockVectorFraction event eps n ps sL sR i) a),
          principalCoefficient (zeroClockVectorFraction event eps n ps sL sR i) a k*
            ((s : ℂ)-a)^k/((s : ℂ)-a)^poleOrder (zeroClockVectorFraction event eps n ps sL sR i) a)+
        (analyticNumerator (zeroClockVectorFraction event eps n ps sL sR i) a).eval (s : ℂ)/
          (rootRemainder (zeroClockVectorFraction event eps n ps sL sR i) a).eval (s : ℂ))) := by
  have value (i : Fin 289) := complete_principal_part (zeroClockVectorFraction event eps n ps sL sR i)
    a (s : ℂ) away (regular i)
  simp_rw [complete_negative_powers] at value
  have actual := actual_zero_clock_full_vector event eps s n ps sL sR chart finite
  have same : zeroClockVectorRead event eps s n ps sL sR=(fun i =>
      (∑k ∈ Finset.range (poleOrder (zeroClockVectorFraction event eps n ps sL sR i) a),
        principalCoefficient (zeroClockVectorFraction event eps n ps sL sR i) a k*
          ((s : ℂ)-a)^k/((s : ℂ)-a)^poleOrder (zeroClockVectorFraction event eps n ps sL sR i) a)+
      (analyticNumerator (zeroClockVectorFraction event eps n ps sL sR i) a).eval (s : ℂ)/
        (rootRemainder (zeroClockVectorFraction event eps n ps sL sR i) a).eval (s : ℂ)) := by
    funext i
    exact value i
  rw [same] at actual
  exact actual

def actualZeroClockMode (event : DressedEvent) (eps : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) (a : ℂ) : Fin 289 → ℂ :=
  sourcePoleMode (zeroClockSourceVector event eps n ps sL sR) (zeroClockFrequencyDenominator event eps n) a

theorem actual_zero_clock_full_mode (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : FullVectorClockFinite event eps n ps sL sR)
    (root : a∈visibleRoots (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR)) :
    actualZeroClockMode event eps n ps sL sR a≠0 ∧
      (zeroClockPencil event eps n).map (Polynomial.eval a)*ᵥactualZeroClockMode event eps n ps sL sR a=0 := by
  have observed : a∈visibleRoots (readFraction
      (dotProduct (fun i => Polynomial.C (ActualCompositeFieldCurrent.compositeCurrent pd dL dR i))
        (zeroClockSourceVector event eps n ps sL sR)) (zeroClockFrequencyDenominator event eps n)) := by
    rw [actual_zero_clock_vector_observer]
    exact root
  exact ⟨source_pole_mode_nonzero _ _ _ _ observed,
    source_visible_full_kernel _ _ _ _ _ _ (actual_zero_clock_threshold_equation event eps n ps sL sR balanced finite) observed⟩

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

/-- The kernel is of the source-generated actual P limit; its separate original clearing chart remains explicit. -/
theorem actual_zero_clock_threshold_kernel (event : DressedEvent) (eps s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (balanced : PencilClockBalanced event eps n) (finite : FullVectorClockFinite event eps n ps sL sR)
    (clearingRegular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR)) :
    zeroClockThresholdPencil event eps s n*ᵥactualZeroClockMode event eps n ps sL sR (s : ℂ)=0 :=
  divided_matrix_kernel _ _ _ clearingRegular
    (actual_zero_clock_full_mode event eps n pd ps dL dR sL sR (s : ℂ) balanced finite root).2

/-- Original quantum feedback reaches the same full threshold mode with the original sigma normalizer. -/
theorem actual_zero_clock_mode_quantum_return (event : DressedEvent) (eps s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (balanced : PencilClockBalanced event eps n) (finite : FullVectorClockFinite event eps n ps sL sR)
    (clearingRegular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR)) :
    let v := actualZeroClockMode event eps n ps sL sR (s : ℂ)
    Tendsto (fun sigma : ℝ => (sigma : ℂ) •
      (frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (emOriginalJacobi (frequencyRay eps s n)*ᵥv)) := by
  dsimp only
  let v := actualZeroClockMode event eps n ps sL sR (s : ℂ)
  have continuous : Continuous (fun M : Matrix (Fin 289) (Fin 289) ℂ => M*ᵥv) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have limit := (continuous.tendsto _).comp (actual_zero_clock_threshold_pencil event eps s n clearingRegular balanced)
  rw [actual_zero_clock_threshold_kernel event eps s n pd ps dL dR sL sR balanced finite clearingRegular root] at limit
  have constant : Tendsto (fun _ : ℝ => emOriginalJacobi (frequencyRay eps s n)*ᵥv)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (emOriginalJacobi (frequencyRay eps s n)*ᵥv)) := tendsto_const_nhds
  have full := constant.sub limit
  simp only [Function.comp_def,sub_zero] at full
  apply Tendsto.congr' _ full
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  rw [damped_source_sheet_response event eps s sigma n positive,Matrix.sub_mulVec,Matrix.smul_mulVec]
  abel

/-- All nine original cokernel rows retain forcing versus quantum responsibility at this actual threshold. -/
theorem actual_zero_clock_mode_nine_return (event : DressedEvent) (eps s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (balanced : PencilClockBalanced event eps n) (finite : FullVectorClockFinite event eps n ps sL sR)
    (clearingRegular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR)) (j : Fin 9) :
    let v := actualZeroClockMode event eps n ps sL sR (s : ℂ)
    Tendsto (fun sigma : ℝ => (sigma : ℂ)*sourceCokernel (frequencyRay eps s n)
      (frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv) j)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (sourceCokernel (frequencyRay eps s n) (emOriginalJacobi (frequencyRay eps s n)*ᵥv) j)) := by
  dsimp only
  let v := actualZeroClockMode event eps n ps sL sR (s : ℂ)
  have continuous : Continuous (fun a : Fin 289 → ℂ => sourceCokernel (frequencyRay eps s n) a j) :=
    (continuous_apply j).comp ((sourceCokernel (frequencyRay eps s n)).toContinuousLinearMap.continuous)
  have limit := (continuous.tendsto _).comp
    (actual_zero_clock_mode_quantum_return event eps s n pd ps dL dR sL sR balanced finite clearingRegular root)
  simpa only [Function.comp_def,map_smul,Pi.smul_apply,smul_eq_mul] using limit

structure FullZeroClockMode (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (a : ℂ) where
  mode : Fin 289 → ℂ
  generated : mode=actualZeroClockMode event eps n ps sL sR a
  nonzero : mode≠0
  homogeneous : (zeroClockPencil event eps n).map (Polynomial.eval a)*ᵥmode=0
  electromagnetic : ModeEMDisposition mode
  complete : mode=emInsertion*ᵥemCoordinateCurrent mode+emCurrentResidual mode
  residual : emInsertion.transpose*ᵥemCurrentResidual mode=0
  clearing : PoleClearingDisposition (zeroClockClearing event eps n) a
  preparations : PreparedProbe dL ∧ PreparedProbe dR ∧ PreparedProbe sL ∧ PreparedProbe sR
  principals : Fin 289 → ℕ × List ℂ
  principals_generated : principals=zeroClockVectorPrincipalData event eps n ps sL sR a

def sourceFullZeroClockMode (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : FullVectorClockFinite event eps n ps sL sR)
    (root : a∈visibleRoots (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR)) :
    FullZeroClockMode event eps n pd ps dL dR sL sR a := by
  let v := actualZeroClockMode event eps n ps sL sR a
  have paid := actual_zero_clock_full_mode event eps n pd ps dL dR sL sR a balanced finite root
  exact ⟨v,rfl,paid.1,paid.2,sourceModeEMDisposition v,
    (source_mode_full_decomposition v).1,(source_mode_full_decomposition v).2,
    sourcePoleClearingDisposition _ a,
    ⟨actual_prepared_probe dL,actual_prepared_probe dR,actual_prepared_probe sL,actual_prepared_probe sR⟩,
    zeroClockVectorPrincipalData event eps n ps sL sR a,rfl⟩

inductive FullClockReturn (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Type
  | singular (zero : frequencyClockDeterminant event eps n=0)
  | observerClock (nonzero : frequencyClockDeterminant event eps n≠0)
      (failure : ¬FrequencyClockFinite event eps n pd ps dL dR sL sR)
  | vectorClock (nonzero : frequencyClockDeterminant event eps n≠0)
      (observer : FrequencyClockFinite event eps n pd ps dL dR sL sR)
      (failure : ¬FullVectorClockFinite event eps n ps sL sR)
      (pole : ∃i, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
        0<poleOrder (readFraction (clockSpecialize s (fullClockSourceVector event eps n ps sL sR i))
          (clockSpecialize s (frequencyClockDeterminant event eps n))) 0)
  | thresholdClock (nonzero : frequencyClockDeterminant event eps n≠0)
      (observer : FrequencyClockFinite event eps n pd ps dL dR sL sR)
      (vector : FullVectorClockFinite event eps n ps sL sR)
      (failure : ¬PencilClockBalanced event eps n)
      (pole : ∃i j, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
        0<poleOrder (readFraction (clockSpecialize s (fullClockPencil event eps n i j))
          (clockSpecialize s (fullClockClearing event eps n))) 0)
  | realized (nonzero : frequencyClockDeterminant event eps n≠0)
      (observer : FrequencyClockFinite event eps n pd ps dL dR sL sR)
      (vector : FullVectorClockFinite event eps n ps sL sR)
      (balanced : PencilClockBalanced event eps n)
      (modes : Multiset (Σa : ℂ, FullZeroClockMode event eps n pd ps dL dR sL sR a))
      (response_return : ∀s : ℝ, (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0 →
        Tendsto (fun sigma : ℝ => correctedProbeResponse event eps s sigma n ps sL sR)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockVectorRead event eps s n ps sL sR)))
      (pencil_return : ∀s : ℝ, (zeroClockClearing event eps n).eval (s : ℂ)≠0 →
        Tendsto (fun sigma : ℝ => frequencyResponsePencil event ((eps^2 : ℝ) • n)
          (frequencyRay eps s n) (dampedFourierClock (sourceFrequency eps s) sigma))
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockThresholdPencil event eps s n)))

/-- Extra full-vector and threshold responsibilities refine the original source return without replacing its branches. -/
def sourceFullClockReturn (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : FullClockReturn event eps n pd ps dL dR sL sR := by
  classical
  match sourceFrequencyClockReturn event eps n pd ps dL dR sL sR with
  | .singular zero => exact .singular zero
  | .clockResponsibility nonzero failure => exact .observerClock nonzero failure
  | .finite nonzero observer _ _ =>
    by_cases vector : FullVectorClockFinite event eps n ps sL sR
    · by_cases balanced : PencilClockBalanced event eps n
      · exact .realized nonzero observer vector balanced
          ((visibleRoots (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR)).attach.map
            (fun a => ⟨a.val,sourceFullZeroClockMode event eps n pd ps dL dR sL sR a.val balanced vector a.property⟩))
          (fun s regular => actual_zero_clock_full_vector event eps s n ps sL sR regular vector)
          (fun s regular => actual_zero_clock_threshold_pencil event eps s n regular balanced)
      · exact .thresholdClock nonzero observer vector balanced (source_pencil_clock_failure event eps n balanced)
    · exact .vectorClock nonzero observer vector (source_full_vector_clock_failure event eps n ps sL sR nonzero vector)

end LowEnergy.GaussComposite.ActualDressedZeroClockVector
