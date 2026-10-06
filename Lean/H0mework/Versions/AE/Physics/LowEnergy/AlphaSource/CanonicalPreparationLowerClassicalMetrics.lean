import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerClassicalRawFields

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerClassical
open PreparationVacuumRationalW PreparationVacuumCoframeBudget
open PreparationScalarCoordinates PreparationVacuumLowerLeaves
open GaussNativeEnergy GaussHistoryHilbert SourceQuantumConfigurationHilbert
open scoped BigOperators ContDiff Topology Matrix


section NativeFields
open SaturationMonoid.PhysicsCore
open PreparationVacuumCoefficientBudget PreparationVacuumPrimitiveMatrix PreparationVacuumPrincipalBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumCentralBudget PreparationVacuumEngineBudget
open PreparationVacuumClockSymbol PreparationVacuumEngineSmooth PreparationVacuumMoyalBudget
open PreparationCoordinates PreparationChartGuard PreparationVacuumSourceChartBudget
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open SU7MotherLieAlgebra StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorYukawaMassSpectrum
open StageNineExteriorMotherLieRepresentation SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal
open CanonicalPreparationCutoff
open scoped RealInnerProductSpace

def phiColumn : RectSymbol 70 1 := fun x i _ =>
  scalarRealify (vacuum+sourceScalar x) i

def scalarLinear (i : Fin 70) : Phase →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (scalarRealify.toLinearMap.toContinuousLinearMap.comp sourceScalar)

theorem phiColumn_formula (x : Phase) (i : Fin 70) (j : Fin 1) :
    phiColumn x i j=scalarRealify vacuum i+scalarLinear i x := by
  simp [phiColumn,scalarLinear]

theorem phiColumn_smooth : RectSmooth phiColumn := by
  intro i j
  simp only [phiColumn_formula]
  exact contDiffOn_const.add (scalarLinear i).contDiff.contDiffOn

def phiArray : ArrayBound := affineArray 919 1

theorem phiColumn_budget (x : Phase) (box : x.1∈sourceClosedBox) (M : ℕ) :
    MatrixBound phiColumn M phiArray x := by
  have total : ∀ m,∀ w : Word m,
      (∑ i : Fin 70,|PreparationVacuumCanonicalMoyal.jet m (fun y => phiColumn y i 0) w x|) ≤ phiArray m := by
    intro m w
    cases m with
    | zero =>
      simp only [PreparationVacuumCanonicalMoyal.jet,iteratedFDeriv_zero_apply]
      change scalarL1 (vacuum+sourceScalar x) ≤ 919
      have triangle : scalarL1 (vacuum+sourceScalar x) ≤ scalarL1 vacuum+scalarL1 (sourceScalar x) := by
        unfold scalarL1
        simp only [map_add,Pi.add_apply,←Finset.sum_add_distrib]
        exact Finset.sum_le_sum (fun i _ => abs_add_le _ _)
      rw [original_vacuum_norm] at triangle
      linarith [sourceScalar_box_L1 x box]
    | succ m => cases m with
      | zero =>
        have one (i : Fin 70) : PreparationVacuumCanonicalMoyal.jet 1 (fun y => phiColumn y i 0) w x=scalarLinear i (PreparationVacuumCanonicalMoyal.slotDirection (w 0)) := by
          simp only [phiColumn_formula]
          simp only [PreparationVacuumCanonicalMoyal.jet,iteratedFDeriv_one_apply]
          change (fderiv ℝ (fun y => scalarRealify vacuum i+scalarLinear i y) x) (PreparationVacuumCanonicalMoyal.slotDirection (w 0))=_
          rw [fderiv_const_add]
          exact congrArg (fun f : Phase →L[ℝ] ℝ => f (PreparationVacuumCanonicalMoyal.slotDirection (w 0))) (scalarLinear i).fderiv
        simp only [one]
        exact sourceScalar_direction_L1 (w 0)
      | succ m =>
        have zero (i : Fin 70) : PreparationVacuumCanonicalMoyal.jet (m+2) (fun y => phiColumn y i 0) w x=0 := by
          simp only [phiColumn_formula]
          unfold PreparationVacuumCanonicalMoyal.jet
          rw [iteratedFDeriv_succ_apply_right]
          simp only [fderiv_const_add,ContinuousLinearMap.fderiv]
          rw [iteratedFDeriv_const_of_ne (by omega)]
          simp
        simp only [zero,abs_zero,Finset.sum_const_zero,phiArray,affineArray,le_refl]
  intro m hm w
  constructor
  · intro i
    simpa only [Fin.sum_univ_one] using
      (Finset.single_le_sum (fun j _ => abs_nonneg (PreparationVacuumCanonicalMoyal.jet m (fun y => phiColumn y j 0) w x))
        (Finset.mem_univ i)).trans (total m w)
  · intro j
    fin_cases j
    exact total m w


open GaussLiveMomentum SourceQuantumConfigurationHilbert

def connectionLinear : Fin 36 → (Phase →L[ℝ] ℝ) :=
  ![0,phaseCoordinate 67,phaseCoordinate 68,phaseCoordinate 69,phaseCoordinate 70,phaseCoordinate 71,
    0,phaseCoordinate 72,phaseCoordinate 73,phaseCoordinate 74,phaseCoordinate 75,phaseCoordinate 76,
    phaseCoordinate 77,phaseCoordinate 78,phaseCoordinate 79,phaseCoordinate 80,phaseCoordinate 81,phaseCoordinate 82,
    0,phaseCoordinate 83,phaseCoordinate 84,phaseCoordinate 85,phaseCoordinate 86,phaseCoordinate 87,
    phaseCoordinate 88,phaseCoordinate 89,phaseCoordinate 90,phaseCoordinate 91,phaseCoordinate 92,phaseCoordinate 93,
    phaseCoordinate 94,phaseCoordinate 95,phaseCoordinate 96,phaseCoordinate 97,phaseCoordinate 98,phaseCoordinate 99]

theorem connectionLinear_source (x : Phase) (j : Fin 36) :
    connectionLinear j x=rawCoordinates
      (GaussNativePotential.connectionField (fullCoordinates.symm x.1) (spatialRow j)) (nativeRow j) := by
  change connectionLinear j x=gaugeRaw (gaugeFree.symm (splitCoordinates x.1).2.2).val j
  rw [decode_original_rows]
  fin_cases j <;> rfl

theorem connectionLinear_coordinate (j : Fin 36) :
    connectionLinear j=0 ∨ ∃ k,connectionLinear j=phaseCoordinate k := by
  fin_cases j
  all_goals first | exact Or.inl rfl | exact Or.inr ⟨_,rfl⟩

def AentryArray : ArrayBound := affineArray 15 1

theorem connectionLinear_budget (j : Fin 36) (x : Phase) (box : x.1∈sourceClosedBox) (M : ℕ) :
    FiniteBound (connectionLinear j) M AentryArray x := by
  intro m hm w
  rcases connectionLinear_coordinate j with zero|⟨k,same⟩
  · rw [zero]
    exact (finite_constant 0 0 (by simp) M x m hm w).trans
      (by simpa [constantArray,AentryArray] using affineArray_nonnegative 15 1 (by norm_num) (by norm_num) m)
  · rw [same]
    cases m with
    | zero => exact source_coordinate_j15 x box k
    | succ m => cases m with
      | zero =>
        have one : PreparationVacuumCanonicalMoyal.jet 1 (phaseCoordinate k) w x=phaseCoordinate k (PreparationVacuumCanonicalMoyal.slotDirection (w 0)) := linear_jet_one _ _ _
        have direction : phaseCoordinate k (PreparationVacuumCanonicalMoyal.slotDirection (w 0))=(if w 0=(k,false) then 1 else 0) := phaseCoordinate_direction k (w 0)
        rw [one,direction]
        split_ifs <;> norm_num [AentryArray,affineArray]
      | succ m =>
        have zero : PreparationVacuumCanonicalMoyal.jet (m+2) (phaseCoordinate k) w x=0 := linear_jet_higher _ _ _ _
        rw [zero]
        simp [AentryArray,affineArray]

def scalarActionMatrix (s : Fin 3) : RectSymbol 70 70 := fun x i j =>
  ∑ r : Fin 12,(originalRho r i j : ℝ)*connectionLinear (combinedRow s r) x

theorem scalarActionMatrix_smooth (s : Fin 3) : RectSmooth (scalarActionMatrix s) := by
  intro i j
  exact ContDiffOn.sum (fun r _ => contDiffOn_const.mul (connectionLinear (combinedRow s r)).contDiff.contDiffOn)

theorem scalarActionMatrix_source (s : Fin 3) (x : Phase) (i j : Fin 70) :
    scalarActionMatrix s x i j=scalarRealify
      (action (scalarUnit j) (GaussNativePotential.connectionField (fullCoordinates.symm x.1) s)) i := by
  have expand (a : NativeLie) : a=∑ r : Fin 12,rawCoordinates a r • originalUnit r := by
    apply rawCoordinates.injective
    simp only [map_sum,map_smul,originalUnit,LinearEquiv.apply_symm_apply]
    ext k
    simp [Pi.single_apply]
  rw [expand (GaussNativePotential.connectionField (fullCoordinates.symm x.1) s)]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  unfold scalarActionMatrix
  apply Finset.sum_congr rfl
  intro r hr
  rw [originalRho_source,connectionLinear_source,spatial_combined,native_combined]
  ring

theorem scalarActionMatrix_budget (s : Fin 3) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : x.1∈sourceClosedBox) :
    MatrixBound (scalarActionMatrix s) M (fun m => 12*AentryArray m) x := by
  have entry (m : ℕ) (w : Word m) (i j : Fin 70) :
      PreparationVacuumCanonicalMoyal.jet m (fun y => scalarActionMatrix s y i j) w x=
        ∑ r : Fin 12,(originalRho r i j : ℝ)*PreparationVacuumCanonicalMoyal.jet m (connectionLinear (combinedRow s r)) w x := by
    unfold scalarActionMatrix
    rw [jet_sum poleDomain_open Finset.univ _ (fun r _ =>
      contDiffOn_const.mul (connectionLinear (combinedRow s r)).contDiff.contDiffOn) m w x hx]
    simp_rw [PreparationVacuumEngineBudget.jet_scale _ _ (connectionLinear _).contDiff.contDiffOn m w x hx]
  have one (r : Fin 12) (j : Fin 70) :
      (∑ i,|(originalRho r i j : ℝ)|) ≤ 1 ∧ (∑ i,|(originalRho r j i : ℝ)|) ≤ 1 := by
    exact_mod_cast originalRho_norm r j
  have bound (m : ℕ) (hm : m ≤ M) (w : Word m) (f : Fin 12→Fin 70→ℝ)
      (columns : ∀ r,(∑ i,|f r i|) ≤ 1) :
      (∑ i : Fin 70,|∑ r : Fin 12,f r i*PreparationVacuumCanonicalMoyal.jet m (connectionLinear (combinedRow s r)) w x|) ≤ 12*AentryArray m := by
    calc
      _ ≤ ∑ i : Fin 70,∑ r : Fin 12,|f r i*PreparationVacuumCanonicalMoyal.jet m (connectionLinear (combinedRow s r)) w x| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ r : Fin 12,(∑ i : Fin 70,|f r i|)*|PreparationVacuumCanonicalMoyal.jet m (connectionLinear (combinedRow s r)) w x| := by
        simp_rw [abs_mul]
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
      _ ≤ ∑ r : Fin 12,AentryArray m := Finset.sum_le_sum (fun r _ => by
        have h := connectionLinear_budget (combinedRow s r) x box M m hm w
        simpa only [one_mul] using mul_le_mul (columns r) h (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      _ = _ := by simp
  intro m hm w
  simp only [entry]
  exact ⟨fun i => bound m hm w (fun r j => (originalRho r i j : ℝ)) (fun r => (one r i).2),
    fun j => bound m hm w (fun r i => (originalRho r i j : ℝ)) (fun r => (one r j).1)⟩


def gradientColumn (s : Fin 3) : RectSymbol 70 1 := fun x i _ =>
  scalarRealify (GaussNativePotential.scalarGradient (fullCoordinates.symm x.1) s) i

theorem gradientColumn_source (s : Fin 3) (x : Phase) :
    gradientColumn s x=scalarActionMatrix s x*phiColumn x := by
  ext i j
  have expand (v : Scalar) : v=∑ k : Fin 70,scalarRealify v k • scalarUnit k := by
    apply scalarRealify.injective
    simp only [map_sum,map_smul,scalarUnit_read]
    ext k
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  change scalarRealify (StageNineCoframeScalarMatterRegularity.scalarP286ActionBilinear
    (GaussNativePotential.connectionField (fullCoordinates.symm x.1) s)
    (vacuum+sourceScalar x)) i=_
  conv_lhs => rw [expand (vacuum+sourceScalar x)]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [scalarActionMatrix_source]
  change scalarRealify (vacuum+sourceScalar x) k *
    scalarRealify (action (scalarUnit k) (GaussNativePotential.connectionField (fullCoordinates.symm x.1) s)) i=_
  have linear : scalarLinear k x=scalarRealify (sourceScalar x) k := rfl
  rw [phiColumn_formula,linear,map_add]
  change (scalarRealify vacuum k+scalarRealify (sourceScalar x) k)*
    scalarRealify (action (scalarUnit k) (GaussNativePotential.connectionField (fullCoordinates.symm x.1) s)) i=_
  ring

def UiArray : ArrayBound := fun m => 12*productArray AentryArray phiArray m

theorem gradientColumn_smooth (s : Fin 3) : RectSmooth (gradientColumn s) := by
  have same : gradientColumn s=(fun y => scalarActionMatrix s y*phiColumn y) := funext (gradientColumn_source s)
  rw [same]
  exact matrix_product_smooth _ _ (scalarActionMatrix_smooth s) phiColumn_smooth

theorem gradientColumn_budget (s : Fin 3) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : x.1∈sourceClosedBox) : MatrixBound (gradientColumn s) M UiArray x := by
  have bound := finite_matrix_product (scalarActionMatrix s) phiColumn (scalarActionMatrix_smooth s)
    phiColumn_smooth M (fun m => 12*AentryArray m) phiArray
    (fun m => mul_nonneg (by norm_num) (affineArray_nonnegative 15 1 (by norm_num) (by norm_num) m))
    (affineArray_nonnegative 919 1 (by norm_num) (by norm_num)) x hx
    (scalarActionMatrix_budget s M x hx box) (phiColumn_budget x box M)
  rw [productArray_scale_left] at bound
  have same : gradientColumn s=(fun y => scalarActionMatrix s y*phiColumn y) := funext (gradientColumn_source s)
  rw [same]
  exact bound

def nextSpatial : Fin 3→Fin 3 := ![1,2,0]
def lastSpatial : Fin 3→Fin 3 := ![2,0,1]

def magneticColumn : RectSymbol 36 1 := fun x j _ =>
  rawCoordinates (GaussNativePotential.magneticField (fullCoordinates.symm x.1) (spatialRow j)) (nativeRow j)

def magneticTerm (s : Fin 3) (r j : Fin 12) : Symbol := fun x =>
  connectionLinear (combinedRow (nextSpatial s) r) x*connectionLinear (combinedRow (lastSpatial s) j) x

theorem magneticTerm_smooth (s : Fin 3) (r j : Fin 12) : SmoothSymbol (magneticTerm s r j) :=
  (connectionLinear _).contDiff.contDiffOn.mul (connectionLinear _).contDiff.contDiffOn

theorem magneticColumn_formula (x : Phase) (s : Fin 3) (i : Fin 12) (k : Fin 1) :
    magneticColumn x (combinedRow s i) k=
      ∑ r : Fin 12,∑ j : Fin 12,(originalAd r i j : ℝ)*magneticTerm s r j x := by
  have source : GaussNativePotential.magneticField (fullCoordinates.symm x.1) s=
      StageNineP286BracketCalculus.coordinateBracketBilinear
        (GaussNativePotential.connectionField (fullCoordinates.symm x.1) (nextSpatial s))
        (GaussNativePotential.connectionField (fullCoordinates.symm x.1) (lastSpatial s)) := by
    fin_cases s <;> rfl
  simp only [magneticColumn,spatial_combined,native_combined,source,original_bracket_expansion]
  simp only [magneticTerm,connectionLinear_source,spatial_combined,native_combined]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem magneticColumn_smooth : RectSmooth magneticColumn := by
  intro i k
  rw [←combined_rows i]
  simp only [magneticColumn_formula]
  exact ContDiffOn.sum (fun r _ => ContDiffOn.sum (fun j _ =>
    contDiffOn_const.mul (magneticTerm_smooth _ r j)))

def magneticFieldArray : ArrayBound := fun m => 252*powerArray AentryArray 2 m

theorem magneticColumn_budget (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : x.1∈sourceClosedBox) : MatrixBound magneticColumn M magneticFieldArray x := by
  have part (s : Fin 3) (r j : Fin 12) : FiniteBound (magneticTerm s r j) M (powerArray AentryArray 2) x := by
    rw [powerArray_two]
    exact finite_product _ _ (connectionLinear _).contDiff.contDiffOn (connectionLinear _).contDiff.contDiffOn
      AentryArray AentryArray (affineArray_nonnegative 15 1 (by norm_num) (by norm_num)) M x hx
      (connectionLinear_budget _ x box M) (connectionLinear_budget _ x box M)
  have component (s : Fin 3) (i : Fin 12) : FiniteBound (fun y => magneticColumn y (combinedRow s i) 0) M
      (fun m => (∑ r : Fin 12,∑ j : Fin 12,|(originalAd r i j : ℝ)|)*powerArray AentryArray 2 m) x := by
    have same : (fun y => magneticColumn y (combinedRow s i) 0)=
        (fun y => ∑ r : Fin 12,∑ j : Fin 12,(originalAd r i j : ℝ)*magneticTerm s r j y) := by
      funext y
      exact magneticColumn_formula y s i 0
    rw [same]
    have inner (r : Fin 12) := finite_sum Finset.univ (fun j y => (originalAd r i j : ℝ)*magneticTerm s r j y)
      (fun j _ => contDiffOn_const.mul (magneticTerm_smooth s r j))
      (fun j m => |(originalAd r i j : ℝ)| *powerArray AentryArray 2 m) M x hx
      (fun j _ => finite_scale _ _ (magneticTerm_smooth s r j) _ M x hx (part s r j))
    have total := finite_sum Finset.univ (fun r y => ∑ j : Fin 12,(originalAd r i j : ℝ)*magneticTerm s r j y)
      (fun r _ => ContDiffOn.sum (fun j _ => contDiffOn_const.mul (magneticTerm_smooth s r j)))
      (fun r m => ∑ j : Fin 12,|(originalAd r i j : ℝ)| *powerArray AentryArray 2 m) M x hx (fun r _ => inner r)
    simpa only [Finset.sum_mul] using total
  have originalTotal : (∑ i : Fin 12,∑ r : Fin 12,∑ j : Fin 12,|(originalAd r i j : ℝ)|)=84 := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (f:=fun i j => |(originalAd _ i j : ℝ)|)]
    exact_mod_cast originalBracket_absolute_sum
  have total (m : ℕ) (hm : m ≤ M) (w : Word m) :
      (∑ i : Fin 36,|PreparationVacuumCanonicalMoyal.jet m (fun y => magneticColumn y i 0) w x|) ≤ magneticFieldArray m := by
    rw [←gaugeRowEquiv.sum_comp]
    simp only [gaugeRowEquiv,Fintype.sum_prod_type]
    calc
      _ ≤ ∑ s : Fin 3,∑ i : Fin 12,(∑ r : Fin 12,∑ j : Fin 12,|(originalAd r i j : ℝ)|)*powerArray AentryArray 2 m :=
        Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun i _ => component s i m hm w))
      _ = _ := by simp only [←Finset.sum_mul,originalTotal,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,magneticFieldArray]; ring
  intro m hm w
  constructor
  · intro i
    simpa only [Fin.sum_univ_one] using
      (Finset.single_le_sum (fun j _ => abs_nonneg (PreparationVacuumCanonicalMoyal.jet m (fun y => magneticColumn y j 0) w x))
        (Finset.mem_univ i)).trans (total m hm w)
  · intro j
    fin_cases j
    exact total m hm w


theorem original_field_arrays :
    UiArray 0=165420 ∧ UiArray 1=11208 ∧ UiArray 2=24 ∧
    magneticFieldArray 0=56700 ∧ magneticFieldArray 1=7560 ∧ magneticFieldArray 2=504 := by
  norm_num [UiArray,magneticFieldArray,powerArray_two,productArray,AentryArray,phiArray,affineArray,
    Finset.sum_range_succ]

end NativeFields
open SaturationMonoid.PhysicsCore

def CSupported (c : ℚ) : Prop := |c|=1 ∨ |c|=2 ∨ |c|=4
instance : DecidablePred CSupported := fun _ => by unfold CSupported; infer_instance

def cCeiling (c : ℚ) : ℕ := if |c|=1 then 2 else if |c|=2 then 4 else 7

theorem original_n_ceiling (c : ℚ) (supported : CSupported c) :
    ⌈|(c : ℝ)|/N⌉₊=cCeiling c := by
  rcases supported with h|h|h
  · have real : |(c : ℝ)|=1 := by exact_mod_cast h
    rw [real,cCeiling,if_pos h,Nat.ceil_eq_iff (by decide)]
    norm_num
    constructor
    · rw [←one_div,lt_div_iff₀ N_positive]; nlinarith [N_bounds.2]
    · rw [←one_div,div_le_iff₀ N_positive]; nlinarith [N_bounds.1]
  · have real : |(c : ℝ)|=2 := by exact_mod_cast h
    have ne : ¬|c|=1 := by rw [h]; norm_num
    rw [real,cCeiling,if_neg ne,if_pos h,Nat.ceil_eq_iff (by decide)]
    norm_num
    constructor
    · rw [lt_div_iff₀ N_positive]; nlinarith [N_bounds.2]
    · rw [div_le_iff₀ N_positive]; nlinarith [N_bounds.1]
  · have real : |(c : ℝ)|=4 := by exact_mod_cast h
    have n1 : ¬|c|=1 := by rw [h]; norm_num
    have n2 : ¬|c|=2 := by rw [h]; norm_num
    rw [real,cCeiling,if_neg n1,if_neg n2,Nat.ceil_eq_iff (by decide)]
    norm_num
    constructor
    · rw [lt_div_iff₀ N_positive]; nlinarith [N_bounds.2]
    · rw [div_le_iff₀ N_positive]; nlinarith [N_bounds.1]

theorem actual_n_coefficient (c : ℚ) (supported : CSupported c)
    (n : ℝ) (b : Fin 3→ℝ) (time : TimeBox n b) : |(c : ℝ)/n| ≤ (cCeiling c : ℝ) := by
  rw [abs_div,abs_of_pos (time_positive n b time).1]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) N_positive time.lower).trans (by
    rw [←original_n_ceiling c supported]
    exact Nat.le_ceil _)

def cTimeValue (ts : TimeTerms) (n : ℝ) (b : Fin 3→ℝ) : ℝ :=
  (ts.map (fun t => ((t.1 : ℝ)/n)*timeMonomial t.2 n b)).sum

def cTimeAmplitude (ts : TimeTerms) : ℕ := (ts.map (fun t => cCeiling t.1*2^(t.2 0))).sum

theorem cTimeValue_budget (ts : TimeTerms) (supported : ∀ t∈ts,CSupported t.1)
    (n : ℝ) (b : Fin 3→ℝ) (time : TimeBox n b) :
    |cTimeValue ts n b| ≤ (cTimeAmplitude ts : ℝ) := by
  induction ts with
  | nil => simp [cTimeValue,cTimeAmplitude]
  | cons t ts ih =>
    have bound := mul_le_mul (actual_n_coefficient t.1 (supported t (by simp)) n b time)
      (time_monomial_bound t.2 n b time) (abs_nonneg _) (Nat.cast_nonneg _)
    change |((t.1 : ℝ)/n)*timeMonomial t.2 n b+cTimeValue ts n b| ≤ _
    refine (abs_add_le _ _).trans ((add_le_add (by simpa only [abs_mul] using bound)
      (ih (fun t ht => supported t (by simp [ht])))).trans_eq ?_)
    simp [cTimeAmplitude,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]

structure CEntry where
  numerator : QTimeTerms
  poles : Powers

def cNumerator (ts : QTimeTerms) (n : ℝ) (b : Fin 3→ℝ) : Symbol := fun x =>
  (ts.map (fun t => cTimeValue t.1 n b*monomial false t.2 x)).sum

def cNumeratorArray (ts : QTimeTerms) (m : ℕ) : ℕ :=
  (ts.map (fun t => cTimeAmplitude t.1*(degree t.2).descFactorial m*15^(degree t.2-m))).sum

def cValue (e : CEntry) (n : ℝ) (b : Fin 3→ℝ) : Symbol := fun x =>
  cNumerator e.numerator n b x*monomial true e.poles x

def cArray (e : CEntry) (m : ℕ) : ℕ :=
  ∑ k∈Finset.range (m+1),m.choose k*cNumeratorArray e.numerator k*reciprocalArray (degree e.poles) (m-k)

def CEntrySupported (e : CEntry) : Prop := poleSupported e.poles ∧
  ∀ t∈e.numerator,∀ u∈t.1,CSupported u.1

instance (e : CEntry) : Decidable (CEntrySupported e) := by
  unfold CEntrySupported poleSupported CSupported
  infer_instance

theorem cNumerator_smooth (ts : QTimeTerms) (n : ℝ) (b : Fin 3 → ℝ) :
    ContDiffOn ℝ ∞ (cNumerator ts n b) coframeDomain := by
  induction ts with
  | nil => exact contDiffOn_const
  | cons t ts ih => exact (contDiffOn_const.mul (monomial_smooth false t.2 (by simp))).add ih

theorem cValue_smooth (e : CEntry) (supported : CEntrySupported e) (n : ℝ) (b : Fin 3 → ℝ) :
    ContDiffOn ℝ ∞ (cValue e n b) coframeDomain :=
  (cNumerator_smooth e.numerator n b).mul (monomial_smooth true e.poles (fun _ => supported.1))

theorem cNumerator_budget (ts : QTimeTerms)
    (supported : ∀ t∈ts,∀ u∈t.1,CSupported u.1)
    (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈coframeDomain) (bound : ∀ i,|qCoordinate i x| ≤ 15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹| ≤ 15) :
    |jet m (cNumerator ts n b) w x| ≤ (cNumeratorArray ts m : ℝ) := by
  induction ts with
  | nil =>
    rw [show cNumerator [] n b=(fun _ : Phase => 0) by funext y; rfl,jet_zero]
    simp [cNumeratorArray]
  | cons t ts ih =>
    have smooth := (monomial_smooth false t.2 (by simp) x hx).contDiffAt (coframeDomain_open.mem_nhds hx)
    have tail := (cNumerator_smooth ts n b x hx).contDiffAt (coframeDomain_open.mem_nhds hx)
    have read : jet m (cNumerator (t::ts) n b) w x=
        cTimeValue t.1 n b*jet m (monomial false t.2) w x+jet m (cNumerator ts n b) w x := by
      change jet m (fun y => cTimeValue t.1 n b*monomial false t.2 y+cNumerator ts n b y) w x=_
      rw [jet_add _ _ _ _ _ (contDiffAt_const.mul smooth) tail,jet_scale _ _ _ _ _ smooth]
    rw [read]
    have estimate := mul_le_mul (cTimeValue_budget t.1 (supported t (by simp)) n b time)
      (actual_monomial_budget false t.2 (by simp) m w x hx bound inverse) (abs_nonneg _) (Nat.cast_nonneg _)
    refine (abs_add_le _ _).trans ((add_le_add (by simpa only [abs_mul] using estimate)
      (ih (fun t ht => supported t (by simp [ht])))).trans_eq ?_)
    simp [cNumeratorArray,monomialBound,numeratorBound,Nat.cast_add,Nat.cast_mul,mul_assoc]

theorem cValue_budget (e : CEntry) (supported : CEntrySupported e)
    (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈coframeDomain) (bound : ∀ i,|qCoordinate i x| ≤ 15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹| ≤ 15) :
    |jet m (cValue e n b) w x| ≤ (cArray e m : ℝ) := by
  have result := product_jet_budget (cNumerator e.numerator n b) (monomial true e.poles)
    (cNumerator_smooth e.numerator n b) (monomial_smooth true e.poles (fun _ => supported.1))
    (fun m => (cNumeratorArray e.numerator m : ℝ)) (fun m => (reciprocalArray (degree e.poles) m : ℝ))
    (fun _ => Nat.cast_nonneg _) x hx
    (fun m w => cNumerator_budget e.numerator supported.2 n b time m w x hx bound inverse)
    (fun m w => by simpa [reciprocalArray,monomialBound,reciprocalBound] using
      actual_monomial_budget true e.poles (fun _ => supported.1) m w x hx bound inverse) m w
  exact result.trans_eq (by simp [convolution,cArray,Nat.cast_sum,Nat.cast_mul])


def shiftEntries : Matrix (Fin 1) (Fin 3) CEntry :=
  !![⟨[([(1,![0,1,0,0])],![0,0,1,0,0,1])],![0,0,0,0,0,0]⟩, ⟨[([(1,![0,0,1,0])],![1,0,0,0,0,1]),([(-1,![0,1,0,0])],![0,1,0,0,0,1])],![0,0,0,0,0,0]⟩, ⟨[([(1,![0,0,0,1])],![1,0,1,0,0,0]),([(-1,![0,0,1,0])],![1,0,0,0,1,0]),([(1,![0,1,0,0])],![0,1,0,0,1,0]),([(-1,![0,1,0,0])],![0,0,1,1,0,0])],![0,0,0,0,0,0]⟩]

theorem shift_supported (i : Fin 1) (j : Fin 3) : CEntrySupported (shiftEntries i j) := by
  revert i j
  decide +kernel

def metricEntries : Matrix (Fin 3) (Fin 3) CEntry :=
  !![⟨[([(1,![2,0,0,0]),(-1,![0,2,0,0])],![0,0,1,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([(-1,![0,1,1,0])],![1,0,0,0,0,1]),([(-1,![2,0,0,0]),(1,![0,2,0,0])],![0,1,0,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([(-1,![0,1,0,1])],![1,0,1,0,0,0]),([(1,![0,1,1,0])],![1,0,0,0,1,0]),([(1,![2,0,0,0]),(-1,![0,2,0,0])],![0,1,0,0,1,0]),([(-1,![2,0,0,0]),(1,![0,2,0,0])],![0,0,1,1,0,0])],![1,0,0,0,0,0]⟩;
    ⟨[([(-1,![0,1,1,0])],![1,0,0,0,0,1]),([(-1,![2,0,0,0]),(1,![0,2,0,0])],![0,1,0,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([(1,![2,0,0,0]),(-1,![0,0,2,0])],![2,0,0,0,0,1]),([(2,![0,1,1,0])],![1,1,0,0,0,1]),([(1,![2,0,0,0]),(-1,![0,2,0,0])],![0,2,0,0,0,1])],![1,0,1,0,0,0]⟩, ⟨[([(-1,![0,0,1,1])],![2,0,1,0,0,0]),([(-1,![2,0,0,0]),(1,![0,0,2,0])],![2,0,0,0,1,0]),([(1,![0,1,0,1])],![1,1,1,0,0,0]),([(-2,![0,1,1,0])],![1,1,0,0,1,0]),([(1,![0,1,1,0])],![1,0,1,1,0,0]),([(-1,![2,0,0,0]),(1,![0,2,0,0])],![0,2,0,0,1,0]),([(1,![2,0,0,0]),(-1,![0,2,0,0])],![0,1,1,1,0,0])],![1,0,1,0,0,0]⟩;
    ⟨[([(-1,![0,1,0,1])],![1,0,1,0,0,0]),([(1,![0,1,1,0])],![1,0,0,0,1,0]),([(1,![2,0,0,0]),(-1,![0,2,0,0])],![0,1,0,0,1,0]),([(-1,![2,0,0,0]),(1,![0,2,0,0])],![0,0,1,1,0,0])],![1,0,0,0,0,0]⟩, ⟨[([(-1,![0,0,1,1])],![2,0,1,0,0,0]),([(-1,![2,0,0,0]),(1,![0,0,2,0])],![2,0,0,0,1,0]),([(1,![0,1,0,1])],![1,1,1,0,0,0]),([(-2,![0,1,1,0])],![1,1,0,0,1,0]),([(1,![0,1,1,0])],![1,0,1,1,0,0]),([(-1,![2,0,0,0]),(1,![0,2,0,0])],![0,2,0,0,1,0]),([(1,![2,0,0,0]),(-1,![0,2,0,0])],![0,1,1,1,0,0])],![1,0,1,0,0,0]⟩, ⟨[([(1,![2,0,0,0]),(-1,![0,0,0,2])],![2,0,2,0,0,0]),([(2,![0,0,1,1])],![2,0,1,0,1,0]),([(1,![2,0,0,0]),(-1,![0,0,2,0])],![2,0,0,0,2,0]),([(-2,![0,1,0,1])],![1,1,1,0,1,0]),([(2,![0,1,1,0])],![1,1,0,0,2,0]),([(2,![0,1,0,1])],![1,0,2,1,0,0]),([(-2,![0,1,1,0])],![1,0,1,1,1,0]),([(1,![2,0,0,0]),(-1,![0,2,0,0])],![0,2,0,0,2,0]),([(-2,![2,0,0,0]),(2,![0,2,0,0])],![0,1,1,1,1,0]),([(1,![2,0,0,0]),(-1,![0,2,0,0])],![0,0,2,2,0,0])],![1,0,1,0,0,1]⟩]

theorem metric_supported (i : Fin 3) (j : Fin 3) : CEntrySupported (metricEntries i j) := by
  revert i j
  decide +kernel

def mixedEntries : Matrix (Fin 3) (Fin 3) CEntry :=
  !![⟨[([(2,![0,0,0,1])],![0,1,0,0,0,0]),([(-2,![0,0,1,0])],![0,0,0,1,0,0])],![1,0,0,0,0,0]⟩, ⟨[([(-2,![0,0,0,1])],![2,0,0,0,0,0]),([(2,![0,1,0,0])],![1,0,0,1,0,0]),([(-2,![0,0,0,1])],![0,2,0,0,0,0]),([(2,![0,0,1,0])],![0,1,0,1,0,0])],![1,0,1,0,0,0]⟩, ⟨[([(2,![0,0,1,0])],![2,0,1,0,0,0]),([(2,![0,0,0,1])],![2,0,0,0,1,0]),([(-2,![0,1,0,0])],![1,1,1,0,0,0]),([(-2,![0,1,0,0])],![1,0,0,1,1,0]),([(2,![0,0,0,1])],![0,2,0,0,1,0]),([(-2,![0,0,0,1])],![0,1,1,1,0,0]),([(-2,![0,0,1,0])],![0,1,0,1,1,0]),([(2,![0,0,1,0])],![0,0,1,2,0,0])],![1,0,1,0,0,1]⟩;
    ⟨[([(2,![0,0,0,1])],![0,0,1,0,0,0]),([(-2,![0,0,1,0])],![0,0,0,0,1,0])],![1,0,0,0,0,0]⟩, ⟨[([(2,![0,1,0,0])],![1,0,0,0,1,0]),([(-2,![0,0,0,1])],![0,1,1,0,0,0]),([(2,![0,0,1,0])],![0,1,0,0,1,0])],![1,0,1,0,0,0]⟩, ⟨[([(-2,![0,1,0,0])],![1,0,2,0,0,0]),([(-2,![0,1,0,0])],![1,0,0,0,2,0]),([(2,![0,0,0,1])],![0,1,1,0,1,0]),([(-2,![0,0,1,0])],![0,1,0,0,2,0]),([(-2,![0,0,0,1])],![0,0,2,1,0,0]),([(2,![0,0,1,0])],![0,0,1,1,1,0])],![1,0,1,0,0,1]⟩;
    ⟨[([(-2,![0,0,1,0])],![0,0,0,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([(2,![0,1,0,0])],![1,0,0,0,0,1]),([(2,![0,0,1,0])],![0,1,0,0,0,1])],![1,0,1,0,0,0]⟩, ⟨[([(-2,![0,1,0,0])],![1,0,0,0,1,0]),([(-2,![0,0,1,0])],![0,1,0,0,1,0]),([(2,![0,0,1,0])],![0,0,1,1,0,0])],![1,0,1,0,0,0]⟩]

theorem mixed_supported (i : Fin 3) (j : Fin 3) : CEntrySupported (mixedEntries i j) := by
  revert i j
  decide +kernel

def magneticEntries : Matrix (Fin 3) (Fin 3) CEntry :=
  !![⟨[([(-2,![0,0,0,0])],![0,0,1,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([(2,![0,0,0,0])],![0,1,0,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([(-2,![0,0,0,0])],![0,1,0,0,1,0]),([(2,![0,0,0,0])],![0,0,1,1,0,0])],![1,0,0,0,0,0]⟩;
    ⟨[([(2,![0,0,0,0])],![0,1,0,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([(-2,![0,0,0,0])],![2,0,0,0,0,1]),([(-2,![0,0,0,0])],![0,2,0,0,0,1])],![1,0,1,0,0,0]⟩, ⟨[([(2,![0,0,0,0])],![2,0,0,0,1,0]),([(2,![0,0,0,0])],![0,2,0,0,1,0]),([(-2,![0,0,0,0])],![0,1,1,1,0,0])],![1,0,1,0,0,0]⟩;
    ⟨[([(-2,![0,0,0,0])],![0,1,0,0,1,0]),([(2,![0,0,0,0])],![0,0,1,1,0,0])],![1,0,0,0,0,0]⟩, ⟨[([(2,![0,0,0,0])],![2,0,0,0,1,0]),([(2,![0,0,0,0])],![0,2,0,0,1,0]),([(-2,![0,0,0,0])],![0,1,1,1,0,0])],![1,0,1,0,0,0]⟩, ⟨[([(-2,![0,0,0,0])],![2,0,2,0,0,0]),([(-2,![0,0,0,0])],![2,0,0,0,2,0]),([(-2,![0,0,0,0])],![0,2,0,0,2,0]),([(4,![0,0,0,0])],![0,1,1,1,1,0]),([(-2,![0,0,0,0])],![0,0,2,2,0,0])],![1,0,1,0,0,1]⟩]

theorem magnetic_supported (i : Fin 3) (j : Fin 3) : CEntrySupported (magneticEntries i j) := by
  revert i j
  decide +kernel


def cMatrixArray {a b : ℕ} (E : Matrix (Fin a) (Fin b) CEntry) (m : ℕ) : ℕ :=
  max (Finset.univ.sup (fun i => ∑ j,cArray (E i j) m))
    (Finset.univ.sup (fun j => ∑ i,cArray (E i j) m))

def shiftArray : PreparationVacuumCentralBudget.ArrayBound := fun m => cMatrixArray shiftEntries m
def metricArray : PreparationVacuumCentralBudget.ArrayBound := fun m => cMatrixArray metricEntries m
def mixedArray : PreparationVacuumCentralBudget.ArrayBound := fun m => cMatrixArray mixedEntries m
def magneticMetricArray : PreparationVacuumCentralBudget.ArrayBound := fun m => cMatrixArray magneticEntries m

theorem original_classical_zeros :
    cMatrixArray shiftEntries 0=3150 ∧ cMatrixArray metricEntries 0=13699206000 ∧
    cMatrixArray mixedEntries 0=638482500 ∧ cMatrixArray magneticEntries 0=3938905125 := by
  decide +kernel

def cMatrix {a b : ℕ} (E : Matrix (Fin a) (Fin b) CEntry) (n : ℝ) (beta : Fin 3→ℝ) :
    PreparationVacuumPrincipalBudget.RectSymbol a b := fun x i j => cValue (E i j) n beta x

theorem cMatrix_budget {a b : ℕ} (E : Matrix (Fin a) (Fin b) CEntry)
    (supported : ∀ i j,CEntrySupported (E i j)) (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (box : sourceBox x) :
    PreparationVacuumPrincipalBudget.MatrixBound (cMatrix E n beta) M
      (fun m => (cMatrixArray E m : ℝ)) x := by
  intro m hm w
  have entry (i : Fin a) (j : Fin b) : |jet m (cValue (E i j) n beta) w x| ≤ (cArray (E i j) m : ℝ) :=
    cValue_budget (E i j) (supported i j) n beta time m w x (sourceBox_guards x box).1
      (sourceBox_guards x box).2.1 (sourceBox_guards x box).2.2
  constructor
  · intro i
    exact (Finset.sum_le_sum (fun j _ => entry i j)).trans (by
      have h : (∑ j,cArray (E i j) m) ≤ cMatrixArray E m := (Finset.le_sup (f:=fun i => ∑ j,cArray (E i j) m) (Finset.mem_univ i)).trans (Nat.le_max_left _ _)
      have real : ((∑ j,cArray (E i j) m : ℕ) : ℝ) ≤ (cMatrixArray E m : ℝ) := by exact_mod_cast h
      simpa only [Nat.cast_sum] using real)
  · intro j
    exact (Finset.sum_le_sum (fun i _ => entry i j)).trans (by
      have h : (∑ i,cArray (E i j) m) ≤ cMatrixArray E m := (Finset.le_sup (f:=fun j => ∑ i,cArray (E i j) m) (Finset.mem_univ j)).trans (Nat.le_max_right _ _)
      have real : ((∑ i,cArray (E i j) m : ℕ) : ℝ) ≤ (cMatrixArray E m : ℝ) := by exact_mod_cast h
      simpa only [Nat.cast_sum] using real)

theorem cMatrix_smooth {a b : ℕ} (E : Matrix (Fin a) (Fin b) CEntry)
    (supported : ∀ i j,CEntrySupported (E i j)) (n : ℝ) (beta : Fin 3→ℝ) :
    PreparationVacuumPrincipalBudget.RectSmooth (cMatrix E n beta) := by
  intro i j
  exact (cValue_smooth (E i j) (supported i j) n beta).mono
    (fun x hx => by
      have physical := (show x∈PreparationVacuumMoyalSymmetry.originalPhysicalPhase from hx.1.1)
      intro k hk
      rcases hk with rfl|rfl|rfl
      · exact physical.1.ne'
      · exact physical.2.1.ne'
      · exact physical.2.2.1.ne')


open PreparationVacuumTemporalOrdering PreparationVacuumLowerTensor

private theorem original_minkowski_inverse : minkowskiInternalMetric⁻¹=minkowskiInternalMetric := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiInternalMetric,Matrix.mul_apply,Fin.sum_univ_four]

theorem original_scalar_metric_formula (n : ℝ) (beta : Fin 3→ℝ) (z : physicalChart) (hn : n≠0) :
    originalScalarMetric n beta z.val=
      (n*volume z.val) • (generatedCoframeInverse n beta z.val.1*minkowskiInternalMetric*
        (generatedCoframeInverse n beta z.val.1).transpose) := by
  unfold originalScalarMetric lorentzianMetricOfCoframe
  rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv,original_minkowski_inverse,
    originalCoframeInverse_generated n beta z hn,coframe_determinant]
  simp only [originalTimeColumn,Matrix.mul_assoc,volume]
  rfl

theorem shift_readback (n : ℝ) (beta : Fin 3→ℝ) (hn : n≠0) (x : Phase)
    (physical : x∈PreparationVacuumMoyalSymmetry.originalPhysicalPhase) (i : Fin 3) :
    cValue (shiftEntries 0 i) n beta x=originalScalarMetric n beta (fullCoordinates.symm x.1) 0 i.succ := by
  rw [original_scalar_metric_formula n beta ⟨fullCoordinates.symm x.1,physical⟩ hn]
  have h0 : x.1 0≠0 := physical.1.ne'
  have h2 : x.1 2≠0 := physical.2.1.ne'
  have h5 : x.1 5≠0 := physical.2.2.1.ne'
  simp only [Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,smul_eq_mul,Fin.sum_univ_four]
  have q (k : Fin 6) : (fullCoordinates.symm x.1).1 k=x.1 (Fin.castAdd 94 k) := rfl
  fin_cases i <;>
    norm_num [shiftEntries,cValue,cNumerator,cTimeValue,timeMonomial,timeCoordinate,
      monomial,powerFactor,Fin.prod_univ_succ,qCoordinate,qSlot,
      generatedCoframeInverse,minkowskiInternalMetric,Matrix.diagonal,Fin.ext_iff,triadInverse,volume,q,Fin.sum_univ_three,
      Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_four,smul_eq_mul]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals field_simp [h0,h2,h5,hn]
  all_goals ring

theorem metric_readback (n : ℝ) (beta : Fin 3→ℝ) (hn : n≠0) (x : Phase)
    (physical : x∈PreparationVacuumMoyalSymmetry.originalPhysicalPhase) (i j : Fin 3) :
    cValue (metricEntries i j) n beta x=originalScalarMetric n beta (fullCoordinates.symm x.1) i.succ j.succ := by
  rw [original_scalar_metric_formula n beta ⟨fullCoordinates.symm x.1,physical⟩ hn]
  have h0 : x.1 0≠0 := physical.1.ne'
  have h2 : x.1 2≠0 := physical.2.1.ne'
  have h5 : x.1 5≠0 := physical.2.2.1.ne'
  simp only [Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,smul_eq_mul,Fin.sum_univ_four]
  have q (k : Fin 6) : (fullCoordinates.symm x.1).1 k=x.1 (Fin.castAdd 94 k) := rfl
  fin_cases i <;> fin_cases j <;>
    norm_num [metricEntries,cValue,cNumerator,cTimeValue,timeMonomial,timeCoordinate,
      monomial,powerFactor,Fin.prod_univ_succ,qCoordinate,qSlot,
      generatedCoframeInverse,minkowskiInternalMetric,Matrix.diagonal,Fin.ext_iff,triadInverse,volume,q,Fin.sum_univ_three,
      Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_four,smul_eq_mul]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals field_simp [h0,h2,h5,hn]
  all_goals ring

theorem mixed_readback (n : ℝ) (beta : Fin 3→ℝ) (x : Phase)
    (physical : x∈PreparationVacuumMoyalSymmetry.originalPhysicalPhase) (i j : Fin 3) :
    cValue (mixedEntries i j) n beta x=originalMixedBlock n beta (fullCoordinates.symm x.1) i j := by
  rw [originalMixedBlock_generated n beta ⟨fullCoordinates.symm x.1,physical⟩]
  have h0 : x.1 0≠0 := physical.1.ne'
  have h2 : x.1 2≠0 := physical.2.1.ne'
  have h5 : x.1 5≠0 := physical.2.2.1.ne'
  have sigma : sourceSigma=(1/2 : ℝ) :=
    SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.sourceCoupling_eq
  rw [sigma]
  simp only [Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,smul_eq_mul,Fin.sum_univ_three]
  have q (k : Fin 6) : (fullCoordinates.symm x.1).1 k=x.1 (Fin.castAdd 94 k) := rfl
  fin_cases i <;> fin_cases j <;>
    norm_num [mixedEntries,cValue,cNumerator,cTimeValue,timeMonomial,timeCoordinate,
      monomial,powerFactor,Fin.prod_univ_succ,qCoordinate,qSlot,
      triad,triadInverse,sourceCross,volume,q,
      Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_three,smul_eq_mul]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals field_simp [h0,h2,h5]
  all_goals ring


theorem magnetic_readback (n : ℝ) (beta : Fin 3→ℝ) (x : Phase)
    (physical : x∈PreparationVacuumMoyalSymmetry.originalPhysicalPhase) (i j : Fin 3) :
    cValue (magneticEntries i j) n beta x=originalMagneticBlock n beta (fullCoordinates.symm x.1) i j := by
  have h0 : x.1 0≠0 := physical.1.ne'
  have h2 : x.1 2≠0 := physical.2.1.ne'
  have h5 : x.1 5≠0 := physical.2.2.1.ne'
  have sigma : sourceSigma=(1/2 : ℝ) :=
    SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.sourceCoupling_eq
  unfold originalMagneticBlock
  rw [sourceBFKernel_wedge,coframe_determinant,sigma]
  have q (k : Fin 6) : (fullCoordinates.symm x.1).1 k=x.1 (Fin.castAdd 94 k) := rfl
  fin_cases i <;> fin_cases j <;>
    norm_num [magneticEntries,cValue,cNumerator,cTimeValue,timeMonomial,timeCoordinate,
      monomial,powerFactor,Fin.prod_univ_succ,qCoordinate,qSlot,volume,q,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.coframeWedge,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.pairFirst,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.pairSecond,
      SaturationMonoid.PhysicsCore.StageNineGlobalIntegratedAction.lorentzianTwoFormSign,
      coframe,originalTimeColumn,Fin.sum_univ_six]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals field_simp [h0,h2,h5]
  all_goals ring

open PreparationVacuumPrincipalBudget PreparationVacuumClockSymbol PreparationVacuumEngineSmooth
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry

def actualShift (n : ℝ) (beta : Fin 3→ℝ) : RectSymbol 1 3 := fun x _ j =>
  originalScalarMetric n beta (fullCoordinates.symm x.1) 0 j.succ

def actualMetric (n : ℝ) (beta : Fin 3→ℝ) : RectSymbol 3 3 := fun x i j =>
  originalScalarMetric n beta (fullCoordinates.symm x.1) i.succ j.succ

def actualMixed (n : ℝ) (beta : Fin 3→ℝ) : RectSymbol 3 3 := fun x =>
  originalMixedBlock n beta (fullCoordinates.symm x.1)

def actualMagnetic (n : ℝ) (beta : Fin 3→ℝ) : RectSymbol 3 3 := fun x =>
  originalMagneticBlock n beta (fullCoordinates.symm x.1)

private theorem original_matrix_transport {a b : ℕ} (E : Matrix (Fin a) (Fin b) CEntry)
    (supported : ∀ i j,CEntrySupported (E i j)) (actual : RectSymbol a b)
    (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (same : ∀ x∈originalPhysicalPhase,∀ i j,cValue (E i j) n beta x=actual x i j)
    (M : ℕ) (x : Phase) (box : sourceBox x) :
    MatrixBound actual M (fun m => cMatrixArray E m) x := by
  have physical : x∈originalPhysicalPhase := (PreparationPhaseScalar.phaseChart x.1 box).property
  have bound := cMatrix_budget E supported n beta time M x box
  intro m hm w
  have equal (i : Fin a) (j : Fin b) : PreparationVacuumCanonicalMoyal.jet m (fun y => actual y i j) w x=
      PreparationVacuumCanonicalMoyal.jet m (cValue (E i j) n beta) w x := by
    apply jet_germ
    filter_upwards [originalPhysicalPhase_open.mem_nhds physical] with y hy
    exact (same y hy i j).symm
  simp only [equal]
  exact bound m hm w

theorem actual_shift_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (box : sourceBox x) : MatrixBound (actualShift n beta) M shiftArray x :=
  original_matrix_transport shiftEntries shift_supported (actualShift n beta) n beta time
    (fun y hy i j => by fin_cases i; exact shift_readback n beta (time_positive n beta time).1.ne' y hy j) M x box

theorem actual_metric_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (box : sourceBox x) : MatrixBound (actualMetric n beta) M metricArray x :=
  original_matrix_transport metricEntries metric_supported (actualMetric n beta) n beta time
    (fun y hy i j => metric_readback n beta (time_positive n beta time).1.ne' y hy i j) M x box

theorem actual_mixed_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (box : sourceBox x) : MatrixBound (actualMixed n beta) M mixedArray x :=
  original_matrix_transport mixedEntries mixed_supported (actualMixed n beta) n beta time
    (fun y hy i j => mixed_readback n beta y hy i j) M x box

theorem actual_magnetic_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (box : sourceBox x) : MatrixBound (actualMagnetic n beta) M magneticMetricArray x :=
  original_matrix_transport magneticEntries magnetic_supported (actualMagnetic n beta) n beta time
    (fun y hy i j => magnetic_readback n beta y hy i j) M x box


private theorem original_matrix_smooth {a b : ℕ} (E : Matrix (Fin a) (Fin b) CEntry)
    (supported : ∀ i j,CEntrySupported (E i j)) (actual : RectSymbol a b)
    (n : ℝ) (beta : Fin 3→ℝ)
    (same : ∀ x∈originalPhysicalPhase,∀ i j,cValue (E i j) n beta x=actual x i j) :
    RectSmooth actual := by
  intro i j x hx
  have h := ((cMatrix_smooth E supported n beta i j) x hx).contDiffAt (poleDomain_open.mem_nhds hx)
  have equal : (fun y => actual y i j)=ᶠ[𝓝 x]cValue (E i j) n beta := by
    filter_upwards [originalPhysicalPhase_open.mem_nhds hx.1.1] with y hy
    exact (same y hy i j).symm
  exact (h.congr_of_eventuallyEq equal).contDiffWithinAt

theorem actual_shift_smooth (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta) : RectSmooth (actualShift n beta) :=
  original_matrix_smooth shiftEntries shift_supported (actualShift n beta) n beta
    (fun y hy i j => by fin_cases i; exact shift_readback n beta (time_positive n beta time).1.ne' y hy j)

theorem actual_metric_smooth (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta) : RectSmooth (actualMetric n beta) :=
  original_matrix_smooth metricEntries metric_supported (actualMetric n beta) n beta
    (fun y hy i j => metric_readback n beta (time_positive n beta time).1.ne' y hy i j)

theorem actual_mixed_smooth (n : ℝ) (beta : Fin 3→ℝ) : RectSmooth (actualMixed n beta) :=
  original_matrix_smooth mixedEntries mixed_supported (actualMixed n beta) n beta
    (fun y hy i j => mixed_readback n beta y hy i j)

theorem actual_magnetic_smooth (n : ℝ) (beta : Fin 3→ℝ) : RectSmooth (actualMagnetic n beta) :=
  original_matrix_smooth magneticEntries magnetic_supported (actualMagnetic n beta) n beta
    (fun y hy i j => magnetic_readback n beta y hy i j)


theorem zeroShift_time (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta) : TimeBox n 0 :=
  ⟨time.lower,time.upper,fun i => by
    have h := N_positive
    simp only [Pi.zero_apply,abs_zero]
    positivity⟩

theorem original_shift_zero (n : ℝ) (hn : n≠0) (x : Phase)
    (physical : x∈originalPhysicalPhase) (j : Fin 3) :
    originalScalarMetric n 0 (fullCoordinates.symm x.1) 0 j.succ=0 := by
  rw [←shift_readback n 0 hn x physical j]
  fin_cases j <;> norm_num [shiftEntries,cValue,cNumerator,cTimeValue,timeMonomial,timeCoordinate,
    Fin.prod_univ_succ]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num

theorem scalarSchur_metric_zero (n : ℝ) (beta : Fin 3→ℝ) (hn : n≠0) (x : Phase)
    (physical : x∈originalPhysicalPhase) (i j : Fin 3) :
    actualScalarSchur n beta (fullCoordinates.symm x.1) i j=actualMetric n 0 x i j := by
  rw [actualScalarSchur_generated n beta hn ⟨fullCoordinates.symm x.1,physical⟩,
    ←actualScalarSchur_generated n 0 hn ⟨fullCoordinates.symm x.1,physical⟩]
  simp only [actualScalarSchur,original_shift_zero n hn x physical j,mul_zero,zero_div,sub_zero]
  rfl

end LowEnergy.PreparationVacuumLowerClassical
