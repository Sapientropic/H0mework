import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoefficientNativeActionArrays
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrincipalMatrixJets
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationMatrixActualMatrices

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCoefficientBudget
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Slot := PreparationVacuumCanonicalMoyal.Slot
abbrev Word := PreparationVacuumCanonicalMoyal.Word
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol
open SaturationMonoid.PhysicsCore
open StageNineCoframeGravityGaugeRegularity
open PreparationVacuumSourceMatrixInverse PreparationVacuumSourceChartBudget PreparationScalarCoordinates
open PreparationCoordinates PreparationChartGuard PreparationPhaseScalar
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open SourceQuantumConfigurationHilbert GaussLiveMomentum GaussHistoryHilbert GaussCoreDifferential
open PreparationVacuumPrincipalBudget PreparationVacuumMatrixBudget PreparationVacuumPrimitiveMatrix
open PreparationVacuumCentralBudget PreparationVacuumEngineBudget PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumReciprocalBudget PreparationVacuumEngineSmooth
open PreparationVacuumClockPole PreparationActualFactor
open CanonicalPreparationCutoff
open scoped BigOperators Matrix RealInnerProductSpace Topology

open GaussLiveMomentum

def gaugeRowEquiv : (Fin 3 × Fin 12) ≃ Fin 36 where
  toFun p:=combinedRow p.1 p.2
  invFun j:=(spatialRow j,nativeRow j)
  left_inv p:=by simp [spatial_combined,native_combined]
  right_inv:=combined_rows

theorem combined_eq_iff (s : Fin 3) (k : Fin 12) (j : Fin 36) :
    combinedRow s k=j ↔ s=spatialRow j ∧ k=nativeRow j := by
  constructor
  · intro h
    exact ⟨by simpa only [spatial_combined] using congrArg spatialRow h,
      by simpa only [native_combined] using congrArg nativeRow h⟩
  · rintro ⟨rfl,rfl⟩
    exact combined_rows j

theorem gauge_unit_coordinate (s : Fin 3) (j : Fin 36) :
    gaugeCoordinates (gaugeRaw.symm (Pi.single j 1)) s=
      if s=spatialRow j then rawCoordinates.symm (Pi.single (nativeRow j) 1) else 0 := by
  apply rawCoordinates.injective
  change rawCoordinates (rawCoordinates.symm (fun k=>(Pi.single j 1 : Fin 36→ℝ) (combinedRow s k)))=_
  rw [LinearEquiv.apply_symm_apply]
  ext k
  by_cases h : s=spatialRow j
  · simp [h,Pi.single_apply,combined_eq_iff]
  · simp [h,Pi.single_apply,combined_eq_iff]

def rationalGauge (b : Fin 12) (i j : Fin 36) : ℚ :=
  if spatialRow i=spatialRow j then rationalAd b (nativeRow i) (nativeRow j) else 0

def nativeGaugeBlock (b : Fin 12) (i j : Fin 36) : ℝ :=
  gaugeRaw (nativeGauge (nativeGenerator b) (gaugeRaw.symm (Pi.single j 1))) i

theorem rationalGauge_source (b : Fin 12) (i j : Fin 36) :
    (rationalGauge b i j : ℝ)=nativeGaugeBlock b i j := by
  change _=rawCoordinates (jointP286CoordinateLieBracket (nativeGenerator b)
    (gaugeCoordinates (gaugeRaw.symm (Pi.single j 1)) (spatialRow i))) (nativeRow i)
  rw [gauge_unit_coordinate]
  by_cases h : spatialRow i=spatialRow j
  · simpa only [rationalGauge,if_pos h,nativeAd] using rationalAd_source b (nativeRow i) (nativeRow j)
  · simp only [rationalGauge,if_neg h,Rat.cast_zero]
    change 0=rawCoordinates (jointP286CoordinateLieBracketBilinear (nativeGenerator b) 0) _
    simp

theorem rationalGauge_bounds (b : Fin 12) (j : Fin 36) :
    (∑ i,|rationalGauge b i j|)≤generatorNorms b := by
  rw [←gaugeRowEquiv.sum_comp]
  simpa [gaugeRowEquiv,Fintype.sum_prod_type,rationalGauge,spatial_combined,native_combined,apply_ite abs,Finset.sum_ite_irrel] using
    rationalAd_bounds b (nativeRow j)

def rationalT (b : Fin 12) (i j : Fin 97) : ℚ :=
  Fin.addCases (m:=61) (n:=36) (motive:=fun _=>ℚ)
    (fun r=>Fin.addCases (m:=61) (n:=36) (motive:=fun _=>ℚ)
      (fun c=>rationalCompressed b r c) (fun _=>0) j)
    (fun r=>Fin.addCases (m:=61) (n:=36) (motive:=fun _=>ℚ)
      (fun _=>0) (fun c=>rationalGauge b r c) j) i

def nativeT (b : Fin 12) (i j : Fin 97) : ℝ :=
  Fin.addCases (m:=61) (n:=36) (motive:=fun _=>ℝ)
    (fun r=>Fin.addCases (m:=61) (n:=36) (motive:=fun _=>ℝ)
      (fun c=>nativeCompressed b r c) (fun _=>0) j)
    (fun r=>Fin.addCases (m:=61) (n:=36) (motive:=fun _=>ℝ)
      (fun _=>0) (fun c=>nativeGaugeBlock b r c) j) i

theorem rationalT_source (b : Fin 12) (i j : Fin 97) :
    (rationalT b i j : ℝ)=nativeT b i j := by
  refine Fin.addCases (m:=61) (n:=36) ?_ ?_ i <;> intro r <;>
    refine Fin.addCases (m:=61) (n:=36) ?_ ?_ j <;> intro c
  all_goals simp only [rationalT,nativeT,Fin.addCases_left,Fin.addCases_right]
  · exact rationalCompressed_source b r c
  · exact Rat.cast_zero
  · exact Rat.cast_zero
  · exact rationalGauge_source b r c

theorem rationalT_bounds (b : Fin 12) (j : Fin 97) :
    (∑ i,|rationalT b i j|)≤generatorNorms b := by
  refine Fin.addCases (m:=61) (n:=36) ?_ ?_ j <;> intro c
  all_goals rw [Fin.sum_univ_add (a:=61) (b:=36)]
  · simpa [rationalT] using rationalCompressed_bounds b c
  · simpa [rationalT] using rationalGauge_bounds b c

theorem nativeT_bounds (b : Fin 12) (j : Fin 97) :
    (∑ i,|nativeT b i j|)≤(generatorNorms b : ℝ) := by
  simp_rw [←rationalT_source]
  exact_mod_cast rationalT_bounds b j

open CanonicalPreparationCutoff PreparationVacuumCoframeBudget

def sourceIndex (i : Fin 97) : Option (Fin 100) :=
  Fin.addCases (m:=61) (n:=36) (motive:=fun _=>Option (Fin 100))
    (fun k=>some ⟨6+k.val,by omega⟩)
    (fun k=> ![none,some 67,some 68,some 69,some 70,some 71,none,some 72,some 73,
      some 74,some 75,some 76,some 77,some 78,some 79,some 80,some 81,some 82,none,
      some 83,some 84,some 85,some 86,some 87,some 88,some 89,some 90,some 91,some 92,
      some 93,some 94,some 95,some 96,some 97,some 98,some 99] k) i

def sourceCoordinate (i : Fin 97) : Phase→L[ℝ] ℝ :=
  match sourceIndex i with
  | none=>0
  | some j=>phaseCoordinate j

theorem sourceCoordinate_scalar (i : Fin 61) (x : Phase) :
    sourceCoordinate (Fin.castAdd 36 i) x=scalarFree (fullCoordinates.symm x.1).2.1 i := by
  simp only [sourceCoordinate,sourceIndex,Fin.addCases_left]
  change phaseCoordinate ⟨6+i.val,by omega⟩ x=
    scalarFree (scalarFree.symm (splitCoordinates x.1).2.1) i
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem sourceCoordinate_gauge (i : Fin 36) (x : Phase) :
    sourceCoordinate (Fin.natAdd 61 i) x=gaugeRaw (fullCoordinates.symm x.1).2.2.val i := by
  change _=gaugeRaw (gaugeRaw.symm (insertFree (splitCoordinates x.1).2.2)) i
  rw [LinearEquiv.apply_symm_apply]
  fin_cases i <;> rfl

theorem sourceCoordinate_box (x : Phase) (box : x.1∈sourceClosedBox) (i : Fin 97) :
    |sourceCoordinate i x|≤15 := by
  unfold sourceCoordinate
  cases h : sourceIndex i with
  | none=>norm_num
  | some j=>exact source_coordinate_j15 x box j

theorem sourceCoordinate_direction (i : Fin 97) (s : Slot) :
    sourceCoordinate i (PreparationVacuumCanonicalMoyal.slotDirection s)=if sourceIndex i=some s.1 ∧ s.2=false then 1 else 0 := by
  change sourceCoordinate i (PreparationVacuumCoframeBudget.slotDirection s)=_
  unfold sourceCoordinate
  cases h : sourceIndex i with
  | none=>simp
  | some j=>
    rcases s with ⟨k,b⟩
    cases b <;> simp [phaseCoordinate_direction,eq_comm]

theorem sourceCoordinate_direction_L1 (s : Slot) :
    (∑ i,|sourceCoordinate i (PreparationVacuumCanonicalMoyal.slotDirection s)|)≤1 := by
  simp_rw [sourceCoordinate_direction]
  have exactBudget : ∀ s : Fin 100 × Bool,
      (∑ i : Fin 97,if sourceIndex i=some s.1 ∧ s.2=false then (1 : ℕ) else 0)≤1 := by
    decide +kernel
  simp only [apply_ite abs,abs_one,abs_zero]
  exact_mod_cast exactBudget s

def linearSourceAction (b : Fin 12) (i : Fin 97) : Phase→L[ℝ] ℝ :=
  ∑ j,(nativeT b i j) • sourceCoordinate j

theorem linearSourceAction_apply (b : Fin 12) (i : Fin 97) (x : Phase) :
    linearSourceAction b i x=∑ j,nativeT b i j*sourceCoordinate j x := by
  simp [linearSourceAction]

theorem linearSourceAction_L1 (b : Fin 12) (x : Phase) :
    (∑ i,|linearSourceAction b i x|)≤(generatorNorms b : ℝ)*∑ j,|sourceCoordinate j x| := by
  simp_rw [linearSourceAction_apply]
  calc
    _≤∑ i,∑ j,|nativeT b i j*sourceCoordinate j x|:=
      Finset.sum_le_sum (fun i _=>Finset.abs_sum_le_sum_abs _ _)
    _=∑ j,(∑ i,|nativeT b i j|)*|sourceCoordinate j x|:=by
      simp_rw [abs_mul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _≤∑ j,(generatorNorms b : ℝ)*|sourceCoordinate j x|:=
      Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (nativeT_bounds b j) (abs_nonneg _))
    _=_:=by rw [Finset.mul_sum]

def originalB (b : Fin 9) (i : Fin 97) : Phase→L[ℝ] ℝ :=linearSourceAction (Fin.castAdd 3 b) i
def originalS (i : Fin 97) (s : Fin 3) : Phase→L[ℝ] ℝ :=linearSourceAction (Fin.natAdd 9 s) i

theorem sourceAction_family_L1 {r : ℕ} (e : Fin r→Fin 12) (x : Phase) :
    (∑ b,∑ i,|linearSourceAction (e b) i x|)≤
      (∑ b,(generatorNorms (e b) : ℝ))*(∑ j,|sourceCoordinate j x|) := by
  exact (Finset.sum_le_sum (fun b _=>linearSourceAction_L1 (e b) x)).trans_eq (by rw [Finset.sum_mul])

theorem originalB_total (x : Phase) :
    (∑ b,∑ i,|originalB b i x|)≤22*∑ j,|sourceCoordinate j x| := by
  have h:=sourceAction_family_L1 (Fin.castAdd 3 : Fin 9→Fin 12) x
  have total : (∑ b : Fin 9,(generatorNorms (Fin.castAdd 3 b) : ℝ))=22 := by
    have q : (∑ b : Fin 9,generatorNorms (Fin.castAdd 3 b))=22 := by decide +kernel
    exact_mod_cast q
  simpa only [total,originalB] using h

theorem originalS_total (x : Phase) :
    (∑ i,∑ s,|originalS i s x|)≤10*∑ j,|sourceCoordinate j x| := by
  have h:=sourceAction_family_L1 (Fin.natAdd 9 : Fin 3→Fin 12) x
  have total : (∑ s : Fin 3,(generatorNorms (Fin.natAdd 9 s) : ℝ))=10 := by
    have q : (∑ s : Fin 3,generatorNorms (Fin.natAdd 9 s))=10 := by decide +kernel
    exact_mod_cast q
  rw [Finset.sum_comm]
  simpa only [total,originalS] using h

def originalBArray : ℕ→ℝ | 0=>32010 | 1=>22 | _=>0
def originalSArray : ℕ→ℝ | 0=>14550 | 1=>10 | _=>0

theorem sourceCoordinate_box_L1 (x : Phase) (box : x.1∈sourceClosedBox) :
    (∑ i,|sourceCoordinate i x|)≤1455 := by
  calc
    _≤∑ _i:Fin 97,(15 : ℝ):=Finset.sum_le_sum (fun i _=>sourceCoordinate_box x box i)
    _=1455:=by norm_num

private theorem canonical_linear_one (f : Phase→L[ℝ] ℝ) (w : Word 1) (x : Phase) :
    PreparationVacuumCanonicalMoyal.jet 1 f w x=f (PreparationVacuumCanonicalMoyal.slotDirection (w 0)) := by
  change PreparationVacuumCoframeBudget.jet 1 f w x=f (PreparationVacuumCoframeBudget.slotDirection (w 0))
  exact linear_jet_one f w x

private theorem canonical_linear_higher (f : Phase→L[ℝ] ℝ) (n : ℕ) (w : Word (n+2)) (x : Phase) :
    PreparationVacuumCanonicalMoyal.jet (n+2) f w x=0 := by
  change PreparationVacuumCoframeBudget.jet (n+2) f w x=0
  exact linear_jet_higher f n w x

theorem actual_B_total_budget (n : ℕ) (w : Word n) (x : Phase) (box : x.1∈sourceClosedBox) :
    (∑ b,∑ i,|PreparationVacuumCanonicalMoyal.jet n (originalB b i) w x|)≤originalBArray n := by
  cases n with
  | zero=>
    simp only [PreparationVacuumCanonicalMoyal.jet,iteratedFDeriv_zero_apply]
    exact (originalB_total x).trans (by have h:=sourceCoordinate_box_L1 x box; norm_num [originalBArray]; linarith)
  | succ n=>
    cases n with
    | zero=>
      have read (b : Fin 9) (i : Fin 97) := canonical_linear_one (originalB b i) w x
      simp_rw [read]
      exact (originalB_total (PreparationVacuumCanonicalMoyal.slotDirection (w 0))).trans (by
        have h:=sourceCoordinate_direction_L1 (w 0); norm_num [originalBArray]; linarith)
    | succ n=>
      have read (b : Fin 9) (i : Fin 97) := canonical_linear_higher (originalB b i) n w x
      simp_rw [read]
      simp [originalBArray]

theorem actual_S_total_budget (n : ℕ) (w : Word n) (x : Phase) (box : x.1∈sourceClosedBox) :
    (∑ i,∑ s,|PreparationVacuumCanonicalMoyal.jet n (originalS i s) w x|)≤originalSArray n := by
  cases n with
  | zero=>
    simp only [PreparationVacuumCanonicalMoyal.jet,iteratedFDeriv_zero_apply]
    exact (originalS_total x).trans (by have h:=sourceCoordinate_box_L1 x box; norm_num [originalSArray]; linarith)
  | succ n=>
    cases n with
    | zero=>
      have read (i : Fin 97) (t : Fin 3) := canonical_linear_one (originalS i t) w x
      simp_rw [read]
      exact (originalS_total (PreparationVacuumCanonicalMoyal.slotDirection (w 0))).trans (by
        have h:=sourceCoordinate_direction_L1 (w 0); norm_num [originalSArray]; linarith)
    | succ n=>
      have read (i : Fin 97) (t : Fin 3) := canonical_linear_higher (originalS i t) n w x
      simp_rw [read]
      simp [originalSArray]

def scalarProjection : Scalar→ₗ[ℝ] (Fin 61→ℝ) where
  toFun v:=read61 (scalarRealify v)
  map_add' v w:=by
    ext i
    fin_cases i <;> simp [read61,map_add] <;> ring
  map_smul' r v:=by
    ext i
    fin_cases i <;> simp [read61,map_smul] <;> ring

def scalarNativeMap (b : Fin 12) : (Fin 61→ℝ)→ₗ[ℝ] (Fin 61→ℝ) :=
  scalarProjection.comp ((StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (nativeGenerator b)).comp
    (scalarSlice.subtype.comp scalarFree.symm.toLinearMap))

def gaugeNativeMap (b : Fin 12) : (Fin 36→ℝ)→ₗ[ℝ] (Fin 36→ℝ) :=
  gaugeRaw.toLinearMap.comp ((nativeGauge (nativeGenerator b)).comp gaugeRaw.symm.toLinearMap)

theorem matrix_of_pi_linear {n m : ℕ} (f : (Fin n→ℝ)→ₗ[ℝ] (Fin m→ℝ)) (x : Fin n→ℝ) (i : Fin m) :
    f x i=∑ j,f (Pi.single j 1) i*x j := by
  have expansion : x=∑ j,x j • (Pi.single j 1 : Fin n→ℝ) := by
    ext k
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs=>rw [expansion]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem linearSourceAction_scalar (b : Fin 12) (i : Fin 61) (x : Phase) :
    linearSourceAction b (Fin.castAdd 36 i) x=
      read61 (scalarRealify (action (fullCoordinates.symm x.1).2.1.val (nativeGenerator b))) i := by
  rw [linearSourceAction_apply,Fin.sum_univ_add (a:=61) (b:=36)]
  simp only [nativeT,Fin.addCases_left,Fin.addCases_right,zero_mul,Finset.sum_const_zero,add_zero]
  simp_rw [sourceCoordinate_scalar]
  have h:=matrix_of_pi_linear (scalarNativeMap b) (scalarFree (fullCoordinates.symm x.1).2.1) i
  simpa only [scalarNativeMap,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
    scalarProjection,nativeCompressed,action,Submodule.subtype_apply,LinearMap.coe_mk,AddHom.coe_mk] using h.symm

theorem linearSourceAction_gauge (b : Fin 12) (i : Fin 36) (x : Phase) :
    linearSourceAction b (Fin.natAdd 61 i) x=
      gaugeRaw (nativeGauge (nativeGenerator b) (fullCoordinates.symm x.1).2.2.val) i := by
  rw [linearSourceAction_apply,Fin.sum_univ_add (a:=61) (b:=36)]
  simp only [nativeT,Fin.addCases_left,Fin.addCases_right,zero_mul,Finset.sum_const_zero,zero_add]
  simp_rw [sourceCoordinate_gauge]
  have h:=matrix_of_pi_linear (gaugeNativeMap b) (gaugeRaw (fullCoordinates.symm x.1).2.2.val) i
  simpa only [gaugeNativeMap,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,nativeGaugeBlock] using h.symm

theorem scalarProjection_orbit (a : NativeLie) : read61 (scalarRealify (orbit a))=0 := by
  rcases hc : nativeCoordinates a with ⟨c,w,h⟩
  have ha : a=nativeCoordinates.symm (c,w,h) := by
    apply nativeCoordinates.injective
    simp only [LinearEquiv.apply_symm_apply,hc]
  rw [ha]
  ext i
  fin_cases i <;>
    simp [read61,scalarRealify,scalarRead,sourceOrbit_all,sourceOrbit35] <;> ring

def rationalScalarProjection (i : Fin 70) (j : Fin 61) : ℚ:=columnEntry (dualColumns j) i

theorem rationalScalarProjection_source (i : Fin 70) (j : Fin 61) :
    (rationalScalarProjection i j : ℝ)=read61 (scalarRealify (scalarUnit i)) j := by
  rw [scalarUnit_read,dualColumns_read,columnValue_unit]
  rfl

theorem rationalScalarProjection_bounds :
    (∀ i,∑ j,|rationalScalarProjection i j|≤4) ∧
    (∀ j,∑ i,|rationalScalarProjection i j|≤4) := by
  decide +kernel

open PreparationVacuumCanonicalMoyal PreparationVacuumPrincipalBudget

theorem orbitPairing_surjective : Function.Surjective orbitPairing := by
  intro v
  let c:=(sourceGram⁻¹).mulVec v
  refine ⟨∑ j,c j • orbit (normalBuild (sourceNormal j)),?_⟩
  have regular : IsUnit sourceGram.det := by rw [sourceGram_det]; norm_num
  have entry (i j : Fin 9) :
      inner ℝ (orbit (normalBuild (sourceNormal i))) (orbit (normalBuild (sourceNormal j)))=sourceGram i j := by
    rw [←sourceGram_actual]
    change _=inner ℝ (orbit (normalBuild (sourceNormal i))) (orbit (sourceBroken j).val)
    rw [sourceBroken_orbit]
  have equation : orbitPairing (∑ j,c j • orbit (normalBuild (sourceNormal j)))=sourceGram.mulVec c := by
    ext i
    simp only [orbitPairing,inner_sum,real_inner_smul_right,Matrix.mulVec,entry]
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  rw [equation]
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ regular,Matrix.one_mulVec]

theorem actual_D9_regular (z : physicalChart) :
    (sourceD9 (vacuum+(z.val.2.1 : Scalar))).det≠0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro v
  obtain ⟨xi,hxi⟩:=orbitPairing_surjective v
  exact ⟨inverseBrokenCoordinates z xi 0,(actual_D9_equation z xi 0).trans hxi⟩

theorem actual_M3_regular (z : physicalChart) : (PreparationVacuumSourceChartBudget.sourceOrbitMinor z.val).det≠0 := by
  rw [PreparationVacuumSourceChartBudget.sourceOrbitMinor_det]
  have a : 0<firstGauge z.val.2.2.val:=z.property.2.2.2.2.1
  have b : 0<secondGauge z.val.2.2.val:=z.property.2.2.2.2.2.1
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ a.ne')) b.ne'

theorem open_D9_inverse_coefficients (z : physicalChart) (xi : Scalar) (eta : Gauge) :
    inverseBrokenCoordinates z xi eta=
      ((sourceD9 (vacuum+(z.val.2.1 : Scalar)))⁻¹).mulVec (orbitPairing xi) := by
  have equation:=actual_D9_equation z xi eta
  rw [←equation,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (actual_D9_regular z)),Matrix.one_mulVec]

theorem open_M3_inverse_coefficients (z : physicalChart) (xi : Scalar) (eta : Gauge) :
    inverseStabilizerCoordinates z xi eta=(PreparationVacuumSourceChartBudget.sourceOrbitMinor z.val)⁻¹.mulVec (gaugeRight z xi eta) := by
  have equation:=actual_M3_equation z xi eta
  rw [←equation,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (actual_M3_regular z)),Matrix.one_mulVec]

theorem open_inverse_broken_matrix (z : FlatConfiguration) (hz : fullCoordinates.symm z∈physicalChart)
    (xi : Scalar) (eta : Gauge) :
    brokenPart (ambientInverseLie (fullCoordinates.symm z) xi eta)=matrixBroken z xi := by
  rw [sourceBroken_expansion (brokenPart (ambientInverseLie (fullCoordinates.symm z) xi eta))]
  change (∑ i : Fin 9,inverseBrokenCoordinates ⟨fullCoordinates.symm z,hz⟩ xi eta i • sourceBroken i)=_
  rw [open_D9_inverse_coefficients]
  rfl

theorem open_inverse_lie_matrix (z : FlatConfiguration) (hz : fullCoordinates.symm z∈physicalChart)
    (xi : Scalar) (eta : Gauge) : ambientInverseLie (fullCoordinates.symm z) xi eta=matrixLie z xi eta := by
  rw [actual_lie_decomposition (ambientInverseLie (fullCoordinates.symm z) xi eta)]
  change (brokenPart (ambientInverseLie (fullCoordinates.symm z) xi eta)).val+
    ∑ j : Fin 3,inverseStabilizerCoordinates ⟨fullCoordinates.symm z,hz⟩ xi eta j •
      (sourceStabilizer j).val=matrixLie z xi eta
  rw [open_M3_inverse_coefficients,open_inverse_broken_matrix z hz xi eta]
  have right : gaugeRight ⟨fullCoordinates.symm z,hz⟩ xi eta=matrixGaugeRight z xi eta := by
    unfold gaugeRight matrixGaugeRight
    change lockedRows (eta-nativeGauge (brokenPart (ambientInverseLie (fullCoordinates.symm z)
      xi eta)).val (fullCoordinates.symm z).2.2.val)=_
    rw [open_inverse_broken_matrix z hz xi eta]
  rw [right]
  rfl

theorem open_inverseL_matrix_formula (z : FlatConfiguration) (hz : fullCoordinates.symm z∈physicalChart)
    (xi : Scalar) (eta : Gauge) :
    ((inverseL (fullCoordinates.symm z) (xi,eta)).1,
      ((inverseL (fullCoordinates.symm z) (xi,eta)).2.1.val,
       (inverseL (fullCoordinates.symm z) (xi,eta)).2.2.val))=
    (matrixLie z xi eta,
      (xi-action (vacuum+((fullCoordinates.symm z).2.1 : Scalar)) (matrixLie z xi eta),
       eta-nativeGauge (matrixLie z xi eta) (fullCoordinates.symm z).2.2.val)) := by
  have lie:=open_inverse_lie_matrix z hz xi eta
  have slices:=actual_inverse_slice_reconstruction ⟨fullCoordinates.symm z,hz⟩ xi eta
  change (ambientInverseScalar (fullCoordinates.symm z) xi eta : Scalar)=
    xi-action (vacuum+((fullCoordinates.symm z).2.1 : Scalar))
      (ambientInverseLie (fullCoordinates.symm z) xi eta) ∧
    (ambientInverseGauge (fullCoordinates.symm z) xi eta : Gauge)=
    eta-nativeGauge (ambientInverseLie (fullCoordinates.symm z) xi eta)
      (fullCoordinates.symm z).2.2.val at slices
  change (ambientInverseLie (fullCoordinates.symm z) xi eta,
    ((ambientInverseScalar (fullCoordinates.symm z) xi eta : Scalar),
     (ambientInverseGauge (fullCoordinates.symm z) xi eta : Gauge)))=_
  rw [slices.1,slices.2,lie]

theorem open_coefficient_matrix_formula (z : FlatConfiguration) (hz : fullCoordinates.symm z∈physicalChart)
    (xi : Scalar) (eta : Gauge) (k : Fin 94) :
    sourceCoefficient z (xi,eta) k=explicitCoefficient z xi eta k := by
  have original:=open_inverseL_matrix_formula z hz xi eta
  have scalar:=congrArg (fun t : NativeLie × Scalar × Gauge=>t.2.1) original
  have gauge:=congrArg (fun t : NativeLie × Scalar × Gauge=>t.2.2) original
  unfold sourceCoefficient direction
  rw [full_blocks,map_zero]
  change joinCoordinates (0,read61 (scalarRealify (inverseL (fullCoordinates.symm z) (xi,eta)).2.1.val),
    (fun j=>gaugeRaw (inverseL (fullCoordinates.symm z) (xi,eta)).2.2.val (freeRow j))) (Fin.natAdd 6 k)=_
  dsimp only at scalar gauge
  rw [scalar,gauge]
  unfold explicitCoefficient joinCoordinates
  simp only [Fin.val_natAdd,Nat.add_sub_cancel_left,show 6+k.val-67=k.val-61 by omega]
  split_ifs <;> first | omega | rfl


def freeIndex (k : Fin 94) : Fin 97 :=
  Fin.addCases (m:=61) (n:=33) (motive:=fun _=>Fin 97)
    (Fin.castAdd 36) (fun j=>Fin.natAdd 61 (freeRow j)) k

def lockedIndex (j : Fin 3) : Fin 97:=Fin.natAdd 61 ((![0,6,18] : Fin 3→Fin 36) j)

def ambientReader : Ambient→ₗ[ℝ] (Fin 94→ℝ) where
  toFun v k:=Fin.addCases (m:=61) (n:=33) (motive:=fun _=>ℝ)
    (fun i=>scalarProjection v.1 i) (fun j=>gaugeRaw v.2 (freeRow j)) k
  map_add' v w:=by
    ext k
    refine Fin.addCases (m:=61) (n:=33) ?_ ?_ k <;> intro i <;> simp [map_add]
  map_smul' r v:=by
    ext k
    refine Fin.addCases (m:=61) (n:=33) ?_ ?_ k <;> intro i <;> simp [map_smul]

@[simp] theorem ambientReader_scalar (v : Ambient) (i : Fin 61) :
    ambientReader v (Fin.castAdd 33 i)=scalarProjection v.1 i := by
  simp only [ambientReader,LinearMap.coe_mk,AddHom.coe_mk,Fin.addCases_left]

@[simp] theorem ambientReader_gauge (v : Ambient) (i : Fin 33) :
    ambientReader v (Fin.natAdd 61 i)=gaugeRaw v.2 (freeRow i) := by
  simp only [ambientReader,LinearMap.coe_mk,AddHom.coe_mk,Fin.addCases_right]

@[simp] theorem freeIndex_scalar (i : Fin 61) : freeIndex (Fin.castAdd 33 i)=Fin.castAdd 36 i := by
  simp only [freeIndex,Fin.addCases_left]

@[simp] theorem freeIndex_gauge (i : Fin 33) : freeIndex (Fin.natAdd 61 i)=Fin.natAdd 61 (freeRow i) := by
  simp only [freeIndex,Fin.addCases_right]

theorem nativeGenerator_broken (b : Fin 9) : nativeGenerator (Fin.castAdd 3 b)=(sourceBroken b).val := by
  fin_cases b <;> rfl

theorem nativeGenerator_stabilizer (s : Fin 3) : nativeGenerator (Fin.natAdd 9 s)=(sourceStabilizer s).val := by
  fin_cases s <;> rfl

theorem lockedRows_raw (v : Gauge) (j : Fin 3) : lockedRows v j=gaugeRaw v (![0,6,18] j) := by
  fin_cases j <;> rfl

def sourceActionFree (a : NativeLie) (x : Phase) : Fin 94→ℝ :=
  ambientReader (action (vacuum+((fullCoordinates.symm x.1).2.1 : Scalar)) a,
    nativeGauge a (fullCoordinates.symm x.1).2.2.val)

theorem sourceActionFree_generator (b : Fin 12) (x : Phase) (k : Fin 94) :
    sourceActionFree (nativeGenerator b) x k=linearSourceAction b (freeIndex k) x := by
  refine Fin.addCases (m:=61) (n:=33) ?_ ?_ k <;> intro i
  all_goals simp only [sourceActionFree,ambientReader_scalar,ambientReader_gauge,freeIndex_scalar,freeIndex_gauge]
  · change read61 (scalarRealify (action (vacuum+((fullCoordinates.symm x.1).2.1 : Scalar))
      (nativeGenerator b))) i=linearSourceAction b (Fin.castAdd 36 i) x
    rw [linearSourceAction_scalar]
    have act : action (vacuum+((fullCoordinates.symm x.1).2.1 : Scalar)) (nativeGenerator b)=
      orbit (nativeGenerator b)+action ((fullCoordinates.symm x.1).2.1 : Scalar) (nativeGenerator b) := by
      exact map_add (StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (nativeGenerator b)) _ _
    rw [act]
    change scalarProjection (orbit (nativeGenerator b)+_) i=scalarProjection _ i
    rw [map_add]
    change read61 (scalarRealify (orbit (nativeGenerator b))) i+_=_
    rw [scalarProjection_orbit]
    simp
  · exact (linearSourceAction_gauge b (freeRow i) x).symm

theorem coefficient_physical_read (z : FlatConfiguration) (hz : fullCoordinates.symm z∈physicalChart)
    (xi : Scalar) (eta : Gauge) (k : Fin 94) :
    sourceCoefficient z (xi,eta) k=ambientReader (xi,eta) k-
      ambientReader (action (vacuum+((fullCoordinates.symm z).2.1 : Scalar)) (ambientInverseLie (fullCoordinates.symm z) xi eta),
        nativeGauge (ambientInverseLie (fullCoordinates.symm z) xi eta) (fullCoordinates.symm z).2.2.val) k := by
  rw [open_coefficient_matrix_formula z hz xi eta k]
  simp only [open_inverse_lie_matrix z hz xi eta]
  let correction : Ambient :=
    (action (vacuum+((fullCoordinates.symm z).2.1 : Scalar)) (matrixLie z xi eta),
      nativeGauge (matrixLie z xi eta) (fullCoordinates.symm z).2.2.val)
  trans ambientReader ((xi,eta)-correction) k
  · refine Fin.addCases (m:=61) (n:=33) ?_ ?_ k <;> intro i
    · simp only [explicitCoefficient,Fin.val_castAdd,dif_pos i.isLt,ambientReader_scalar]
      rfl
    · have outside : ¬61+i.val<61 := by omega
      simp only [explicitCoefficient,Fin.val_natAdd,dif_neg outside,Nat.add_sub_cancel_left,ambientReader_gauge]
      rfl
  · exact congrFun (ambientReader.map_sub (xi,eta) correction) k


def scalarSeed : Matrix (Fin 70) (Fin 94) ℝ := fun i k=>ambientReader (scalarUnit i,0) k
def gaugeSeed : Matrix (Fin 36) (Fin 94) ℝ := fun i k=>ambientReader (0,gaugeRaw.symm (Pi.single i 1)) k
def lockedProjection : Matrix (Fin 3) (Fin 36) ℝ := fun i j=>if j=(![0,6,18] i) then 1 else 0

def freeB : RectSymbol 9 94 := fun x b k=>originalB b (freeIndex k) x
def pivotB : RectSymbol 9 3 := fun x b i=>originalB b (lockedIndex i) x
def freeS : RectSymbol 94 3 := fun x k s=>originalS (freeIndex k) s x

def matrixF : RectSymbol 9 9:=fun x=>(actualD9 x)⁻¹
def matrixU : RectSymbol 3 3:=fun x=>(actualM3 x)⁻¹

def sectionMatrix : RectSymbol 94 3:=fun x=>freeS x*matrixU x
def wMatrix : RectSymbol 9 94:=fun x=>freeB x-pivotB x*(sectionMatrix x)ᵀ

def scalarFormula : RectSymbol 70 94:=fun x=>scalarSeed-sourceO*((matrixF x)ᵀ*wMatrix x)
def gaugeFormula : RectSymbol 36 94:=fun x=>gaugeSeed-lockedProjectionᵀ*(sectionMatrix x)ᵀ

theorem orbitPairing_matrix (xi : Scalar) : orbitPairing xi=sourceOᵀ.mulVec (scalarRealify xi) := by
  ext i
  rw [orbitPairing,scalar_inner_realified]
  rfl

theorem orbitPairing_unit (a : Fin 70) (i : Fin 9) : orbitPairing (scalarUnit a) i=sourceO a i := by
  rw [orbitPairing_matrix,scalarUnit_read]
  simp [Matrix.mulVec,Pi.single_apply]

theorem lockedRows_unit (a : Fin 36) (i : Fin 3) :
    lockedRows (gaugeRaw.symm (Pi.single a 1)) i=lockedProjection i a := by
  rw [lockedRows_raw,LinearEquiv.apply_symm_apply]
  simp [lockedProjection,Pi.single_apply,eq_comm]


theorem rect_neg {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (B : ℝ) (bound : RectBound M B) :
    RectBound (-M) B := by
  simpa only [RectBound,Matrix.neg_apply,abs_neg] using bound

theorem finite_matrix_sub {a b : ℕ} (M L : RectSymbol a b) (ms : RectSmooth M) (ls : RectSmooth L)
    (N : ℕ) (B D : ArrayBound) (x : Phase) (hx : x∈poleDomain)
    (mb : MatrixBound M N B x) (lb : MatrixBound L N D x) :
    MatrixBound (fun y=>M y-L y) N (fun n=>B n+D n) x := by
  intro m hm w
  have read (i : Fin a) (j : Fin b) :
      PreparationVacuumCanonicalMoyal.jet m (fun y=>(M y-L y) i j) w x=PreparationVacuumCanonicalMoyal.jet m (fun y=>M y i j) w x-PreparationVacuumCanonicalMoyal.jet m (fun y=>L y i j) w x := by
    unfold PreparationVacuumCanonicalMoyal.jet
    exact congrArg (fun T=>T (PreparationVacuumCanonicalMoyal.slotDirection∘w)) (iteratedFDeriv_sub_apply
      (((ms i j x hx).contDiffAt (poleDomain_open.mem_nhds hx)).of_le (by exact_mod_cast (ENat.natCast_lt_top m).le))
      (((ls i j x hx).contDiffAt (poleDomain_open.mem_nhds hx)).of_le (by exact_mod_cast (ENat.natCast_lt_top m).le)))
  simp_rw [read]
  simpa only [RectBound,Matrix.add_apply,Matrix.neg_apply,sub_eq_add_neg] using rect_add (mb m hm w) (rect_neg _ _ (lb m hm w))

theorem finite_matrix_constant {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (c : ℝ)
    (bound : RectBound M c) (N : ℕ) (x : Phase) :
    MatrixBound (fun _=>M) N (constantArray c) x := by
  intro m hm w
  cases m with
  | zero=>simpa only [RectBound,PreparationVacuumCanonicalMoyal.jet,iteratedFDeriv_zero_apply,constantArray,if_pos rfl,ite_true] using bound
  | succ m=>
    simp only [PreparationVacuumCanonicalMoyal.jet,iteratedFDeriv_const_of_ne (by omega : m+1≠0)]
    simp [RectBound,constantArray]

theorem productArray_constant_left (c : ℝ) (B : ArrayBound) (n : ℕ) :
    productArray (constantArray c) B n=c*B n := by
  unfold productArray constantArray
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk ne
    simp [ne]
  · simp

theorem sum_embedding_bound {a b : ℕ} (e : Fin a↪Fin b) (f : Fin b→ℝ) (positive : ∀ i,0≤f i) :
    (∑ i,f (e i))≤∑ i,f i := by
  rw [←Finset.sum_image]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>positive i)
  · exact fun i _ j _ h=>e.injective h


def sourceActionMap (x : Phase) : NativeLie→ₗ[ℝ] (Fin 94→ℝ) :=
  ambientReader.comp ((action (vacuum+((fullCoordinates.symm x.1).2.1 : Scalar))).prod
    ((nativeGauge.flip) (fullCoordinates.symm x.1).2.2.val))

theorem coefficient_broken_stabilizer (x : Phase) (hx : fullCoordinates.symm x.1∈physicalChart)
    (xi : Scalar) (eta : Gauge) (k : Fin 94) :
    sourceCoefficient x.1 (xi,eta) k=ambientReader (xi,eta) k-
      ((∑ b : Fin 9,inverseBrokenCoordinates ⟨fullCoordinates.symm x.1,hx⟩ xi eta b*freeB x b k)+
       ∑ s : Fin 3,inverseStabilizerCoordinates ⟨fullCoordinates.symm x.1,hx⟩ xi eta s*freeS x k s) := by
  rw [coefficient_physical_read x.1 hx xi eta k]
  congr 1
  change sourceActionMap x (ambientInverseLie (fullCoordinates.symm x.1) xi eta) k=_
  rw [actual_inverse_lie_reconstruction ⟨fullCoordinates.symm x.1,hx⟩ xi eta,
    map_add,map_sum,map_sum]
  simp only [map_smul,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro b hb
    congr 1
    change sourceActionFree (sourceBroken b).val x k=originalB b (freeIndex k) x
    rw [←nativeGenerator_broken,sourceActionFree_generator]
    rfl
  · apply Finset.sum_congr rfl
    intro t ht
    congr 1
    change sourceActionFree (sourceStabilizer t).val x k=originalS (freeIndex k) t x
    rw [←nativeGenerator_stabilizer,sourceActionFree_generator]
    rfl


def lockedMap : Gauge→ₗ[ℝ] (Fin 3→ℝ) :=
  LinearMap.pi (fun i=>(LinearMap.proj (![0,6,18] i)).comp gaugeRaw.toLinearMap)

theorem lockedMap_read (eta : Gauge) : lockedMap eta=lockedRows eta := by
  ext i
  exact (lockedRows_raw eta i).symm

theorem pivotB_read (x : Phase) (b : Fin 9) (i : Fin 3) :
    pivotB x b i=lockedMap (nativeGauge (sourceBroken b).val (fullCoordinates.symm x.1).2.2.val) i := by
  change linearSourceAction (Fin.castAdd 3 b) (Fin.natAdd 61 ((![0,6,18] : Fin 3→Fin 36) i)) x=_
  rw [linearSourceAction_gauge,nativeGenerator_broken]
  rfl

theorem gaugeRight_vector (x : Phase) (hx : fullCoordinates.symm x.1∈physicalChart)
    (xi : Scalar) (eta : Gauge) :
    gaugeRight ⟨fullCoordinates.symm x.1,hx⟩ xi eta=
      lockedRows eta-(inverseBrokenCoordinates ⟨fullCoordinates.symm x.1,hx⟩ xi eta) ᵥ* pivotB x := by
  unfold gaugeRight
  rw [←lockedMap_read,map_sub,lockedMap_read]
  congr 1
  have expanded:=congrArg Subtype.val (sourceBroken_expansion
    (brokenPart (ambientInverseLie (fullCoordinates.symm x.1) xi eta)))
  simp only [Submodule.coe_sum,Submodule.coe_smul] at expanded
  rw [expanded,map_sum,LinearMap.sum_apply,map_sum]
  ext i
  simp only [map_smul,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.vecMul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←pivotB_read]
  rfl

theorem coefficient_vector_formula (x : Phase) (hx : fullCoordinates.symm x.1∈physicalChart)
    (xi : Scalar) (eta : Gauge) :
    sourceCoefficient x.1 (xi,eta)=ambientReader (xi,eta)-
      (orbitPairing xi) ᵥ* ((matrixF x)ᵀ*wMatrix x)-
      (lockedRows eta) ᵥ* (sectionMatrix x)ᵀ := by
  let beta:=inverseBrokenCoordinates ⟨fullCoordinates.symm x.1,hx⟩ xi eta
  let gamma:=inverseStabilizerCoordinates ⟨fullCoordinates.symm x.1,hx⟩ xi eta
  have direct : sourceCoefficient x.1 (xi,eta)=ambientReader (xi,eta)-
      (beta ᵥ* freeB x+gamma ᵥ* (freeS x)ᵀ) := by
    ext k
    exact coefficient_broken_stabilizer x hx xi eta k
  have bf : beta=(orbitPairing xi) ᵥ* (matrixF x)ᵀ := by
    rw [Matrix.vecMul_transpose]
    exact open_D9_inverse_coefficients ⟨fullCoordinates.symm x.1,hx⟩ xi eta
  have gu : gamma=(lockedRows eta-beta ᵥ* pivotB x) ᵥ* (matrixU x)ᵀ := by
    rw [Matrix.vecMul_transpose]
    exact (open_M3_inverse_coefficients ⟨fullCoordinates.symm x.1,hx⟩ xi eta).trans
      (congrArg ((PreparationVacuumSourceChartBudget.sourceOrbitMinor (fullCoordinates.symm x.1))⁻¹.mulVec) (gaugeRight_vector x hx xi eta))
  rw [direct,gu,Matrix.vecMul_vecMul,←Matrix.transpose_mul,Matrix.sub_vecMul,
    Matrix.vecMul_vecMul]
  change ambientReader (xi,eta)-(beta ᵥ* freeB x+
    ((lockedRows eta) ᵥ* (sectionMatrix x)ᵀ-beta ᵥ* (pivotB x*(sectionMatrix x)ᵀ)))=_
  have wread : beta ᵥ* freeB x-beta ᵥ* (pivotB x*(sectionMatrix x)ᵀ)=beta ᵥ* wMatrix x :=
    (Matrix.vecMul_sub _ _ _).symm
  calc
    _=ambientReader (xi,eta)-(beta ᵥ* freeB x-beta ᵥ* (pivotB x*(sectionMatrix x)ᵀ))-
        (lockedRows eta) ᵥ* (sectionMatrix x)ᵀ:=by abel
    _=ambientReader (xi,eta)-beta ᵥ* wMatrix x-(lockedRows eta) ᵥ* (sectionMatrix x)ᵀ:=by rw [wread]
    _=_:=by rw [bf,Matrix.vecMul_vecMul]

theorem scalarCoefficients_open (x : Phase) (hx : fullCoordinates.symm x.1∈physicalChart) :
    scalarCoefficients x.1=scalarFormula x := by
  ext a k
  have h:=congrFun (coefficient_vector_formula x hx (scalarUnit a) 0) k
  change sourceCoefficient x.1 (scalarUnit a,0) k=scalarFormula x a k
  simpa only [scalarCoefficients,scalarFormula,scalarSeed,Matrix.sub_apply,Matrix.mul_apply,
    Pi.sub_apply,Matrix.vecMul,dotProduct,Matrix.transpose_apply,orbitPairing_unit,lockedRows,map_zero,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero,sub_zero] using h

theorem gaugeCoefficients_open (x : Phase) (hx : fullCoordinates.symm x.1∈physicalChart) :
    gaugeCoefficients x.1=gaugeFormula x := by
  ext a k
  have h:=congrFun (coefficient_vector_formula x hx 0 (gaugeRaw.symm (Pi.single a 1))) k
  simpa only [gaugeCoefficients,gaugeFormula,gaugeSeed,Matrix.sub_apply,Matrix.mul_apply,
    Pi.sub_apply,Matrix.vecMul,dotProduct,Matrix.transpose_apply,orbitPairing,inner_zero_right,lockedRows_unit,
    zero_mul,Finset.sum_const_zero,sub_zero] using h


theorem freeIndex_readback : ∀ k : Fin 94,sourceIndex (freeIndex k)=some (Fin.natAdd 6 k) := by
  decide +kernel

def freeEmbedding : Fin 94↪Fin 97 where
  toFun:=freeIndex
  inj':=by
    intro i j h
    have image:=congrArg sourceIndex h
    rw [freeIndex_readback,freeIndex_readback] at image
    exact Fin.natAdd_injective 94 6 (Option.some.inj image)

def lockedEmbedding : Fin 3↪Fin 97 where
  toFun:=lockedIndex
  inj':=by decide +kernel

theorem rect_of_total {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (B : ℝ)
    (total : (∑ i,∑ j,|M i j|)≤B) : RectBound M B := by
  constructor
  · intro i
    exact (Finset.single_le_sum (fun k _=>Finset.sum_nonneg (fun j _=>abs_nonneg (M k j)))
      (Finset.mem_univ i)).trans total
  · intro j
    rw [Finset.sum_comm] at total
    exact (Finset.single_le_sum (fun k _=>Finset.sum_nonneg (fun i _=>abs_nonneg (M i k)))
      (Finset.mem_univ j)).trans total

theorem rect_pullback {a b c d : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (B : ℝ)
    (e : Fin c↪Fin a) (f : Fin d↪Fin b) (bound : RectBound M B) :
    RectBound (fun i j=>M (e i) (f j)) B := by
  constructor
  · intro i
    exact (sum_embedding_bound f (fun j=>|M (e i) j|) (fun _=>abs_nonneg _)).trans (bound.1 (e i))
  · intro j
    exact (sum_embedding_bound e (fun i=>|M i (f j)|) (fun _=>abs_nonneg _)).trans (bound.2 (f j))

theorem narrowBox_closed (x : Phase) (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) : x.1∈sourceClosedBox := by
  intro i
  have h:=box i
  have positive:=radius_small.1
  linarith

theorem freeB_smooth : RectSmooth freeB := fun b k=>(originalB b (freeIndex k)).contDiff.contDiffOn
theorem pivotB_smooth : RectSmooth pivotB := fun b i=>(originalB b (lockedIndex i)).contDiff.contDiffOn
theorem freeS_smooth : RectSmooth freeS := fun k s=>(originalS (freeIndex k) s).contDiff.contDiffOn

theorem freeB_budget (x : Phase) (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) :
    MatrixBound freeB N PreparationVacuumPrincipalBudget.originalBArray x := by
  intro n hn w
  have total:=actual_B_total_budget n w x (narrowBox_closed x box)
  have bound:=rect_pullback _ _ (Function.Embedding.refl (Fin 9)) freeEmbedding (rect_of_total _ _ total)
  have same : originalBArray n=PreparationVacuumPrincipalBudget.originalBArray n := by cases n with
    | zero=>rfl
    | succ n=>cases n <;> rfl
  rw [same] at bound
  exact bound

theorem pivotB_budget (x : Phase) (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) :
    MatrixBound pivotB N PreparationVacuumPrincipalBudget.originalBArray x := by
  intro n hn w
  have total:=actual_B_total_budget n w x (narrowBox_closed x box)
  have bound:=rect_pullback _ _ (Function.Embedding.refl (Fin 9)) lockedEmbedding (rect_of_total _ _ total)
  have same : originalBArray n=PreparationVacuumPrincipalBudget.originalBArray n := by cases n with
    | zero=>rfl
    | succ n=>cases n <;> rfl
  rw [same] at bound
  exact bound

theorem freeS_budget (x : Phase) (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) :
    MatrixBound freeS N PreparationVacuumPrincipalBudget.originalMArray x := by
  intro n hn w
  have total:=actual_S_total_budget n w x (narrowBox_closed x box)
  have bound:=rect_pullback _ _ freeEmbedding (Function.Embedding.refl (Fin 3)) (rect_of_total _ _ total)
  have same : originalSArray n=PreparationVacuumPrincipalBudget.originalMArray n := by cases n with
    | zero=>rfl
    | succ n=>cases n <;> rfl
  rw [same] at bound
  exact bound


theorem matrixF_smooth : RectSmooth matrixF :=
  inverse_smooth actualD9 (fun i j=>(actualD9_smooth i j).mono (Set.subset_univ _))
    (fun y hy=>actual_D9_regular ⟨fullCoordinates.symm y.1,hy.1.1⟩)

theorem matrixU_smooth : RectSmooth matrixU :=
  inverse_smooth actualM3 (fun i j=>(actualM3_smooth i j).mono (Set.subset_univ _))
    (fun y hy=>actual_M3_regular ⟨fullCoordinates.symm y.1,hy.1.1⟩)

theorem matrixF_budget (x : Phase) (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) :
    MatrixBound matrixF N originalFArray x := by
  intro n hn w
  apply actual_D9_inverse_budget x box PreparationVacuumPrincipalBudget.originalDArray N
    (affineArray_nonnegative _ _ (by norm_num) (by norm_num)) ?_ n hn w
  intro m hm v
  constructor
  · intro i
    have h:=actual_D9_row_budget m v x (narrowBox_closed x box) i
    have array : (PreparationVacuumPrimitiveMatrix.originalDArray m : ℝ)=
        PreparationVacuumPrincipalBudget.originalDArray m := by cases m with
      | zero=>norm_num [PreparationVacuumPrimitiveMatrix.originalDArray,PreparationVacuumPrincipalBudget.originalDArray,affineArray]
      | succ m=>cases m <;> norm_num [PreparationVacuumPrimitiveMatrix.originalDArray,PreparationVacuumPrincipalBudget.originalDArray,affineArray]
    rw [array] at h
    exact h
  · intro j
    have h:=actual_D9_column_budget m v x (narrowBox_closed x box) j
    have array : (PreparationVacuumPrimitiveMatrix.originalDArray m : ℝ)=
        PreparationVacuumPrincipalBudget.originalDArray m := by cases m with
      | zero=>norm_num [PreparationVacuumPrimitiveMatrix.originalDArray,PreparationVacuumPrincipalBudget.originalDArray,affineArray]
      | succ m=>cases m <;> norm_num [PreparationVacuumPrimitiveMatrix.originalDArray,PreparationVacuumPrincipalBudget.originalDArray,affineArray]
    rw [array] at h
    exact h

theorem matrixU_budget (x : Phase) (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) :
    MatrixBound matrixU N originalUArray x := by
  intro n hn w
  apply actual_M3_inverse_budget x box PreparationVacuumPrincipalBudget.originalMArray N
    (affineArray_nonnegative _ _ (by norm_num) (by norm_num)) ?_ n hn w
  intro m hm v
  constructor
  · intro i
    have h:=actual_M3_row_budget m v x (narrowBox_closed x box) i
    have array : (PreparationVacuumPrimitiveMatrix.originalMArray m : ℝ)=
        PreparationVacuumPrincipalBudget.originalMArray m := by cases m with
      | zero=>norm_num [PreparationVacuumPrimitiveMatrix.originalMArray,PreparationVacuumPrincipalBudget.originalMArray,affineArray]
      | succ m=>cases m <;> norm_num [PreparationVacuumPrimitiveMatrix.originalMArray,PreparationVacuumPrincipalBudget.originalMArray,affineArray]
    rw [array] at h
    exact h
  · intro j
    have h:=actual_M3_column_budget m v x (narrowBox_closed x box) j
    have array : (PreparationVacuumPrimitiveMatrix.originalMArray m : ℝ)=
        PreparationVacuumPrincipalBudget.originalMArray m := by cases m with
      | zero=>norm_num [PreparationVacuumPrimitiveMatrix.originalMArray,PreparationVacuumPrincipalBudget.originalMArray,affineArray]
      | succ m=>cases m <;> norm_num [PreparationVacuumPrimitiveMatrix.originalMArray,PreparationVacuumPrincipalBudget.originalMArray,affineArray]
    rw [array] at h
    exact h

theorem matrixBound_open_congr {a b : ℕ} (M L : RectSymbol a b)
    (same : ∀ y∈poleDomain,M y=L y) (N : ℕ) (B : ArrayBound) (x : Phase) (hx : x∈poleDomain)
    (bound : MatrixBound L N B x) : MatrixBound M N B x := by
  intro n hn w
  have equality (i : Fin a) (j : Fin b) : PreparationVacuumCanonicalMoyal.jet n (fun y=>M y i j) w x=PreparationVacuumCanonicalMoyal.jet n (fun y=>L y i j) w x := by
    have germ : (fun y=>M y i j)=ᶠ[𝓝 x](fun y=>L y i j) :=
      Filter.Eventually.mono (poleDomain_open.mem_nhds hx) (fun y hy=>congrFun (congrFun (same y hy) i) j)
    exact congrArg (fun t=>t (PreparationVacuumCanonicalMoyal.slotDirection∘w)) ((germ.iteratedFDeriv ℝ n).eq_of_nhds)
  simp_rw [equality]
  exact bound n hn w


theorem scalarSeed_scalar (i : Fin 70) (j : Fin 61) :
    scalarSeed i (Fin.castAdd 33 j)=(rationalScalarProjection i j : ℝ) := by
  simp only [scalarSeed,ambientReader_scalar]
  exact (rationalScalarProjection_source i j).symm

theorem scalarSeed_gauge (i : Fin 70) (j : Fin 33) : scalarSeed i (Fin.natAdd 61 j)=0 := by
  simp only [scalarSeed,ambientReader_gauge]
  change gaugeRaw 0 (freeRow j)=0
  simp

theorem gaugeSeed_scalar (i : Fin 36) (j : Fin 61) : gaugeSeed i (Fin.castAdd 33 j)=0 := by
  simp only [gaugeSeed,ambientReader_scalar]
  change scalarProjection 0 j=0
  simp

theorem gaugeSeed_gauge (i : Fin 36) (j : Fin 33) :
    gaugeSeed i (Fin.natAdd 61 j)=if i=freeRow j then 1 else 0 := by
  simp only [gaugeSeed,ambientReader_gauge]
  change gaugeRaw (gaugeRaw.symm (Pi.single i 1)) (freeRow j)=_
  rw [LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply,eq_comm]

theorem scalarSeed_bound : RectBound scalarSeed 4 := by
  constructor
  · intro i
    rw [Fin.sum_univ_add (a:=61) (b:=33)]
    simp only [scalarSeed_scalar,scalarSeed_gauge,abs_zero,Finset.sum_const_zero,add_zero]
    exact_mod_cast rationalScalarProjection_bounds.1 i
  · intro j
    refine Fin.addCases (m:=61) (n:=33) ?_ ?_ j <;> intro k
    · simp only [scalarSeed_scalar]
      exact_mod_cast rationalScalarProjection_bounds.2 k
    · simp only [scalarSeed_gauge,abs_zero,Finset.sum_const_zero]
      norm_num

def gaugeFreeEmbedding : Fin 33↪Fin 36 where
  toFun:=freeRow
  inj':=by decide +kernel

def lockedGaugeEmbedding : Fin 3↪Fin 36 where
  toFun i:=![0,6,18] i
  inj':=by decide +kernel

theorem identity_rect_bound (n : ℕ) : RectBound (1 : Matrix (Fin n) (Fin n) ℝ) 1 := by
  simp [RectBound,Matrix.one_apply,apply_ite abs]

theorem gaugeSeed_bound : RectBound gaugeSeed 1 := by
  have pulled:=rect_pullback (1 : Matrix (Fin 36) (Fin 36) ℝ) 1
    (Function.Embedding.refl (Fin 36)) gaugeFreeEmbedding (identity_rect_bound 36)
  constructor
  · intro i
    rw [Fin.sum_univ_add (a:=61) (b:=33)]
    simp only [gaugeSeed_scalar,gaugeSeed_gauge,abs_zero,Finset.sum_const_zero,zero_add]
    exact pulled.1 i
  · intro j
    refine Fin.addCases (m:=61) (n:=33) ?_ ?_ j <;> intro k
    · simp only [gaugeSeed_scalar,abs_zero,Finset.sum_const_zero]
      norm_num
    · simp only [gaugeSeed_gauge]
      exact pulled.2 k

theorem lockedProjection_bound : RectBound lockedProjection 1 := by
  have pulled:=rect_pullback (1 : Matrix (Fin 36) (Fin 36) ℝ) 1
    lockedGaugeEmbedding (Function.Embedding.refl (Fin 36)) (identity_rect_bound 36)
  simpa [RectBound,lockedProjection,lockedGaugeEmbedding,Matrix.one_apply,eq_comm] using pulled

theorem f_nonnegative : ∀ n,0≤originalFArray n :=
  inverseBudget_nonnegative _ _ (by positivity) (affineArray_nonnegative _ _ (by norm_num) (by norm_num))
theorem u_nonnegative : ∀ n,0≤originalUArray n :=
  inverseBudget_nonnegative _ _ (by positivity) (affineArray_nonnegative _ _ (by norm_num) (by norm_num))
theorem section_nonnegative : ∀ n,0≤ sectionArray n :=
  productArray_nonnegative _ _ (affineArray_nonnegative _ _ (by norm_num) (by norm_num)) u_nonnegative
theorem w_nonnegative (n : ℕ) : 0≤wArray n := add_nonneg
  (affineArray_nonnegative _ _ (by norm_num) (by norm_num) n)
  (productArray_nonnegative _ _ (affineArray_nonnegative _ _ (by norm_num) (by norm_num)) section_nonnegative n)

theorem section_smooth : RectSmooth sectionMatrix :=
  matrix_product_smooth freeS matrixU freeS_smooth matrixU_smooth

theorem section_budget (x : Phase) (hx : x∈poleDomain)
    (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) :
    MatrixBound sectionMatrix N sectionArray x :=
  finite_matrix_product freeS matrixU freeS_smooth matrixU_smooth N _ _
    (affineArray_nonnegative _ _ (by norm_num) (by norm_num)) u_nonnegative x hx
    (freeS_budget x box N) (matrixU_budget x box N)

theorem w_smooth : RectSmooth wMatrix := by
  intro i j
  exact (freeB_smooth i j).sub
    (matrix_product_smooth pivotB (fun y=>(sectionMatrix y)ᵀ) pivotB_smooth
      (fun a b=>section_smooth b a) i j)

theorem w_budget (x : Phase) (hx : x∈poleDomain)
    (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) : MatrixBound wMatrix N wArray x := by
  have product:=finite_matrix_product pivotB (fun y=>(sectionMatrix y)ᵀ) pivotB_smooth
    (fun a b=>section_smooth b a) N PreparationVacuumPrincipalBudget.originalBArray sectionArray
    (affineArray_nonnegative _ _ (by norm_num) (by norm_num)) section_nonnegative x hx
    (pivotB_budget x box N) (finite_matrix_transpose sectionMatrix N sectionArray x (section_budget x hx box N))
  exact finite_matrix_sub freeB (fun y=>pivotB y*(sectionMatrix y)ᵀ) freeB_smooth
    (matrix_product_smooth _ _ pivotB_smooth (fun a b=>section_smooth b a)) N _ _ x hx
    (freeB_budget x box N) product


theorem scalarFormula_budget (x : Phase) (hx : x∈poleDomain)
    (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) :
    MatrixBound scalarFormula N scalarFactorArray x := by
  let fw : RectSymbol 9 94:=fun y=>(matrixF y)ᵀ*wMatrix y
  have fws : RectSmooth fw:=matrix_product_smooth _ _ (fun i j=>matrixF_smooth j i) w_smooth
  have fwb : MatrixBound fw N (productArray originalFArray wArray) x:=
    finite_matrix_product (fun y=>(matrixF y)ᵀ) wMatrix (fun i j=>matrixF_smooth j i) w_smooth
      N originalFArray wArray f_nonnegative w_nonnegative x hx
      (finite_matrix_transpose matrixF N originalFArray x (matrixF_budget x box N)) (w_budget x hx box N)
  have oBound : RectBound sourceO 3:=sourceO_bound
  have product:=finite_matrix_product (fun _=>sourceO) fw (fun _ _=>contDiffOn_const) fws N
    (constantArray 3) (productArray originalFArray wArray)
    (constantArray_nonnegative _ (by norm_num)) (productArray_nonnegative _ _ f_nonnegative w_nonnegative)
    x hx (finite_matrix_constant sourceO 3 oBound N x) fwb
  have arrayEq : productArray (constantArray 3) (productArray originalFArray wArray)=
      fun n=>3*productArray originalFArray wArray n := funext (productArray_constant_left 3 _)
  rw [arrayEq] at product
  exact finite_matrix_sub (fun _=>scalarSeed) (fun y=>sourceO*fw y) (fun _ _=>contDiffOn_const)
    (matrix_product_smooth _ _ (fun _ _=>contDiffOn_const) fws) N (constantArray 4)
    (fun n=>3*productArray originalFArray wArray n) x hx
    (finite_matrix_constant scalarSeed 4 scalarSeed_bound N x) product

theorem gaugeFormula_budget (x : Phase) (hx : x∈poleDomain)
    (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) :
    MatrixBound gaugeFormula N gaugeFactorArray x := by
  have product:=finite_matrix_product (fun _=>lockedProjectionᵀ) (fun y=>(sectionMatrix y)ᵀ)
    (fun _ _=>contDiffOn_const) (fun i j=>section_smooth j i) N (constantArray 1) sectionArray
    (constantArray_nonnegative _ (by norm_num)) section_nonnegative x hx
    (finite_matrix_constant lockedProjectionᵀ 1 (rect_transpose lockedProjection_bound) N x)
    (finite_matrix_transpose sectionMatrix N sectionArray x (section_budget x hx box N))
  have arrayEq : productArray (constantArray 1) sectionArray=sectionArray := by
    funext n
    simpa only [one_mul] using productArray_constant_left 1 sectionArray n
  rw [arrayEq] at product
  exact finite_matrix_sub (fun _=>gaugeSeed) (fun y=>lockedProjectionᵀ*(sectionMatrix y)ᵀ)
    (fun _ _=>contDiffOn_const)
    (matrix_product_smooth _ _ (fun _ _=>contDiffOn_const) (fun i j=>section_smooth j i))
    N (constantArray 1) sectionArray x hx (finite_matrix_constant gaugeSeed 1 gaugeSeed_bound N x) product

/-- Original native coefficient arrays, with all200 coordinate words and no supplied coefficient jets. -/
theorem generatedCoefficientInputs (x : Phase) (hx : x∈poleDomain)
    (box : ∀ i,|x.1 i-flatSource i|≤ sourceRadius) (N : ℕ) : CoefficientInputs x N where
  scalar:=matrixBound_open_congr (fun y=>scalarCoefficients y.1) scalarFormula
    (fun y hy=>scalarCoefficients_open y hy.1.1) N scalarFactorArray x hx
    (scalarFormula_budget x hx box N)
  gauge:=matrixBound_open_congr (fun y=>gaugeCoefficients y.1) gaugeFormula
    (fun y hy=>gaugeCoefficients_open y hy.1.1) N gaugeFactorArray x hx
    (gaugeFormula_budget x hx box N)


end LowEnergy.PreparationVacuumCoefficientBudget
