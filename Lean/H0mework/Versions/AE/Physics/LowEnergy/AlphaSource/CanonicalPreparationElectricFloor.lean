import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrincipalFloor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhaseBounds
open SaturationMonoid.PhysicsCore
open StageNineP286GaugeAuxiliaryVariation StageNineGlobalIntegratedAction StageNineHyperchargeAuxiliaryVariation
open PreparationActualFactor PreparationScalarCoordinates PreparationPhaseScalar
open PreparationPhaseGuard PreparationCoordinates PreparationChartGuard
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumScalarChart SourceQuantumNativeDimensions
open GaussNativeEnergy GaussHistoryHilbert GaussNativeForm
open scoped BigOperators Matrix RealInnerProductSpace

theorem actual_sourceSigma_half : sourceSigma=(1/2 : ℝ) :=
  Stage9C.Material.SpinPair.sourceCoupling_eq

theorem original_slot0_native (i : Fin 3) :
    gaugeCoordinates gaugeSlot0.val i=
      if i=0 then rawCoordinates.symm (Pi.single (1 : Fin 12) 1) else 0 := by
  change rawCoordinates.symm
    (fun j => insertFree (Pi.single (0 : Fin 33) 1) (combinedRow i j))=_
  fin_cases i <;> apply rawCoordinates.injective <;> ext j <;> fin_cases j <;>
    norm_num [insertFree,combinedRow,Pi.single_apply,Fin.ext_iff]

theorem original_slot0_native_norm :
    ‖rawCoordinates.symm (Pi.single (1 : Fin 12) 1)‖^2=(2 : ℝ) := by
  rw [←real_inner_self_eq_norm_sq]
  change p286CoordinateLiePairing
    (rawCoordinates.symm (Pi.single (1 : Fin 12) 1))
    (rawCoordinates.symm (Pi.single (1 : Fin 12) 1))=2
  rw [actual_raw_block_decode]
  unfold p286CoordinateLiePairing
  simp only [LinearEquiv.symm_apply_apply]
  norm_num [p286LiePairing,specialUnitaryLiePairing_self_eq_sum_normSq,
    hyperchargeLiePairing_eq_coordinate_mul,actualRawBlock,Pi.single_apply,Fin.ext_iff,
    Fin.sum_univ_succ]

theorem original_slot0_coefficient_square :
    (∑ a : LieIndex, (lieBasis.repr (gaugeCoordinates gaugeSlot0.val 0) a)^2)=2 := by
  rw [←EuclideanSpace.real_norm_sq_eq,LinearIsometryEquiv.norm_map,
    original_slot0_native]
  simp only [ite_true]
  exact original_slot0_native_norm

theorem original_slot0_electric_read (z : physicalChart) (p : Cotangent) :
    ambientMomentum z.val p (0,gaugeSlot0.val)=
      ∑ a : LieIndex, lieBasis.repr (gaugeCoordinates gaugeSlot0.val 0) a*
        electricMomentum z.val p 0 a := by
  rw [original_gauge_decomposition,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul]
  change (∑ i : Fin 3, ∑ a : LieIndex,
    lieBasis.repr (gaugeCoordinates gaugeSlot0.val i) a*electricMomentum z.val p i a)=_
  simp [Fin.sum_univ_three,original_slot0_native]

theorem actual_angular_slot0_lower (u : FlatConfiguration)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius) : 1/3<u 67 := by
  have center : (7/20 : ℝ)<sourceUnitMomentum 67 := by
    rw [sourceUnitMomentum,if_neg (by decide),if_pos (by decide)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤3563),Real.sqrt_nonneg (3563 : ℝ)]
  have lower:=(abs_le.mp (ubox 67)).1
  linarith [radius_small.2]

theorem actual_slot0_electric_square (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius) :
    (u 67)^2≤2*∑ a : LieIndex,
      electricMomentum (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 0 a^2 := by
  let native:=phaseChart z zbox
  let p:=nativeCovector (WithLp.toLp 2 u)
  have read:=original_slot0_electric_read native p
  rw [original_gauge_slot0_momentum native u] at read
  have cauchy:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a : LieIndex => lieBasis.repr (gaugeCoordinates gaugeSlot0.val 0) a)
    (fun a : LieIndex => electricMomentum native.val p 0 a)
  rw [original_slot0_coefficient_square,←read] at cauchy
  exact cauchy

theorem actual_triad_entry_bound (z : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius) (i j : Fin 3) :
    |triad (fullCoordinates.symm z).1 i j|≤2 := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact coframe_box_abs z zbox _
    | norm_num [triad]

theorem original_electric_recover (z : physicalChart) (p : Cotangent)
    (i : Fin 3) (a : LieIndex) :
    electricMomentum z.val p i a=
      ∑ k : Fin 3, triad z.val.1 k i*rotatedElectric z.val p a k := by
  have original : (triad z.val.1).transpose *ᵥ
      ((triadInverse z.val.1).transpose *ᵥ (fun j => electricMomentum z.val p j a))=
      fun j => electricMomentum z.val p j a := by
    rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,triad_inverse_left z,
      Matrix.transpose_one,Matrix.one_mulVec]
  exact (congrFun original i).symm

theorem actual_electric_square_bound (z : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius) (p : Cotangent) (a : LieIndex) :
    electricMomentum (fullCoordinates.symm z) p 0 a^2≤
      12*∑ k : Fin 3, rotatedElectric (fullCoordinates.symm z) p a k^2 := by
  let native:=phaseChart z zbox
  have coefficient : (∑ k : Fin 3, triad native.val.1 k 0^2)≤12 := by
    have terms : ∀ k : Fin 3, triad native.val.1 k 0^2≤4 := by
      intro k
      have b:=actual_triad_entry_bound z zbox k 0
      change |triad native.val.1 k 0|≤2 at b
      have sq:=mul_self_le_mul_self (abs_nonneg _) b
      nlinarith [sq_abs (triad native.val.1 k 0)]
    have sum:=Finset.sum_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin 3))) => terms k)
    norm_num at sum
    exact sum
  have cauchy:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k : Fin 3 => triad native.val.1 k 0)
    (fun k : Fin 3 => rotatedElectric native.val p a k)
  rw [←original_electric_recover native p 0 a] at cauchy
  exact cauchy.trans (mul_le_mul_of_nonneg_right coefficient
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem actual_electric_norm_lower (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius) :
    1/216 < ∑ a : LieIndex, ∑ k : Fin 3,
      rotatedElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) a k^2 := by
  have slot:=actual_slot0_electric_square z u zbox
  have source:=actual_angular_slot0_lower u ubox
  have original:=Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset LieIndex)) =>
    actual_electric_square_bound z zbox (nativeCovector (WithLp.toLp 2 u)) a)
  rw [←Finset.mul_sum] at original
  nlinarith

theorem actual_closed_phase_T_sigma_floor (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius) :
    sourceSigma/300 < T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) := by
  have volume:=actual_volume_bounds z zbox
  have field:=actual_electric_norm_lower z u zbox ubox
  have positive : 0<GaussNativeEnergy.volume (fullCoordinates.symm z) := by linarith [volume.1]
  have product:=mul_lt_mul_of_pos_left field positive
  have margin : (1/300 : ℝ)<GaussNativeEnergy.volume (fullCoordinates.symm z)*
      ∑ a : LieIndex, ∑ k : Fin 3,
        rotatedElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) a k^2 := by
    nlinarith [volume.1]
  have source:=mul_lt_mul_of_pos_left margin sourceSigma_positive
  rw [T_original_squares]
  simpa only [div_eq_mul_inv,one_mul,mul_assoc] using source

theorem actual_closed_phase_T_floor (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius) :
    1/600 < T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) := by
  have source:=actual_closed_phase_T_sigma_floor z u zbox ubox
  rw [actual_sourceSigma_half] at source
  norm_num at source
  exact source

end LowEnergy.PreparationPhaseBounds
