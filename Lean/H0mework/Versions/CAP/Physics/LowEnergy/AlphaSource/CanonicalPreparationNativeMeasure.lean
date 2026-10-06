import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationRawGram

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationMeasure
open MeasureTheory MeasureTheory.Measure
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open PreparationCoordinates PreparationScalarCoordinates CanonicalPreparationCutoff
open scoped ENNReal RealInnerProductSpace

local instance originalScalarRealInner : InnerProductSpace ℝ Scalar :=
  inferInstanceAs (InnerProductSpace ℝ
    (EuclideanSpace ℂ SaturationMonoid.PhysicsCore.StageNineDynamicBreakingVacuum.ScalarBasisIndex))

private theorem map_volume_inverse {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (decode : E ≃L[ℝ] F) :
    (volume : Measure F).map decode.symm=
      ENNReal.ofReal decode.toLinearMap.normDet • (volume : Measure E) := by
  ext s hs
  rw [Measure.map_apply decode.symm.continuous.measurable hs,Measure.smul_apply]
  have preimage : decode.symm ⁻¹' s=decode '' s := by
    ext y
    constructor
    · intro h; exact ⟨decode.symm y,h,decode.apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩; simpa using hx
  rw [preimage]
  have dimension := decode.toLinearEquiv.finrank_eq
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V:=F),← dimension]
  exact decode.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s

def euclideanDecode {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (read : E ≃L[ℝ] (Fin n → ℝ)) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] E :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv.trans read.symm

theorem coordinate_volume_from_original_Gram {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (read : E ≃L[ℝ] (Fin n → ℝ)) :
    (volume : Measure E).map read =
      ENNReal.ofReal (Real.sqrt
        (Matrix.gram ℝ (fun i : Fin n => read.symm (Pi.single i 1))).det) •
        (volume : Measure (Fin n → ℝ)) := by
  let decode := euclideanDecode read
  have gram : (Matrix.gram ℝ (fun i : Fin n =>
      decode.toLinearMap (EuclideanSpace.basisFun (Fin n) ℝ i))).det=
      (Matrix.gram ℝ (fun i : Fin n => read.symm (Pi.single i 1))).det := by
    congr 1
    ext i j
    simp [decode,euclideanDecode,EuclideanSpace.basisFun_apply,PiLp.ofLp_single]
  have square : decode.toLinearMap.normDet^2=
      (Matrix.gram ℝ (fun i : Fin n => read.symm (Pi.single i 1))).det := by
    simpa only [gram,RCLike.ofReal_real_eq_id,id_eq] using
      decode.toLinearMap.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
  have factor : decode.toLinearMap.normDet=Real.sqrt
      (Matrix.gram ℝ (fun i : Fin n => read.symm (Pi.single i 1))).det := by
    rw [← square,Real.sqrt_sq decode.toLinearMap.normDet_nonneg]
  have mapped := map_volume_inverse decode
  have composition : read=(WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv ∘ decode.symm := by
    ext x; simp [decode,euclideanDecode]
  rw [composition,← Measure.map_map (by fun_prop) (by fun_prop),mapped,Measure.map_smul,factor]
  exact congrArg (fun μ => ENNReal.ofReal (Real.sqrt
    (Matrix.gram ℝ (fun i : Fin n => read.symm (Pi.single i 1))).det) • μ)
      (PiLp.volume_preserving_ofLp (Fin n)).map_eq

theorem scalar_coordinate_measure :
    SourceQuantumScalarHilbert.sliceMeasure.map scalarFreeContinuous=
      ENNReal.ofReal (1/16 : ℝ) • (volume : Measure (Fin 61 → ℝ)) := by
  unfold SourceQuantumScalarHilbert.sliceMeasure
  rw [coordinate_volume_from_original_Gram (E:=scalarSlice) (n:=61) scalarFreeContinuous]
  change ENNReal.ofReal (Real.sqrt
    (Matrix.gram ℝ (fun i : Fin 61 => scalarFree.symm (Pi.single i 1))).det) • _ = _
  rw [original_scalar_Gram_det]
  congr 2
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
  norm_num

theorem gauge_coordinate_measure :
    GaussHistoryHilbert.coordinateGaugeMeasure.map gaugeFreeContinuous=
      ENNReal.ofReal (16384*Real.sqrt 3) • (volume : Measure (Fin 33 → ℝ)) := by
  change (volume : Measure coordinateSlice).map gaugeFreeContinuous = _
  rw [coordinate_volume_from_original_Gram]
  change ENNReal.ofReal (Real.sqrt
    (Matrix.gram ℝ (fun i : Fin 33 => gaugeFree.symm (Pi.single i 1))).det) • _ = _
  rw [original_gauge_Gram_det]
  congr 2
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3))).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ)≤3 by norm_num)]

theorem coframe_coordinate_measure :
    coframeMeasure.map coframeCoordinates=(volume : Measure (Fin 6 → ℝ)) :=
  (PiLp.volume_preserving_ofLp (Fin 6)).map_eq

def blockMeasure : Measure CoordinateBlocks :=
  (volume : Measure (Fin 6 → ℝ)).prod
    ((volume : Measure (Fin 61 → ℝ)).prod (volume : Measure (Fin 33 → ℝ)))

def nativeVolumeFactor : ℝ := 1024*Real.sqrt 3

theorem nativeVolumeFactor_pos : 0<nativeVolumeFactor :=
  mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))

theorem block_coordinate_measure :
    GaussHistoryHilbert.configurationMeasure.map blockCoordinates=
      ENNReal.ofReal nativeVolumeFactor • blockMeasure := by
  change (coframeMeasure.prod (SourceQuantumScalarHilbert.sliceMeasure.prod
    GaussHistoryHilbert.coordinateGaugeMeasure)).map
    (Prod.map coframeCoordinates (Prod.map scalarFreeContinuous gaugeFreeContinuous)) = _
  rw [← Measure.map_prod_map _ _ coframeCoordinates.continuous.measurable
    (scalarFreeContinuous.continuous.measurable.prodMap gaugeFreeContinuous.continuous.measurable),
    ← Measure.map_prod_map _ _ scalarFreeContinuous.continuous.measurable
      gaugeFreeContinuous.continuous.measurable,coframe_coordinate_measure,
    scalar_coordinate_measure,gauge_coordinate_measure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.prod_smul_right,Measure.prod_smul_right,smul_smul]
  change (ENNReal.ofReal (1/16 : ℝ)*ENNReal.ofReal (16384*Real.sqrt 3)) • blockMeasure = _
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤1/16)]
  congr 2
  unfold nativeVolumeFactor
  ring

private abbrev RawIndex := Fin 6 ⊕ (Fin 61 ⊕ Fin 33)

private def rawIndex : RawIndex ≃ Fin 100 :=
  (Equiv.sumCongr (Equiv.refl (Fin 6)) finSumFinEquiv).trans finSumFinEquiv

private def rawSplit : (RawIndex → ℝ) ≃ᵐ CoordinateBlocks :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : RawIndex => ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin 6 → ℝ))
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 61 ⊕ Fin 33 => ℝ)))

private def rawFlatten : CoordinateBlocks ≃ᵐ (Fin 100 → ℝ) :=
  rawSplit.symm.trans (MeasurableEquiv.piCongrLeft (fun _ : Fin 100 => ℝ) rawIndex)

private theorem rawFlatten_eq : (rawFlatten : CoordinateBlocks → (Fin 100 → ℝ))=
    flattenCoordinates := by
  ext x i
  obtain ⟨j,rfl⟩ := rawIndex.surjective i
  simp only [rawFlatten,MeasurableEquiv.trans_apply,MeasurableEquiv.piCongrLeft_apply_apply]
  change rawSplit.symm x j=joinCoordinates x (rawIndex j)
  rcases j with a | (b | c)
  · simp [rawIndex,rawSplit,joinCoordinates,finSumFinEquiv,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm,MeasurableEquiv.prodCongr]
  · have bound : 6+b.val<67 := by omega
    simp [rawIndex,rawSplit,joinCoordinates,finSumFinEquiv,bound,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm,MeasurableEquiv.prodCongr]
  · have bound : ¬(6+(61+c.val)<67) := by omega
    simp [rawIndex,rawSplit,joinCoordinates,finSumFinEquiv,bound,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm,MeasurableEquiv.prodCongr]
    apply congrArg x.2.2
    apply Fin.ext
    change c.val=6+(61+c.val)-67
    omega

theorem flatten_coordinate_measure :
    blockMeasure.map flattenCoordinates.toContinuousLinearEquiv=flatMeasure := by
  have preservingSplit : MeasurePreserving rawSplit
      (volume : Measure (RawIndex → ℝ)) blockMeasure :=
    (MeasurePreserving.id (volume : Measure (Fin 6 → ℝ))).prod
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 61 ⊕ Fin 33 => ℝ)) |>.comp
        (volume_measurePreserving_sumPiEquivProdPi (fun _ : RawIndex => ℝ))
  have preservingFlatten : MeasurePreserving rawFlatten blockMeasure flatMeasure :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin 100 => ℝ) rawIndex).comp preservingSplit.symm
  change blockMeasure.map flattenCoordinates=flatMeasure
  simpa only [rawFlatten_eq] using preservingFlatten.map_eq

theorem native_full100_measure :
    GaussHistoryHilbert.configurationMeasure.map fullCoordinates=
      ENNReal.ofReal nativeVolumeFactor • flatMeasure := by
  change GaussHistoryHilbert.configurationMeasure.map
    (flattenCoordinates.toContinuousLinearEquiv ∘ blockCoordinates) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),block_coordinate_measure,
    Measure.map_smul,flatten_coordinate_measure]

theorem nativeFlatMeasure_eq : PreparationScalarCoordinates.nativeFlatMeasure=
    ENNReal.ofReal (1024*Real.sqrt 3) • flatMeasure := native_full100_measure

end LowEnergy.PreparationMeasure
