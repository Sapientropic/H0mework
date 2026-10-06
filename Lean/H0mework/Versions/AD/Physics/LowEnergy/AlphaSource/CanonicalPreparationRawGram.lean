import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarGuard
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationMeasure
open SaturationMonoid.PhysicsCore
open SourceQuantumScalarChart SourceQuantumNativeDimensions
open SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open PreparationCoordinates PreparationScalarCoordinates
open scoped RealInnerProductSpace

private def originalRawBlock (x : Fin 12 → ℝ) : SU7MotherLieAlgebra.P286LieBlockData :=
  (⟨!![(x 6 : ℂ)*Complex.I,x 0+x 1*Complex.I,x 2+x 3*Complex.I;
        -x 0+x 1*Complex.I,(x 7 : ℂ)*Complex.I,x 4+x 5*Complex.I;
        -x 2+x 3*Complex.I,-x 4+x 5*Complex.I,-((x 6+x 7 : ℝ) : ℂ)*Complex.I],by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply] <;> ring
    · simp [Matrix.trace,Fin.sum_univ_succ]; ring⟩,
   ⟨!![(x 10 : ℂ)*Complex.I,x 8+x 9*Complex.I;
        -x 8+x 9*Complex.I,-(x 10 : ℂ)*Complex.I],by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply] <;> ring
    · simp [Matrix.trace,Fin.sum_univ_succ]⟩,
   ⟨(x 11 : ℂ)*Complex.I,by
      change star ((x 11 : ℂ)*Complex.I) = -((x 11 : ℂ)*Complex.I)
      simp⟩)

private theorem original_raw_decode (x : Fin 12 → ℝ) :
    rawCoordinates.symm x=StageNineHolonomicField.p286CoordinateEquiv (originalRawBlock x) := by
  apply rawCoordinates.injective
  rw [rawCoordinates.apply_symm_apply]
  change x=rawRead _
  unfold rawRead
  rw [nativeCoordinates_apply]
  ext i
  fin_cases i <;> simp [originalRawBlock]

theorem original_raw_inner (x y : Fin 12 → ℝ) :
    inner ℝ (rawCoordinates.symm x) (rawCoordinates.symm y) =
      2*(x 0*y 0+x 1*y 1+x 2*y 2+x 3*y 3+x 4*y 4+x 5*y 5+
         x 6*y 6+x 7*y 7+x 8*y 8+x 9*y 9+x 10*y 10)+
        x 6*y 7+x 7*y 6+x 11*y 11 := by
  rw [original_raw_decode,original_raw_decode]
  change StageNineP286GaugeAuxiliaryVariation.p286CoordinateLiePairing _ _ = _
  norm_num [StageNineP286GaugeAuxiliaryVariation.p286CoordinateLiePairing,
    StageNineP286GaugeAuxiliaryVariation.p286LiePairing,
    StageNineGlobalIntegratedAction.specialUnitaryLiePairing,
    StageNineGlobalIntegratedAction.hyperchargeLiePairing,Matrix.trace,Matrix.mul_apply,
    Fin.sum_univ_succ,originalRawBlock]
  ring

def gaugeGramWeight (i : Fin 33) : ℝ := if i=9 ∨ i=20 ∨ i=32 then 1 else 2

def gaugeGram : Matrix (Fin 33) (Fin 33) ℝ :=
  Matrix.diagonal gaugeGramWeight + Matrix.single 27 28 1 + Matrix.single 28 27 1

theorem gauge_original_inner (x y : Fin 33 → ℝ) :
    inner ℝ (gaugeFree.symm x).val (gaugeFree.symm y).val =
      (∑ i : Fin 33, gaugeGramWeight i*x i*y i)+x 27*y 28+x 28*y 27 := by
  change inner ℝ (gaugeBuild (insertFree x)) (gaugeBuild (insertFree y)) = _
  change (∑ i : Fin 3, inner ℝ
    (rawCoordinates.symm (fun j => insertFree x (combinedRow i j)))
    (rawCoordinates.symm (fun j => insertFree y (combinedRow i j)))) = _
  simp_rw [original_raw_inner]
  simp [Fin.sum_univ_succ,insertFree,combinedRow,gaugeGramWeight]
  ring

theorem original_gauge_Gram :
    Matrix.gram ℝ (fun i : Fin 33 => gaugeFree.symm (Pi.single i 1))=gaugeGram := by
  ext i j
  rw [Matrix.gram_apply]
  change inner ℝ (gaugeFree.symm (Pi.single i 1)).val
    (gaugeFree.symm (Pi.single j 1)).val = _
  rw [gauge_original_inner]
  simp [gaugeGram,Matrix.diagonal_apply,Matrix.single,Pi.single_apply]
  by_cases hij : i=j <;> by_cases hi27 : i=27 <;> by_cases hi28 : i=28 <;>
    by_cases hj27 : j=27 <;> by_cases hj28 : j=28 <;> simp_all [eq_comm]

private def triangularGaugeGram : Matrix (Fin 33) (Fin 33) ℝ :=
  gaugeGram.updateRow 28 (gaugeGram 28+(-1/2 : ℝ) • gaugeGram 27)

private theorem triangular_gauge_det : triangularGaugeGram.det=gaugeGram.det := by
  exact Matrix.det_updateRow_add_smul_self gaugeGram (by decide : (28 : Fin 33)≠27) (-1/2)

private theorem triangular_gauge_upper : triangularGaugeGram.IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  simp only [triangularGaugeGram,Matrix.updateRow_apply]
  by_cases hi : i=28
  · subst i
    by_cases hj : j=27
    · subst j; norm_num [gaugeGram,gaugeGramWeight,Matrix.diagonal_apply,Matrix.single,Fin.ext_iff]
    · have j28 : j≠28 := by omega
      simp [gaugeGram,Matrix.single,Ne.symm hj,Ne.symm j28]
  · have hji : i≠j := by omega
    have notpair : ¬(i=27 ∧ j=28) := by omega
    simp [hi,gaugeGram,Matrix.single,hji,eq_comm,notpair]

private theorem triangular_gauge_diagonal (i : Fin 33) :
    triangularGaugeGram i i=if i=28 then 3/2 else gaugeGramWeight i := by
  by_cases hi : i=28
  · subst i; norm_num [triangularGaugeGram,gaugeGram,gaugeGramWeight,
      Matrix.diagonal_apply,Matrix.single,Fin.ext_iff]
  · simp [triangularGaugeGram,hi,gaugeGram,Matrix.single,Ne.symm hi]

theorem gauge_Gram_det : gaugeGram.det=805306368 := by
  rw [← triangular_gauge_det,Matrix.det_of_isUpperTriangular triangular_gauge_upper]
  simp_rw [triangular_gauge_diagonal]
  simp [Fin.prod_univ_succ,gaugeGramWeight]
  norm_num

theorem original_scalar_Gram :
    Matrix.gram ℝ (fun i : Fin 61 => scalarFree.symm (Pi.single i 1))=scalarGram := by
  ext i j
  rw [Matrix.gram_apply]
  change inner ℝ (scalarFree.symm (Pi.single i 1)).val
    (scalarFree.symm (Pi.single j 1)).val = _
  rw [scalar_original_Gram]
  simp [scalarGram,Matrix.diagonal_apply,Pi.single_apply]
  by_cases h : i=j <;> simp_all [eq_comm]

theorem original_scalar_Gram_det :
    (Matrix.gram ℝ (fun i : Fin 61 => scalarFree.symm (Pi.single i 1))).det=1/256 := by
  rw [original_scalar_Gram,scalar_Gram_det]

theorem original_gauge_Gram_det :
    (Matrix.gram ℝ (fun i : Fin 33 => gaugeFree.symm (Pi.single i 1))).det=805306368 := by
  rw [original_gauge_Gram,gauge_Gram_det]

end LowEnergy.PreparationMeasure
