import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoefficientFormula
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTimeCorrectionLeaves

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerClassical
open SaturationMonoid.PhysicsCore
open PreparationVacuumCoefficientBudget PreparationVacuumPrimitiveMatrix PreparationVacuumPrincipalBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumCentralBudget PreparationVacuumEngineBudget
open PreparationVacuumClockSymbol PreparationVacuumEngineSmooth PreparationVacuumMoyalBudget
open PreparationScalarCoordinates PreparationCoordinates PreparationChartGuard PreparationVacuumSourceChartBudget
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open SU7MotherLieAlgebra StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorYukawaMassSpectrum
open StageNineExteriorMotherLieRepresentation SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal
open CanonicalPreparationCutoff
open scoped BigOperators RealInnerProductSpace ContDiff Matrix

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol
abbrev Word := PreparationVacuumCanonicalMoyal.Word
abbrev Slot := PreparationVacuumCanonicalMoyal.Slot

def originalBasisChange : Matrix (Fin 12) (Fin 12) ℚ :=
  ![Pi.single 9 1,Pi.single 10 1,Pi.single 0 1,Pi.single 1 1,
    Pi.single 2 1,Pi.single 3 1,Pi.single 4 1-Pi.single 11 (1/2),
    Pi.single 4 1+Pi.single 11 (1/2),Pi.single 5 1,Pi.single 6 1,
    Pi.single 7 1,Pi.single 8 1]

theorem originalBasisChange_read : ∀ r i : Fin 12,
    (∑ b,originalBasisChange r b*rawGenerator b i)=(Pi.single r 1 : Fin 12→ℚ) i := by
  decide +kernel

def originalUnit (r : Fin 12) : NativeLie := rawCoordinates.symm (Pi.single r 1)

theorem originalUnit_generated (r : Fin 12) :
    originalUnit r=∑ b : Fin 12,(originalBasisChange r b : ℝ) • nativeGenerator b := by
  apply rawCoordinates.injective
  ext i
  simp only [originalUnit,LinearEquiv.apply_symm_apply,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [nativeGenerator_raw]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (originalBasisChange_read r i)
  push_cast at h
  rw [h]
  by_cases eq : i=r <;> simp [eq]

def originalRho (r : Fin 12) (i j : Fin 70) : ℚ :=
  ∑ b,if originalBasisChange r b=0 then 0 else originalBasisChange r b*rationalRho b i j

def originalAd (r : Fin 12) (i j : Fin 12) : ℚ :=
  ∑ b,if originalBasisChange r b=0 then 0 else originalBasisChange r b*rationalAd b i j

theorem originalRho_source (r : Fin 12) (i j : Fin 70) :
    (originalRho r i j : ℝ)=scalarRealify (action (scalarUnit j) (originalUnit r)) i := by
  rw [originalUnit_generated]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  unfold originalRho
  simp only [show ∀ (c d : ℚ), (if c=0 then 0 else c*d)=c*d from fun c d => by split_ifs with h <;> simp_all]
  push_cast
  simp_rw [rationalRho_source]
  rfl

theorem originalAd_source (r i j : Fin 12) :
    (originalAd r i j : ℝ)=rawCoordinates
      (StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket (originalUnit r) (originalUnit j)) i := by
  rw [originalUnit_generated r]
  change _=rawCoordinates (StageNineP286BracketCalculus.coordinateBracketBilinear
    (∑ b : Fin 12,(originalBasisChange r b : ℝ) • nativeGenerator b) (originalUnit j)) i
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,LinearMap.sum_apply,LinearMap.smul_apply]
  unfold originalAd
  simp only [show ∀ (c d : ℚ), (if c=0 then 0 else c*d)=c*d from fun c d => by split_ifs with h <;> simp_all]
  push_cast
  simp_rw [rationalAd_source]
  rfl

def vacuumColumn : Fin 70→ℚ := Pi.single 1 1+Pi.single 3 1+Pi.single 7 1+Pi.single 9 1

theorem vacuum_lex (i : Fin 35) :
    vacuum (lexIndex i)=(if i=1 then 1 else 0)+(if i=3 then 1 else 0)+
      (if i=7 then 1 else 0)+(if i=9 then 1 else 0) := by
  unfold vacuum sourceGeneratedVacuumCoordinates
  rw [StageNineDynamicBreakingVacuum.positive_sourceGeneratedVacuumBase]
  simp only [finiteGenerationJointBreakingScalar,map_sum,finiteGenerationBreakingTensor]
  change (∑ a : Fin 2,∑ b : Fin 2,
    (scalarCoordinateEquiv ((su7ExteriorBasis 4) (finiteGenerationScalarIndex a b))) (lexIndex i))=_
  have basis (k : ScalarBasisIndex) :
      (scalarCoordinateEquiv ((su7ExteriorBasis 4) k)) (lexIndex i)=if k=lexIndex i then 1 else 0 := by
    change (su7ExteriorBasis 4).repr ((su7ExteriorBasis 4) k) (lexIndex i)=_
    exact Module.Basis.repr_self_apply _ _ _
  simp_rw [basis]
  have i00 : finiteGenerationScalarIndex 0 0=lexIndex 3 := by decide +kernel
  have i01 : finiteGenerationScalarIndex 0 1=lexIndex 1 := by decide +kernel
  have i10 : finiteGenerationScalarIndex 1 0=lexIndex 9 := by decide +kernel
  have i11 : finiteGenerationScalarIndex 1 1=lexIndex 7 := by decide +kernel
  simp only [Fin.sum_univ_two,i00,i01,i10,i11,lex_bijective.injective.eq_iff]
  simp only [eq_comm]
  ring

theorem vacuumColumn_source (i : Fin 70) : (vacuumColumn i : ℝ)=scalarRealify vacuum i := by
  induction i using Fin.addCases (m:=35) (n:=35) with
  | left i =>
    change _=scalarRead vacuum (realSlot i)
    rw [scalar_read_real,vacuum_lex]
    fin_cases i <;> norm_num [vacuumColumn,Pi.single_apply,Fin.ext_iff,realSlot]
  | right i =>
    change _=scalarRead vacuum (imagSlot i)
    rw [scalar_read_imag,vacuum_lex]
    fin_cases i <;> norm_num [vacuumColumn,Pi.single_apply,Fin.ext_iff,imagSlot]

theorem original_vacuum_norm : scalarL1 vacuum=4 := by
  unfold scalarL1
  simp_rw [←vacuumColumn_source]
  have h : (∑ i : Fin 70,|vacuumColumn i|)=4 := by decide +kernel
  exact_mod_cast h


def originalRhoFast : Fin 12→Fin 70→Fin 70→ℚ :=
  ![rationalRho 9,rationalRho 10,rationalRho 0,rationalRho 1,rationalRho 2,rationalRho 3,
    (fun i j => rationalRho 4 i j-(1/2)*rationalRho 11 i j),
    (fun i j => rationalRho 4 i j+(1/2)*rationalRho 11 i j),
    rationalRho 5,rationalRho 6,rationalRho 7,rationalRho 8]

theorem originalBasisChange_sum (f : Fin 12→ℚ) (r : Fin 12) :
    (∑ b,originalBasisChange r b*f b)=
      (![f 9,f 10,f 0,f 1,f 2,f 3,f 4-(1/2)*f 11,f 4+(1/2)*f 11,f 5,f 6,f 7,f 8] : Fin 12→ℚ) r := by
  fin_cases r <;> simp [originalBasisChange,Pi.single_apply,sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib]

theorem originalRho_fast (r : Fin 12) (i j : Fin 70) : originalRho r i j=originalRhoFast r i j := by
  unfold originalRho
  simp only [show ∀ (c d : ℚ), (if c=0 then 0 else c*d)=c*d from fun c d => by split_ifs with h <;> simp_all]
  have h := originalBasisChange_sum (fun b => rationalRho b i j) r
  fin_cases r <;> exact h

/-- The original raw12 basis has unit row and column norms on the realified exterior scalar. -/
theorem originalRho_norm : ∀ (r : Fin 12) (j : Fin 70),
    (∑ i,|originalRho r i j|) ≤ 1 ∧ (∑ i,|originalRho r j i|) ≤ 1 := by
  intro r j
  simp_rw [originalRho_fast]
  fin_cases r <;> fin_cases j <;> decide +kernel

theorem originalBracket_absolute_sum : (∑ r : Fin 12,∑ j : Fin 12,∑ i : Fin 12,|originalAd r i j|)=84 := by
  decide +kernel



theorem raw_original_expansion (a : NativeLie) : a=∑ r : Fin 12,rawCoordinates a r • originalUnit r := by
  apply rawCoordinates.injective
  simp only [map_sum,map_smul,originalUnit,LinearEquiv.apply_symm_apply]
  ext k
  simp [Pi.single_apply]

theorem original_bracket_expansion (a b : NativeLie) (i : Fin 12) :
    rawCoordinates (StageNineP286BracketCalculus.coordinateBracketBilinear a b) i=
      ∑ r : Fin 12,∑ j : Fin 12,(originalAd r i j : ℝ)*rawCoordinates a r*rawCoordinates b j := by
  conv_lhs => rw [raw_original_expansion a,raw_original_expansion b]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro j hj
  have source : (originalAd r i j : ℝ)=rawCoordinates
      (StageNineP286BracketCalculus.coordinateBracketBilinear (originalUnit r) (originalUnit j)) i :=
    originalAd_source r i j
  calc
    _ = rawCoordinates a r*rawCoordinates b j*
        rawCoordinates (StageNineP286BracketCalculus.coordinateBracketBilinear (originalUnit r) (originalUnit j)) i := by ring
    _ = rawCoordinates a r*rawCoordinates b j*(originalAd r i j : ℝ) :=
      congrArg (fun t : ℝ => rawCoordinates a r*rawCoordinates b j*t) source.symm
    _ = _ := by ring


end LowEnergy.PreparationVacuumLowerClassical
