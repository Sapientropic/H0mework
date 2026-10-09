import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceIndependentMomentumTransport

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumIndependentMomentumReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open QuantizationCheck.Fermion SourceRealScalarFock
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreHilbert GaussFockPair GaussQuantumMultiplier
open GaussDensityCore PreparationVacuumGradedTransport
open PreparationVacuumFieldConstraintResponse CanonicalPreparationCore
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity
open PreparationVacuumSourceFieldFamily PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open FullQuantum.StateGreen PreparationVacuumActualFieldQuantization
open FullQuantum PreparationVacuumGaugeSourceInjection
open CanonicalGradedSpatialSource
open scoped Topology ContDiff BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance (priority := 10000) sourceFieldModeEq : DecidableEq Mode:=
  fun a b=>@LinearOrder.toDecidableEq Mode SourceRealScalarFock.branchOrder a b

def sourceHalfVolumeRatio (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) : ℂ:=
  (Real.sqrt (GaussNativeEnergy.volume z):ℂ)/
    (Real.sqrt (GaussNativeEnergy.volume (fieldCoordinateCurve f r z)):ℂ)

private theorem source_half_succ (N : ℕ) (z : physicalChart) :
    coreHalfDensity (N+1) z.val=coreHalfDensity N z.val*(Real.sqrt (GaussNativeEnergy.volume z.val):ℂ) :=by
  have weights : GaussDensityCore.density (N+1) z.val=GaussDensityCore.density N z.val*GaussNativeEnergy.volume z.val:=by
    unfold GaussDensityCore.density GaussNativeEnergy.volume
    rw [show N+1+2=(N+2)+1 from by omega,pow_succ]
    ring
  simp only [coreHalfDensity,weights,Real.sqrt_mul (density_pos N z).le,Complex.ofReal_mul]

theorem sourceHalfRatio_adjacent (f : Field289) (r : ℝ) (N : ℕ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) :
    halfRatio f (N+1) z.val r=sourceHalfVolumeRatio f r z.val*halfRatio f N z.val r :=by
  unfold halfRatio sourceHalfVolumeRatio
  rw [source_half_succ N z,source_half_succ N ⟨_,moved⟩]
  ring

theorem sourceHalfRatio_nonzero (f : Field289) (r : ℝ) (N : ℕ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) : halfRatio f N z.val r≠0 :=
  div_ne_zero (coreHalfDensity_ne_zero N z) (coreHalfDensity_ne_zero N ⟨_,moved⟩)

theorem sourceHalfVolumeRatio_nonzero (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) : sourceHalfVolumeRatio f r z.val≠0 :=by
  exact div_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (GaussNativeEnergy.volume_pos z)).ne')
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (GaussNativeEnergy.volume_pos ⟨_,moved⟩)).ne')

def sourceHalfDensityEnd (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) : FockEnd:=
  fiberCoordinates.toLinearMap.comp
    ((transportFiber f z r).toLinearMap.comp fiberCoordinates.symm.toLinearMap)

def sourceHalfDensityInverse (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) : FockEnd where
  toFun psi word:=(halfRatio f word.card z r)⁻¹*psi word
  map_add' psi phi:=by ext word;exact mul_add _ _ _
  map_smul' c psi:=by ext word;change _*(c*psi word)=c*(_*psi word);ring

theorem sourceHalfDensityEnd_actual (f : Field289) (r : ℝ) (z : SourceCoordinateSlice)
    (psi : Fock Mode) (word : Occupation) :
    sourceHalfDensityEnd f r z psi word=halfRatio f word.card z r*psi word :=rfl

theorem sourceHalfDensity_two_sided (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) :
    sourceHalfDensityEnd f r z.val*sourceHalfDensityInverse f r z.val=1 ∧
      sourceHalfDensityInverse f r z.val*sourceHalfDensityEnd f r z.val=1 :=by
  constructor <;> apply LinearMap.ext <;> intro psi <;> funext word
  · change halfRatio f word.card z.val r*((halfRatio f word.card z.val r)⁻¹*psi word)=psi word
    rw [←mul_assoc,mul_inv_cancel₀ (sourceHalfRatio_nonzero f r _ z moved),one_mul]
  · change (halfRatio f word.card z.val r)⁻¹*(halfRatio f word.card z.val r*psi word)=psi word
    rw [←mul_assoc,inv_mul_cancel₀ (sourceHalfRatio_nonzero f r _ z moved),one_mul]

def sourceConjugateField (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) (A : FockEnd) : FockEnd:=
  sourceHalfDensityEnd f r z*A*sourceHalfDensityInverse f r z

set_option backward.isDefEq.respectTransparency true in
theorem sourceConjugateField_creation (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (i : Mode) :
    sourceConjugateField f r z.val (Fermion.creation i)=
      sourceHalfVolumeRatio f r z.val • Fermion.creation i :=by
  have intertwine : sourceHalfDensityEnd f r z.val*Fermion.creation i=
      sourceHalfVolumeRatio f r z.val • (Fermion.creation i*sourceHalfDensityEnd f r z.val) :=by
    apply LinearMap.ext
    intro psi
    funext word
    by_cases present : i∈word
    · have cardinal:=Finset.card_erase_add_one present
      change halfRatio f word.card z.val r*create i psi word=
        sourceHalfVolumeRatio f r z.val*create i (sourceHalfDensityEnd f r z.val psi) word
      simp only [create,present,↓reduceIte,sourceHalfDensityEnd_actual]
      rw [←cardinal,sourceHalfRatio_adjacent f r _ z moved]
      ac_rfl
    · change halfRatio f word.card z.val r*create i psi word=
        sourceHalfVolumeRatio f r z.val*create i (sourceHalfDensityEnd f r z.val psi) word
      simp only [create,present,↓reduceIte,mul_zero]
  rw [sourceConjugateField,intertwine,smul_mul_assoc,mul_assoc,
    (sourceHalfDensity_two_sided f r z moved).1,mul_one]

set_option backward.isDefEq.respectTransparency true in
theorem sourceConjugateField_annihilation (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (i : Mode) :
    sourceConjugateField f r z.val (Fermion.annihilation i)=
      (sourceHalfVolumeRatio f r z.val)⁻¹ • Fermion.annihilation i :=by
  have intertwine : sourceHalfDensityEnd f r z.val*Fermion.annihilation i=
      (sourceHalfVolumeRatio f r z.val)⁻¹ • (Fermion.annihilation i*sourceHalfDensityEnd f r z.val) :=by
    apply LinearMap.ext
    intro psi
    funext word
    by_cases present : i∈word
    · change halfRatio f word.card z.val r*annihilate i psi word=
        (sourceHalfVolumeRatio f r z.val)⁻¹*annihilate i (sourceHalfDensityEnd f r z.val psi) word
      simp only [annihilate,present,↓reduceIte,mul_zero]
    · change halfRatio f word.card z.val r*annihilate i psi word=
        (sourceHalfVolumeRatio f r z.val)⁻¹*annihilate i (sourceHalfDensityEnd f r z.val psi) word
      simp only [annihilate,present,↓reduceIte,sourceHalfDensityEnd_actual]
      have cardinal : (insert i word).card=word.card+1:=Finset.card_insert_of_notMem present
      rw [cardinal,sourceHalfRatio_adjacent f r _ z moved]
      have nonzero:=sourceHalfVolumeRatio_nonzero f r z moved
      field_simp
  rw [sourceConjugateField,intertwine,smul_mul_assoc,mul_assoc,
    (sourceHalfDensity_two_sided f r z moved).1,mul_one]

theorem sourceConjugateField_smul (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) (c : ℂ) (A : FockEnd) :
    sourceConjugateField f r z (c • A)=c • sourceConjugateField f r z A :=by
  simp only [sourceConjugateField,mul_smul_comm,smul_mul_assoc]

theorem sourceConjugateField_originalHalves (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (i : Quantum.Index) :
    sourceConjugateField f r z.val (rawMomentumPlus i)=sourceHalfVolumeRatio f r z.val • rawMomentumPlus i ∧
    sourceConjugateField f r z.val (rawMomentumConjugate i)=sourceHalfVolumeRatio f r z.val • rawMomentumConjugate i ∧
    sourceConjugateField f r z.val (rawPrimalPlus i)=(sourceHalfVolumeRatio f r z.val)⁻¹ • rawPrimalPlus i ∧
    sourceConjugateField f r z.val (rawPrimalConjugate i)=(sourceHalfVolumeRatio f r z.val)⁻¹ • rawPrimalConjugate i :=by
  simp only [rawMomentumPlus,rawMomentumConjugate,rawPrimalPlus,rawPrimalConjugate,
    sourceConjugateField_smul,sourceConjugateField_creation f r z moved,
    sourceConjugateField_annihilation f r z moved,smul_smul]
  constructor
  · congr 1;ring
  constructor
  · congr 1;ring
  constructor <;> congr 1 <;> ring

theorem sourceConjugateField_product (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (A B : FockEnd) :
    sourceConjugateField f r z.val (A*B)=
      sourceConjugateField f r z.val A*sourceConjugateField f r z.val B :=by
  simp only [sourceConjugateField,mul_assoc]
  rw [←mul_assoc (sourceHalfDensityInverse f r z.val) (sourceHalfDensityEnd f r z.val),
    (sourceHalfDensity_two_sided f r z moved).2,one_mul]

theorem sourceConjugateField_quantizedDensity (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (A : Matrix Mode Mode ℂ) :
    sourceConjugateField f r z.val (Fermion.quantize A)=Fermion.quantize A :=by
  have commute : sourceHalfDensityEnd f r z.val*Fermion.quantize A=
      Fermion.quantize A*sourceHalfDensityEnd f r z.val:=by
    apply LinearMap.ext
    intro psi
    have actual:=congrArg (fun T : FockFiber→L[ℂ] FockFiber=>fiberCoordinates (T (fiberCoordinates.symm psi)))
      (GaussQuantumMultiplier.weight_commute (fun N=>halfRatio f N z.val r) A).eq
    exact actual
  rw [sourceConjugateField,commute,mul_assoc,(sourceHalfDensity_two_sided f r z moved).1,mul_one]

theorem sourceConjugateField_independentDensity (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) :
    sourceConjugateField f r z.val
      (rawPairDensity
        (Quantum.operatorMatrix (sourceMovingDensityMother reader p base candidate))
        (Quantum.operatorMatrix (sourceMovingDensityMother reader (-p) base candidate)))=
      Fermion.quantize (transportedRawSymbol reader base candidate p) :=by
  rw [←sourceIndependentDensity_fullCAR,sourceConjugateField_quantizedDensity f r z moved]

end LowEnergy.PreparationVacuumIndependentMomentumReturn
