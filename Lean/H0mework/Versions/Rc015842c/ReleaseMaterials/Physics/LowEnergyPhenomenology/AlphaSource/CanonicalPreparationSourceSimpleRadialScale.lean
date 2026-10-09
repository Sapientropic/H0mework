import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedRadialScale

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticSpatialSource
open PreparationVacuumObservedPoleTensor PreparationVacuumObservedStaticResidue
open PreparationVacuumStaticSimpleCoupling PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalFeedback PreparationVacuumQuantumSlowResidue
open PreparationVacuumQuantumSlowResponse PreparationVacuumPhysicalSlowBlock
open PreparationVacuumPhysicalPinnedVelocity PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalPoleAmputation
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumCausalPoleResponse PreparationVacuumPhysicalPoleSheet
open PreparationVacuumFullSlowFieldResponse PreparationVacuumPhysicalCharacteristic
open CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceEqualProjection sourceRetainerReturn sourcePoleRead
  sourceNativeReaderFirst sourceStaticCurrent sourceCurrentSimple sourceStaticGaugeCurrent
  sourcePoleEulerInitial sourcePoleMaterialPairGap

/-- The real source momentum scales all coordinates of the original Fourier ray. -/
theorem sourceStaticMomentum_radial (n : PhysicalMomentum) (s : ℝ) :
    fixedMomentum (s • n) 0=(s:ℂ) • fixedMomentum n 0 := by
  ext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [fixedMomentum,fullMomentum]
  · simp [fixedMomentum,fullMomentum,PreparationVacuumPhysicalFeedback.physicalSpatial]
    ring

theorem sourceReaderFirst_radial (v : Fin 4→ℂ) (z : ℂ) :
    sourceNativeReaderFirst (z • v)=z • sourceNativeReaderFirst v := by
  simp only [sourceNativeReaderFirst,sourceLinearPart,degreeTensor_scaled,pow_one,
    mul_smul_comm,smul_mul_assoc,smul_sub]

theorem sourceStaticBase_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (i : Fin 289) : sourceStaticBase q (s • n) i=sourceStaticBase q n i := by
  simp only [sourceStaticBase,sourceResonance_radial q.F n s positive]

theorem sourceStaticCurrent_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceStaticCurrent q (s • n) l r=sourceStaticCurrent q n l r := by
  funext i
  rw [sourceStaticCurrent,sourceStaticCurrent,sourceStaticBase_radial q n s positive]

theorem sourceStaticGaugeCurrent_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    sourceStaticGaugeCurrent q (s • n) l r mu a=sourceStaticGaugeCurrent q n l r mu a := by
  simp only [sourceStaticGaugeCurrent,sourceStaticGauge,sourceResonance_radial q.F n s positive]

/-- Both original retainer cross terms have the same reciprocal radial scale. -/
theorem sourceBaseCross_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (i : Fin 289) :
    sourceBaseCross q (s • n) 0 i=(s:ℂ)⁻¹ • sourceBaseCross q n 0 i := by
  simp only [sourceBaseCross,sourceResonance_radial q.F n s positive,sourceOffStatic_radial q.F n s positive,
    smul_mul_assoc,mul_smul_comm,map_smul,smul_neg,smul_sub]

theorem sourceCurrentSimple_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceCurrentSimple q (s • n) l r=(s:ℂ)⁻¹ • sourceCurrentSimple q n l r := by
  ext i
  simp only [sourceCurrentSimple,sourceBaseCross_radial q n s positive,map_smul,Pi.smul_apply,smul_neg]

/-- The full coupling numerator, including its time jet and gauge initial value, is radially constant. -/
theorem sourceNativeSimple_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceNativeSimple q (s • n) l r=sourceNativeSimple q n l r := by
  simp only [sourceNativeSimple,sourceStaticGaugeCurrent_radial q n s positive,
    sourceStaticMomentum_radial,sourceReaderFirst_radial,sourceCurrentSimple_radial q n s positive,
    sourceStaticCurrent_radial q n s positive,Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_smul]

theorem sourceSpatialSquare_radial (n : PhysicalMomentum) (s : ℝ) :
    spatialSquare (s • n)=s^2*spatialSquare n := by
  simp only [spatialSquare,Pi.smul_apply,smul_eq_mul,mul_pow]
  ring

theorem sourceCanonicalStaticDenominator_radial (n : PhysicalMomentum) (s : ℝ) (i : Fin 2) :
    sourceCanonicalDenominator (s • n) 0 i=(s:ℂ)^2*sourceCanonicalDenominator n 0 i := by
  simp only [sourceCanonicalDenominator,sourceSpatialSquare_radial,Complex.ofReal_mul,Complex.ofReal_pow]
  split_ifs <;> ring

/-- The complete actual static coupling scales as inverse momentum squared, without averaging any angular response. -/
theorem sourceSimpleObserved_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    sourceSimpleObserved q (s • n) l r a b pL pR=(s:ℂ)⁻¹^2*sourceSimpleObserved q n l r a b pL pR := by
  simp only [sourceSimpleObserved,sourceCanonicalStaticDenominator_radial,
    sourceNativeSimple_radial q n s positive,mul_inv_rev,inv_pow]
  ring

/-- The source fixes an angular numerator with every material and detector parameter still present. -/
def sourceAngularCoupling (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) : ℂ :=
  (spatialSquare n:ℂ)*sourceSimpleObserved q n l r a b pL pR

theorem sourceAngularCoupling_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    sourceAngularCoupling q (s • n) l r a b pL pR=sourceAngularCoupling q n l r a b pL pR := by
  rw [sourceAngularCoupling,sourceSimpleObserved_radial q n s positive,sourceSpatialSquare_radial]
  simp only [sourceAngularCoupling,Complex.ofReal_mul,Complex.ofReal_pow]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']

end LowEnergy.PreparationVacuumStaticSpatialSource
