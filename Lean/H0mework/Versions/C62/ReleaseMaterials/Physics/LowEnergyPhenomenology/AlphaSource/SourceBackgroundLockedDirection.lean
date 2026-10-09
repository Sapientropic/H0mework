import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugeCurrentWard
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginEnergyWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalElectromagneticDirectionReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource Stage9C.Material.SpinPair
open StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift PointwiseLorentzianCoframeJet
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction DiracCliffordRepresentation
open SourceQuantumScalarChart SourceQuantumScalarOrbitDimensions SourceQuantumResidualGaugeSlice
open PreparationVacuumPhysicalElectromagneticDirection PreparationPhysicalNativeOriginPhaseWard
open StageNineCoframeGravityGaugeRegularity YangMills.FullPairing
open scoped BigOperators Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

/-- The complete original scalar stabilizer supplies the color direction; no Cartan subspace is imposed. -/
def sourceBackgroundColor (n : Fin 3→ℝ) : NativeLie := colorCombination n

def sourceBackgroundSpin (n : Fin 3→ℝ) : DiracMatrix :=
  ∑i : Fin 3,(n i/2:ℂ) • spinRotation i

def sourceBackgroundMatterAction (n : Fin 3→ℝ) : Mother :=
  ∑i : Fin 3,(n i:ℂ) • sourceLockedAction i

/-- The phase is a matter/independent-dual action; it is not a new gauge connection or kinetic term. -/
def sourceBackgroundPhaseAction (n : Fin 3→ℝ) (phase : ℝ) : Mother :=
  sourceBackgroundMatterAction n+(Complex.I*(phase:ℂ)) • LinearMap.id

theorem sourceBackgroundColor_scalar (n : Fin 3→ℝ) : orbit (sourceBackgroundColor n)=0 := by
  change orbit (∑i : Fin 3,n i • colorGenerator i)=0
  simp only [map_sum,map_smul,sourceScalar_color_locked,smul_zero,Finset.sum_const_zero]

theorem sourceBackgroundColor_complete (a : NativeLie) (fixed : orbit a=0) :
    sourceBackgroundColor (colorStabilizerEquiv.symm ⟨a,fixed⟩)=a := by
  exact congrArg Subtype.val (colorStabilizerEquiv.apply_symm_apply ⟨a,fixed⟩)

theorem sourceBackgroundMatter_source (n : Fin 3→ℝ) (point : BasePoint) :
    sourceBackgroundMatterAction n (actual.matter point)=0 := by
  rw [actual_matter]
  simp only [sourceBackgroundMatterAction,LinearMap.sum_apply,LinearMap.smul_apply,
    sourceLockedAction_primal,smul_zero,Finset.sum_const_zero]

theorem sourceBackgroundDual_source (n : Fin 3→ℝ) (point : BasePoint) :
    (actual.conjugateMatter point).comp (sourceBackgroundMatterAction n)=0 := by
  apply LinearMap.ext
  intro v
  rw [actual_conjugateMatter]
  simp only [LinearMap.comp_apply,sourceBackgroundMatterAction,LinearMap.sum_apply,
    LinearMap.smul_apply,map_sum,map_smul,sourceLockedAction_independentDual,
    smul_zero,Finset.sum_const_zero,LinearMap.zero_apply]

theorem sourceBackgroundPhase_matter (n : Fin 3→ℝ) (phase : ℝ) (point : BasePoint) :
    sourceBackgroundPhaseAction n phase (actual.matter point)=
      (Complex.I*(phase:ℂ)) • actual.matter point := by
  simp only [sourceBackgroundPhaseAction,LinearMap.add_apply,LinearMap.smul_apply,
    LinearMap.id_apply,sourceBackgroundMatter_source,zero_add]

theorem sourceBackgroundPhase_dual (n : Fin 3→ℝ) (phase : ℝ) (point : BasePoint) :
    -(actual.conjugateMatter point).comp (sourceBackgroundPhaseAction n phase)=
      -(Complex.I*(phase:ℂ)) • actual.conjugateMatter point := by
  apply LinearMap.ext
  intro v
  have zero:=LinearMap.congr_fun (sourceBackgroundDual_source n point) v
  simp only [LinearMap.comp_apply,LinearMap.zero_apply] at zero
  simp only [sourceBackgroundPhaseAction,LinearMap.neg_apply,LinearMap.comp_apply,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,map_add,map_smul,zero,zero_add,neg_smul]

def sourceBackgroundBracket (a b : NativeLie) : NativeLie := jointP286CoordinateLieBracket a b

private theorem bracket_add (a b c : NativeLie) :
    sourceBackgroundBracket (a+b) c=sourceBackgroundBracket a c+sourceBackgroundBracket b c :=
  jointP286CoordinateLieBracket_add_left a b c
private theorem bracket_scale_left (r : ℝ) (a b : NativeLie) :
    sourceBackgroundBracket (r • a) b=r • sourceBackgroundBracket a b :=
  jointP286CoordinateLieBracket_smul_left r a b
private theorem bracket_scale_right (r : ℝ) (a b : NativeLie) :
    sourceBackgroundBracket a (r • b)=r • sourceBackgroundBracket a b :=
  jointP286CoordinateLieBracket_smul_right r b a
private theorem bracket_color (i j : Fin 3) :
    sourceBackgroundBracket (colorGenerator i) (colorGenerator j)=
      (!![0,-colorGenerator 2,colorGenerator 1;
          colorGenerator 2,0,-colorGenerator 0;
          -colorGenerator 1,colorGenerator 0,0] : Matrix (Fin 3) (Fin 3) NativeLie) i j :=
  colorGenerator_bracket i j

def sourceBackgroundIndex (n : Fin 3→ℝ) (j k : Fin 3) : ℝ :=
  ∑i : Fin 3,n i*sourceIndexRotation i j k

private theorem color_index (i j : Fin 3) :
    sourceBackgroundBracket (colorGenerator i) (colorGenerator j)+
      ∑k : Fin 3,sourceIndexRotation i j k • colorGenerator k=0 := by
  unfold sourceBackgroundBracket
  rw [colorGenerator_bracket]
  fin_cases i <;> fin_cases j <;> simp [sourceIndexRotation]

/-- The actual source spatial triad fixes the index compensation; scalar stability alone does not remove this term. -/
theorem sourceBackgroundGauge_source (n : Fin 3→ℝ) (j : Fin 3) :
    sourceBackgroundBracket (sourceBackgroundColor n) (gaugeCoordinates sourceGauge j)+
      ∑k : Fin 3,sourceBackgroundIndex n j k • gaugeCoordinates sourceGauge k=0 := by
  change sourceBackgroundBracket (∑i : Fin 3,n i • colorGenerator i)
    (gaugeCoordinates sourceGauge j)+_=0
  simp only [sourceGauge_apply,Fin.sum_univ_three,bracket_add,bracket_scale_left,
    bracket_scale_right,bracket_color,sourceBackgroundIndex]
  fin_cases j <;> simp [sourceIndexRotation]
  all_goals module

def sourceBackgroundAuxiliary (point : BasePoint) (pair : Fin 6) : NativeLie :=
  p286CoordinateEquiv (actual.gaugeAuxiliary point pair)

/-- The original constitutive auxiliary has the same color triad, with its source coupling and lapse untouched. -/
theorem sourceBackgroundAuxiliary_source (n : Fin 3→ℝ) (point : BasePoint) (j : Fin 3) :
    sourceBackgroundBracket (sourceBackgroundColor n)
      (sourceBackgroundAuxiliary point ⟨j.val,by omega⟩)+
      ∑k : Fin 3,sourceBackgroundIndex n j k •
        sourceBackgroundAuxiliary point ⟨k.val,by omega⟩=0 := by
  have auxiliary (k : Fin 3) : sourceBackgroundAuxiliary point ⟨k.val,by omega⟩=
      (gaugeScale^2/(sourceCoupling*lapse)) • colorGenerator k := by
    unfold sourceBackgroundAuxiliary
    rw [actual_gaugeAuxiliary]
    fin_cases k <;> simp [electricAuxiliary,colorGenerator]
  change sourceBackgroundBracket (∑i : Fin 3,n i • colorGenerator i)
    (sourceBackgroundAuxiliary point ⟨j.val,by omega⟩)+_=0
  simp only [auxiliary,Fin.sum_univ_three,bracket_add,bracket_scale_left,
    bracket_scale_right,bracket_color,sourceBackgroundIndex]
  fin_cases j <;> simp [sourceIndexRotation]
  all_goals module

theorem sourceBackgroundAuxiliary_magnetic (point : BasePoint) (j : Fin 3) :
    sourceBackgroundAuxiliary point (Fin.natAdd 3 j)=0 := by
  unfold sourceBackgroundAuxiliary
  rw [actual_gaugeAuxiliary]
  fin_cases j <;> simp [electricAuxiliary]

open Stage9C.Dynamics.Homogeneous PreparationVacuumLorentzFieldInjection
  PreparationVacuumNativeFieldInjection PreparationVacuumMixedFieldReturn

/-- This is the original primitive Lorentz frame generator, not an added internal gauge field. -/
def sourceBackgroundFrame (n : Fin 3→ℝ) : LorentzianCoframe :=
  ∑i : Fin 3,n i • frameGenerator (sourceSpinSlot i)

private theorem frame_temporal (i : Fin 3) :
    ∀j : Fin 4,frameGenerator (sourceSpinSlot i) 0 j=0 ∧ frameGenerator (sourceSpinSlot i) j 0=0 := by
  intro j
  fin_cases i <;> fin_cases j <;>
    norm_num [frameGenerator,sourceSpinSlot,lorentzGenerator,lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,orientedLorentzBivectorBasisCoefficient,
      lorentzBivectorFirst,lorentzBivectorSecond,pairFirst,pairSecond,minkowskiInternalSign,Fin.sum_univ_six,Pi.single_apply,Fin.ext_iff,
      Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]

/-- Native frame rotation and the actual coordinate rotation cancel on the complete source coframe. -/
theorem sourceBackgroundCoframe_source (n : Fin 3→ℝ) (point : BasePoint) :
    sourceBackgroundFrame n*actual.coframe point-actual.coframe point*sourceBackgroundFrame n=0 := by
  rw [actual_coframe]
  ext a b
  simp only [Matrix.sub_apply,Matrix.zero_apply,homogeneousCoframe,
    Matrix.mul_diagonal,Matrix.diagonal_mul,sourceBackgroundFrame,Matrix.sum_apply,Matrix.smul_apply]
  by_cases ha : a=0
  · subst a
    simp [frame_temporal]
  · by_cases hb : b=0
    · subst b
      simp [frame_temporal]
    · fin_cases a <;> fin_cases b <;> simp_all

end LowEnergy.PreparationPhysicalElectromagneticDirectionReturn
