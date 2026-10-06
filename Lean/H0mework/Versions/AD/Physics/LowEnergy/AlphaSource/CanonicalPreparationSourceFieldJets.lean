import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFieldEmitter

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceFieldFamily
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open Electromagnetic.CanonicalCoframe
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert
open scoped Matrix Matrix.Norms.L2Operator ContDiff BigOperators
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

abbrev ActionState := LorentzianCoframe × (Fin 4 → SourceMatrix) × SourceMatrix

def sourceState (z : SourceCoordinateSlice) : ActionState :=
  (CanonicalGradedSpatialSource.sourceCoframe z,familyConnection z,familyScalar z)

def fieldDirection (f : Field289) : ActionState :=
  (fieldCoframe f,connectionDirection (sourceField f),scalarDirection (sourceField f))

def stateVolume (s : ActionState) : ℂ := ((|s.1.det|:ℝ):ℂ)
def statePrincipal (mu : Fin 4) (s : ActionState) : SourceMatrix :=
  stateVolume s • coefficientMatrix mu s.1

def stateLower (s : ActionState) : SourceMatrix :=
  (∑ mu : Fin 4,coefficientMatrix mu s.1*s.2.1 mu)+s.2.2

def stateDensityLower (s : ActionState) : SourceMatrix := stateVolume s • stateLower s

def stateHamiltonian (s : ActionState) (i : Fin 4) : SourceMatrix :=
  Fin.cases (timeSymbol (CoframeResponse.principalMatrix s.1) (stateLower s))
    (fun j=>Ring.inverse (CoframeResponse.principalMatrix s.1)*coefficientMatrix j.succ s.1) i

def principalVariation (f : Field289) (mu : Fin 4) (s : ActionState) : SourceMatrix :=
  fderiv ℝ (statePrincipal mu) s (fieldDirection f)
def lowerVariation (f : Field289) (s : ActionState) : SourceMatrix :=
  fderiv ℝ stateDensityLower s (fieldDirection f)

def densityVariation (f : Field289) (s : ActionState) (i : Fin 4) : SourceMatrix :=
  Fin.cases (lowerVariation f s) (fun j=>Complex.I • principalVariation f j.succ s) i-
    Complex.I • (principalVariation f 0 s*stateHamiltonian s i)

-- Holding the base time jet differentiates exactly the source density.
def heldDensityCoefficient (base candidate : ActionState) (i : Fin 4) : SourceMatrix :=
  Fin.cases (stateDensityLower candidate) (fun j=>Complex.I • statePrincipal j.succ candidate) i-
    Complex.I • (statePrincipal 0 candidate*stateHamiltonian base i)

theorem stateVolume_smooth (s : ActionState) (nondegenerate : s.1.det≠0) :
    ContDiffAt ℝ ∞ stateVolume s :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp s
    ((StageNineCoframeVariation.coframe_volume_contDiffAt s.1 nondegenerate).comp s contDiffAt_fst)

theorem statePrincipal_smooth (mu : Fin 4) (s : ActionState) (nondegenerate : s.1.det≠0) :
    ContDiffAt ℝ ∞ (statePrincipal mu) s :=
  (stateVolume_smooth s nondegenerate).smul
    ((coefficientMatrix_smooth mu s.1 nondegenerate).comp s contDiffAt_fst)

theorem stateLower_smooth (s : ActionState) (nondegenerate : s.1.det≠0) :
    ContDiffAt ℝ ∞ stateLower s := by
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro mu _
    exact ((coefficientMatrix_smooth mu s.1 nondegenerate).comp s contDiffAt_fst).mul (by fun_prop)
  · fun_prop

theorem stateDensityLower_smooth (s : ActionState) (nondegenerate : s.1.det≠0) :
    ContDiffAt ℝ ∞ stateDensityLower s :=
  (stateVolume_smooth s nondegenerate).smul (stateLower_smooth s nondegenerate)

theorem principalVariation_smooth (f : Field289) (mu : Fin 4) (s : ActionState)
    (nondegenerate : s.1.det≠0) : ContDiffAt ℝ ∞ (principalVariation f mu) s :=
  ((statePrincipal_smooth mu s nondegenerate).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

theorem lowerVariation_smooth (f : Field289) (s : ActionState)
    (nondegenerate : s.1.det≠0) : ContDiffAt ℝ ∞ (lowerVariation f) s :=
  ((stateDensityLower_smooth s nondegenerate).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

private theorem state_path_derivative (s d : ActionState) :
    HasDerivAt (fun t : ℝ=>s+t • d) d 0 := by
  convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add s using 1
  simp

theorem principalVariation_generated (f : Field289) (mu : Fin 4) (s : ActionState)
    (nondegenerate : s.1.det≠0) :
    HasDerivAt (fun t : ℝ=>statePrincipal mu (s+t • fieldDirection f))
      (principalVariation f mu s) 0 := by
  exact ((statePrincipal_smooth mu s nondegenerate).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (state_path_derivative s (fieldDirection f)) (by simp)

theorem lowerVariation_generated (f : Field289) (s : ActionState) (nondegenerate : s.1.det≠0) :
    HasDerivAt (fun t : ℝ=>stateDensityLower (s+t • fieldDirection f)) (lowerVariation f s) 0 := by
  exact ((stateDensityLower_smooth s nondegenerate).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (state_path_derivative s (fieldDirection f)) (by simp)

theorem densityVariation_generated (f : Field289) (s : ActionState) (nondegenerate : s.1.det≠0)
    (i : Fin 4) :
    HasDerivAt (fun t : ℝ=>heldDensityCoefficient s (s+t • fieldDirection f) i) (densityVariation f s i) 0 := by
  have lower : HasDerivAt
      (fun t : ℝ=>Fin.cases (motive:=fun _ : Fin 4=>SourceMatrix)
        (stateDensityLower (s+t • fieldDirection f))
        (fun j=>Complex.I • statePrincipal j.succ (s+t • fieldDirection f)) i)
      (Fin.cases (motive:=fun _ : Fin 4=>SourceMatrix) (lowerVariation f s)
        (fun j=>Complex.I • principalVariation f j.succ s) i) 0 := by
    refine Fin.cases (lowerVariation_generated f s nondegenerate) (fun j=>?_) i
    exact (principalVariation_generated f j.succ s nondegenerate).const_smul Complex.I
  exact lower.sub (((principalVariation_generated f 0 s nondegenerate).mul_const (stateHamiltonian s i)).const_smul Complex.I)


theorem stateHamiltonian_smooth (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w=>stateHamiltonian w i) s := by
  have unit:=principalMatrix_regular s.1 regular
  have invSmooth : ContDiffAt ℝ ∞ (Ring.inverse : SourceMatrix→SourceMatrix) (CoframeResponse.principalMatrix s.1) := by
    simpa only [unit.unit_spec] using contDiffAt_ringInverse ℝ unit.unit
  have inverse := invSmooth.comp s ((principalMatrix_smooth s.1 nondegenerate).comp s contDiffAt_fst)
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (inverse.mul (stateLower_smooth s nondegenerate)).const_smul (-Complex.I)
  · exact inverse.mul ((coefficientMatrix_smooth j.succ s.1 nondegenerate).comp s contDiffAt_fst)

theorem densityVariation_smooth (f : Field289) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w=>densityVariation f w i) s := by
  have first : ContDiffAt ℝ ∞ (fun w=>Fin.cases (motive:=fun _ : Fin 4=>SourceMatrix)
      (lowerVariation f w) (fun j=>Complex.I • principalVariation f j.succ w) i) s := by
    refine Fin.cases (lowerVariation_smooth f s nondegenerate) (fun j=>?_) i
    exact (principalVariation_smooth f j.succ s nondegenerate).const_smul Complex.I
  exact first.sub (((principalVariation_smooth f 0 s nondegenerate).mul
    (stateHamiltonian_smooth s nondegenerate regular i)).const_smul Complex.I)

def heldFirstCoefficient (f : Field289) (base candidate : ActionState) (i : Fin 4) : SourceMatrix :=
  Fin.cases (lowerVariation f candidate) (fun j=>Complex.I • principalVariation f j.succ candidate) i-
    Complex.I • (principalVariation f 0 candidate*stateHamiltonian base i)

def densitySecond (f g : Field289) (s : ActionState) (i : Fin 4) : SourceMatrix :=
  fderiv ℝ (fun w=>heldFirstCoefficient f s w i) s (fieldDirection g)

def shellSecond (f g : Field289) (s : ActionState) (i : Fin 4) : SourceMatrix :=
  -Complex.I • (principalVariation f 0 s*
    fderiv ℝ (fun w=>stateHamiltonian w i) s (fieldDirection g))

theorem heldFirst_smooth (f : Field289) (base s : ActionState) (nondegenerate : s.1.det≠0)
    (i : Fin 4) : ContDiffAt ℝ ∞ (fun w=>heldFirstCoefficient f base w i) s := by
  have first : ContDiffAt ℝ ∞ (fun w=>Fin.cases (motive:=fun _ : Fin 4=>SourceMatrix)
      (lowerVariation f w) (fun j=>Complex.I • principalVariation f j.succ w) i) s := by
    refine Fin.cases (lowerVariation_smooth f s nondegenerate) (fun j=>?_) i
    exact (principalVariation_smooth f j.succ s nondegenerate).const_smul Complex.I
  exact first.sub (((principalVariation_smooth f 0 s nondegenerate).mul contDiffAt_const).const_smul Complex.I)

theorem densitySecond_generated (f g : Field289) (s : ActionState) (nondegenerate : s.1.det≠0)
    (i : Fin 4) : HasDerivAt (fun t : ℝ=>heldFirstCoefficient f s (s+t • fieldDirection g) i)
      (densitySecond f g s i) 0 :=
  ((heldFirst_smooth f s s nondegenerate i).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (state_path_derivative s (fieldDirection g)) (by simp)

def movingShell (f : Field289) (base candidate : ActionState) (i : Fin 4) : SourceMatrix :=
  -Complex.I • (principalVariation f 0 candidate*(stateHamiltonian candidate i-stateHamiltonian base i))

theorem shellSecond_generated (f g : Field289) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (i : Fin 4) :
    HasDerivAt (fun t : ℝ=>movingShell f s (s+t • fieldDirection g) i) (shellSecond f g s i) 0 := by
  have first:=((principalVariation_smooth f 0 s nondegenerate).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (state_path_derivative s (fieldDirection g)) (by simp)
  have second:=((stateHamiltonian_smooth s nondegenerate regular i).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (state_path_derivative s (fieldDirection g)) (by simp)
  have generated:=(first.mul (second.sub_const (stateHamiltonian s i))).const_smul (-Complex.I)
  unfold movingShell shellSecond
  convert! generated using 1
  simp

theorem densityVariation_split (f : Field289) (base candidate : ActionState) (i : Fin 4) :
    densityVariation f candidate i=heldFirstCoefficient f base candidate i+movingShell f base candidate i := by
  unfold densityVariation heldFirstCoefficient movingShell
  simp only [mul_sub,smul_sub,neg_smul]
  abel

theorem actual_mixed_family_generated (f g : Field289) (z : physicalChart) (i : Fin 4) :
    HasDerivAt (fun t : ℝ=>densityVariation f (sourceState z.val+t • fieldDirection g) i)
      (densitySecond f g (sourceState z.val) i+shellSecond f g (sourceState z.val) i) 0 := by
  have generated:=(densitySecond_generated f g (sourceState z.val) (coframe_nondegenerate z) i).add
    (shellSecond_generated f g (sourceState z.val) (coframe_nondegenerate z)
      (CanonicalGradedSpatialSource.temporal_noncharacteristic z) i)
  convert! generated using 1
  funext t
  exact densityVariation_split f _ _ i

def familyDensity (f : Field289) (z : SourceCoordinateSlice) (i : Fin 4) : SourceMatrix :=
  densityVariation f (sourceState z) i

theorem actual_family_density_generated (f : Field289) (z : physicalChart) (i : Fin 4) :
    HasDerivAt (fun t : ℝ=>heldDensityCoefficient (sourceState z.val)
      (sourceState z.val+t • fieldDirection f) i) (familyDensity f z.val i) 0 :=
  densityVariation_generated f _ (coframe_nondegenerate z) i


def statePhase (s : ActionState) : SourceMatrix :=
  (Complex.I*(stateVolume s)⁻¹) • Ring.inverse (CoframeResponse.principalMatrix s.1)

theorem statePhase_smooth (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) : ContDiffAt ℝ ∞ statePhase s := by
  have unit:=principalMatrix_regular s.1 regular
  have invSmooth : ContDiffAt ℝ ∞ (Ring.inverse : SourceMatrix→SourceMatrix) (CoframeResponse.principalMatrix s.1) := by
    simpa only [unit.unit_spec] using contDiffAt_ringInverse ℝ unit.unit
  have inverse := invSmooth.comp s ((principalMatrix_smooth s.1 nondegenerate).comp s contDiffAt_fst)
  have volume : stateVolume s≠0 := by
    unfold stateVolume
    exact_mod_cast (abs_ne_zero.mpr nondegenerate)
  exact (contDiffAt_const.mul ((stateVolume_smooth s nondegenerate).inv volume)).smul inverse

def familyReader (f : Field289) (z : SourceCoordinateSlice) (i : Fin 4) : SourceMatrix :=
  familyPhase z*familyDensity f z i

def phaseVariation (g : Field289) (s : ActionState) : SourceMatrix :=
  fderiv ℝ statePhase s (fieldDirection g)

theorem actual_normalized_family_derivative (f g : Field289) (z : physicalChart) (i : Fin 4) :
    HasDerivAt (fun t : ℝ=>statePhase (sourceState z.val+t • fieldDirection g)*
      densityVariation f (sourceState z.val+t • fieldDirection g) i)
      (phaseVariation g (sourceState z.val)*familyDensity f z.val i+
        familyPhase z.val*(densitySecond f g (sourceState z.val) i+shellSecond f g (sourceState z.val) i)) 0 := by
  have phase:=((statePhase_smooth (sourceState z.val) (coframe_nondegenerate z)
    (CanonicalGradedSpatialSource.temporal_noncharacteristic z)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      (state_path_derivative (sourceState z.val) (fieldDirection g)) (by simp)
  have generated:=phase.mul (actual_mixed_family_generated f g z i)
  convert! generated using 1
  simp only [Function.comp_apply,zero_smul,add_zero]
  rfl

end LowEnergy.PreparationVacuumSourceFieldFamily
