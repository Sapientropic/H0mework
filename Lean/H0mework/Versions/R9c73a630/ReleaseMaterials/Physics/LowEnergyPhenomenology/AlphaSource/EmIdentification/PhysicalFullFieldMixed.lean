import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldCoefficients

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalFullFieldScattering
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldCovector
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField SU7MotherLieAlgebra StageNineLorentzConnectionVariation
open PointwiseDiracSpinConnectionLift DiracCliffordRepresentation DiracExteriorMatterAction
open SU7ExteriorBreakingYukawa StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum SourceQuantumScalarChart SourceQuantumNativeDimensions
open StageNineCoframeScalarMatterRegularity StageNineP286GaugeConnectionVariation
open SU7MotherGaugeTheory
open FullQuantum.StateGreen FullQuantum.Triangular YangMills.FullPairing
open FullQuantum.CoframeResponse FullQuantum.FullSpace
open Electromagnetic.CanonicalCoframe
open scoped Matrix BigOperators Topology InnerProductSpace Matrix.Norms.L2Operator
  ContDiff

local instance mixIndexDecidable : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe :=
  Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FiberOperators := NormedAlgebra.restrictScalars ℝ ℂ _

/-- The second coefficient jet is the original Hessian CLM applied to the force
    direction first: `coefficientSecond reader force = H_mu force reader`.  The
    derivative of the constant reader direction is zero. -/
def coefficientHessian (mu : Fin 4) :
    LorentzianCoframe →L[ℝ] LorentzianCoframe →L[ℝ] SourceMatrix :=
  fderiv ℝ (fderiv ℝ (coefficientMatrix mu)) (Stage9C.Material.SpinPair.actual.coframe 0)

theorem coefficientSecond_hessian (reader force : LorentzianCoframe)
    (mu : Fin 4) :
    coefficientSecond reader force mu = coefficientHessian mu force reader := by
  have smooth := (coefficientMatrix_smooth mu (Stage9C.Material.SpinPair.actual.coframe 0)
    (actual_coframe_nondegenerate 0)).fderiv_right (m := ∞) (by simp)
  unfold coefficientSecond coefficientJetAt coefficientHessian
  rw [fderiv_clm_apply (smooth.differentiableAt (by simp))
    (differentiableAt_const reader)]
  rw [(hasFDerivAt_const reader (Stage9C.Material.SpinPair.actual.coframe 0)).fderiv,
    ContinuousLinearMap.comp_zero, zero_add]
  rfl

/-- The second volume jet is the `|det|` Hessian applied to the force first. -/
def volumeHessian :
    LorentzianCoframe →L[ℝ] LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fun e : LorentzianCoframe => |e.det|)) (Stage9C.Material.SpinPair.actual.coframe 0)

theorem volumeSecond_hessian (reader force : LorentzianCoframe) :
    volumeSecond reader force = volumeHessian force reader := by
  have smooth := (StageNineCoframeVariation.coframe_volume_contDiffAt
    (Stage9C.Material.SpinPair.actual.coframe 0) (actual_coframe_nondegenerate 0)).fderiv_right (m := ∞)
    (by simp)
  unfold volumeSecond volumeJetAt volumeHessian
  rw [fderiv_clm_apply (smooth.differentiableAt (by simp))
    (differentiableAt_const reader)]
  rw [(hasFDerivAt_const reader (Stage9C.Material.SpinPair.actual.coframe 0)).fderiv,
    ContinuousLinearMap.comp_zero, zero_add]
  rfl

theorem coefficientSecond_add_reader (a b force : LorentzianCoframe)
    (mu : Fin 4) :
    coefficientSecond (a+b) force mu =
      coefficientSecond a force mu+coefficientSecond b force mu := by
  simp only [coefficientSecond_hessian, map_add]

theorem coefficientSecond_add_force (reader a b : LorentzianCoframe)
    (mu : Fin 4) :
    coefficientSecond reader (a+b) mu =
      coefficientSecond reader a mu+coefficientSecond reader b mu := by
  simp only [coefficientSecond_hessian, map_add,
    add_apply]

theorem coefficientSecond_smul_reader (r : ℝ) (a force : LorentzianCoframe)
    (mu : Fin 4) :
    coefficientSecond (r • a) force mu = r • coefficientSecond a force mu := by
  simp only [coefficientSecond_hessian, map_smul]

theorem coefficientSecond_smul_force (r : ℝ) (reader a : LorentzianCoframe)
    (mu : Fin 4) :
    coefficientSecond reader (r • a) mu =
      r • coefficientSecond reader a mu := by
  simp only [coefficientSecond_hessian, map_smul,
    smul_apply]

theorem volumeSecond_add_reader (a b force : LorentzianCoframe) :
    volumeSecond (a+b) force = volumeSecond a force+volumeSecond b force := by
  simp only [volumeSecond_hessian, map_add]

theorem volumeSecond_add_force (reader a b : LorentzianCoframe) :
    volumeSecond reader (a+b) = volumeSecond reader a+volumeSecond reader b := by
  simp only [volumeSecond_hessian, map_add, add_apply]

theorem volumeSecond_smul_reader (r : ℝ) (a force : LorentzianCoframe) :
    volumeSecond (r • a) force = r • volumeSecond a force := by
  simp only [volumeSecond_hessian, map_smul]

theorem volumeSecond_smul_force (r : ℝ) (reader a : LorentzianCoframe) :
    volumeSecond reader (r • a) = r • volumeSecond reader a := by
  simp only [volumeSecond_hessian, map_smul,
    smul_apply]

private theorem volumeDirection_add (a b : LorentzianCoframe) :
    volumeDirection 0 (a+b) = volumeDirection 0 a+volumeDirection 0 b := by
  unfold volumeDirection
  exact map_add _ _ _

private theorem volumeDirection_smul (r : ℝ) (a : LorentzianCoframe) :
    volumeDirection 0 (r • a) = r • volumeDirection 0 a := by
  unfold volumeDirection
  exact map_smul _ _ _

private theorem coefficientJet_add (a b : LorentzianCoframe) (mu : Fin 4) :
    coefficientJet (a+b) mu = coefficientJet a mu+coefficientJet b mu := by
  unfold coefficientJet
  exact map_add _ _ _

private theorem coefficientJet_smul (r : ℝ) (a : LorentzianCoframe)
    (mu : Fin 4) :
    coefficientJet (r • a) mu = r • coefficientJet a mu := by
  unfold coefficientJet
  exact map_smul _ _ _

theorem sourceDensityPrincipalJet_add (f g : Field289) (mu : Fin 4) :
    densityPrincipalJet (sourceField (f+g)) mu =
      densityPrincipalJet (sourceField f) mu+densityPrincipalJet (sourceField g) mu := by
  unfold densityPrincipalJet
  rw [sourceField_coframe_add]
  rw [coefficientJet_add, volumeDirection_add]
  simp only [Complex.ofReal_add, add_smul, smul_add]
  module

theorem sourceDensityPrincipalJet_smul (r : ℝ) (f : Field289) (mu : Fin 4) :
    densityPrincipalJet (sourceField (r • f)) mu =
      r • densityPrincipalJet (sourceField f) mu := by
  unfold densityPrincipalJet
  rw [sourceField_coframe_smul]
  rw [coefficientJet_smul, volumeDirection_smul]
  simp only [smul_eq_mul, Complex.ofReal_mul, mul_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

theorem densityPrincipalSecond_add_left (f g h : Field289) (mu : Fin 4) :
    densityPrincipalSecond (sourceField (f+g)) (sourceField h) mu =
      densityPrincipalSecond (sourceField f) (sourceField h) mu+
        densityPrincipalSecond (sourceField g) (sourceField h) mu := by
  unfold densityPrincipalSecond
  rw [sourceField_coframe_add]
  rw [coefficientSecond_add_reader, volumeDirection_add, volumeSecond_add_reader,
    coefficientJet_add]
  simp only [Complex.ofReal_add, add_smul, smul_add]
  module

theorem densityPrincipalSecond_add_right (f g h : Field289) (mu : Fin 4) :
    densityPrincipalSecond (sourceField f) (sourceField (g+h)) mu =
      densityPrincipalSecond (sourceField f) (sourceField g) mu+
        densityPrincipalSecond (sourceField f) (sourceField h) mu := by
  unfold densityPrincipalSecond
  rw [sourceField_coframe_add]
  rw [coefficientSecond_add_force, volumeDirection_add, volumeSecond_add_force,
    coefficientJet_add]
  simp only [Complex.ofReal_add, add_smul, smul_add]
  module

theorem densityPrincipalSecond_smul_left (r : ℝ) (f g : Field289)
    (mu : Fin 4) :
    densityPrincipalSecond (sourceField (r • f)) (sourceField g) mu =
      r • densityPrincipalSecond (sourceField f) (sourceField g) mu := by
  unfold densityPrincipalSecond
  rw [sourceField_coframe_smul]
  rw [coefficientSecond_smul_reader, volumeDirection_smul,
    volumeSecond_smul_reader, coefficientJet_smul]
  simp only [smul_eq_mul, Complex.ofReal_mul, mul_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

theorem densityPrincipalSecond_smul_right (r : ℝ) (f g : Field289)
    (mu : Fin 4) :
    densityPrincipalSecond (sourceField f) (sourceField (r • g)) mu =
      r • densityPrincipalSecond (sourceField f) (sourceField g) mu := by
  unfold densityPrincipalSecond
  rw [sourceField_coframe_smul]
  rw [coefficientSecond_smul_force, volumeDirection_smul,
    volumeSecond_smul_force, coefficientJet_smul]
  simp only [smul_eq_mul, Complex.ofReal_mul, mul_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

/-- The original mixed lower zero block is additive in the reader field. -/
theorem mixedLowerZero_add_left (f g h : Field289) :
    mixedLowerZero (sourceField (f+g)) (sourceField h) =
      mixedLowerZero (sourceField f) (sourceField h)+
        mixedLowerZero (sourceField g) (sourceField h) := by
  unfold mixedLowerZero
  rw [sourceField_coframe_add]
  simp only [densityPrincipalSecond_add_left, sourceDensityPrincipalJet_add,
    sourceField_conn_add, sourceField_scalar_add]
  rw [volumeSecond_add_reader, volumeDirection_add]
  simp only [Complex.ofReal_add, add_smul, smul_add, add_mul, mul_add,
    Finset.sum_add_distrib]
  module

theorem mixedLowerZero_add_right (f g h : Field289) :
    mixedLowerZero (sourceField f) (sourceField (g+h)) =
      mixedLowerZero (sourceField f) (sourceField g)+
        mixedLowerZero (sourceField f) (sourceField h) := by
  unfold mixedLowerZero
  rw [sourceField_coframe_add]
  simp only [densityPrincipalSecond_add_right, sourceDensityPrincipalJet_add,
    sourceField_conn_add, sourceField_scalar_add]
  rw [volumeSecond_add_force, volumeDirection_add]
  simp only [Complex.ofReal_add, add_smul, smul_add, add_mul, mul_add,
    Finset.sum_add_distrib]
  module

theorem mixedLowerZero_smul_left (r : ℝ) (f g : Field289) :
    mixedLowerZero (sourceField (r • f)) (sourceField g) =
      r • mixedLowerZero (sourceField f) (sourceField g) := by
  unfold mixedLowerZero
  rw [sourceField_coframe_smul]
  simp only [densityPrincipalSecond_smul_left, sourceDensityPrincipalJet_smul,
    sourceField_conn_smul, sourceField_scalar_smul]
  rw [volumeSecond_smul_reader, volumeDirection_smul]
  simp only [smul_eq_mul, Complex.ofReal_mul, mul_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_add, smul_smul, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum]
  module

theorem mixedLowerZero_smul_right (r : ℝ) (f g : Field289) :
    mixedLowerZero (sourceField f) (sourceField (r • g)) =
      r • mixedLowerZero (sourceField f) (sourceField g) := by
  unfold mixedLowerZero
  rw [sourceField_coframe_smul]
  simp only [densityPrincipalSecond_smul_right, sourceDensityPrincipalJet_smul,
    sourceField_conn_smul, sourceField_scalar_smul]
  rw [volumeSecond_smul_force, volumeDirection_smul]
  simp only [smul_eq_mul, Complex.ofReal_mul, mul_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_add, smul_smul, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum]
  module

theorem fieldHamiltonianCoefficients_add (f g : Field289) (i : Fin 4) :
    fieldHamiltonianCoefficients (sourceField (f+g)) i =
      fieldHamiltonianCoefficients (sourceField f) i+
        fieldHamiltonianCoefficients (sourceField g) i := by
  unfold fieldHamiltonianCoefficients
  rw [fieldDensityCoefficients_add, mul_add, smul_add]

theorem fieldHamiltonianCoefficients_smul (r : ℝ) (f : Field289) (i : Fin 4) :
    fieldHamiltonianCoefficients (sourceField (r • f)) i =
      r • fieldHamiltonianCoefficients (sourceField f) i := by
  unfold fieldHamiltonianCoefficients
  rw [fieldDensityCoefficients_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ) r
      (fieldDensityCoefficients (sourceField f) i), mul_smul_comm]
  simp only [smul_comm (-Complex.I * sourceVolume⁻¹),
    RCLike.real_smul_eq_coe_smul (K := ℂ)]

theorem shellContactCoefficients_add_left (f g h : Field289) (i : Fin 4) :
    shellContactCoefficients (sourceField (f+g)) (sourceField h) i =
      shellContactCoefficients (sourceField f) (sourceField h) i+
        shellContactCoefficients (sourceField g) (sourceField h) i := by
  unfold shellContactCoefficients
  rw [sourceDensityPrincipalJet_add, add_mul, smul_add]

theorem shellContactCoefficients_add_right (f g h : Field289) (i : Fin 4) :
    shellContactCoefficients (sourceField f) (sourceField (g+h)) i =
      shellContactCoefficients (sourceField f) (sourceField g) i+
        shellContactCoefficients (sourceField f) (sourceField h) i := by
  unfold shellContactCoefficients
  rw [fieldHamiltonianCoefficients_add, mul_add, smul_add]

theorem shellContactCoefficients_smul_left (r : ℝ) (f g : Field289)
    (i : Fin 4) :
    shellContactCoefficients (sourceField (r • f)) (sourceField g) i =
      r • shellContactCoefficients (sourceField f) (sourceField g) i := by
  unfold shellContactCoefficients
  rw [sourceDensityPrincipalJet_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_mul_assoc, smul_smul]
  module

theorem shellContactCoefficients_smul_right (r : ℝ) (f g : Field289)
    (i : Fin 4) :
    shellContactCoefficients (sourceField f) (sourceField (r • g)) i =
      r • shellContactCoefficients (sourceField f) (sourceField g) i := by
  unfold shellContactCoefficients
  rw [fieldHamiltonianCoefficients_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [mul_smul_comm, smul_smul]
  module

theorem mixedDensityCoefficients_add_left (f g h : Field289) (i : Fin 4) :
    mixedDensityCoefficients (sourceField (f+g)) (sourceField h) i =
      mixedDensityCoefficients (sourceField f) (sourceField h) i+
        mixedDensityCoefficients (sourceField g) (sourceField h) i := by
  unfold mixedDensityCoefficients
  rw [mixedLowerZero_add_left f g h]
  simp only [densityPrincipalSecond_add_left]
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cases_zero]
      rw [add_mul]
      module
  | succ j =>
      simp only [Fin.cases_succ]
      rw [add_mul, smul_add]
      module

theorem mixedDensityCoefficients_add_right (f g h : Field289) (i : Fin 4) :
    mixedDensityCoefficients (sourceField f) (sourceField (g+h)) i =
      mixedDensityCoefficients (sourceField f) (sourceField g) i+
        mixedDensityCoefficients (sourceField f) (sourceField h) i := by
  unfold mixedDensityCoefficients
  rw [mixedLowerZero_add_right f g h]
  simp only [densityPrincipalSecond_add_right]
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cases_zero]
      rw [add_mul]
      module
  | succ j =>
      simp only [Fin.cases_succ]
      rw [add_mul, smul_add]
      module

theorem mixedDensityCoefficients_smul_left (r : ℝ) (f g : Field289)
    (i : Fin 4) :
    mixedDensityCoefficients (sourceField (r • f)) (sourceField g) i =
      r • mixedDensityCoefficients (sourceField f) (sourceField g) i := by
  unfold mixedDensityCoefficients
  rw [mixedLowerZero_smul_left r f g]
  simp only [densityPrincipalSecond_smul_left]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cases_zero, smul_mul_assoc, smul_smul, smul_sub]
      module
  | succ j =>
      simp only [Fin.cases_succ, smul_mul_assoc, smul_smul, smul_sub]
      module

theorem mixedDensityCoefficients_smul_right (r : ℝ) (f g : Field289)
    (i : Fin 4) :
    mixedDensityCoefficients (sourceField f) (sourceField (r • g)) i =
      r • mixedDensityCoefficients (sourceField f) (sourceField g) i := by
  unfold mixedDensityCoefficients
  rw [mixedLowerZero_smul_right r f g]
  simp only [densityPrincipalSecond_smul_right]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cases_zero, smul_mul_assoc, smul_smul, smul_sub]
      module
  | succ j =>
      simp only [Fin.cases_succ, smul_mul_assoc, smul_smul, smul_sub]
      module

/-- The original mixed coefficients are additive in the reader field. -/
theorem mixedCoefficients_add_left (f g h : Field289) (i : Fin 4) :
    mixedCoefficients (sourceField (f+g)) (sourceField h) i =
      mixedCoefficients (sourceField f) (sourceField h) i+
        mixedCoefficients (sourceField g) (sourceField h) i := by
  unfold mixedCoefficients
  rw [mixedDensityCoefficients_add_left, shellContactCoefficients_add_left]
  simp only [map_add]
  module

theorem mixedCoefficients_add_right (f g h : Field289) (i : Fin 4) :
    mixedCoefficients (sourceField f) (sourceField (g+h)) i =
      mixedCoefficients (sourceField f) (sourceField g) i+
        mixedCoefficients (sourceField f) (sourceField h) i := by
  unfold mixedCoefficients
  rw [mixedDensityCoefficients_add_right, shellContactCoefficients_add_right]
  simp only [map_add]
  module

theorem mixedCoefficients_smul_left (r : ℝ) (f g : Field289) (i : Fin 4) :
    mixedCoefficients (sourceField (r • f)) (sourceField g) i =
      r • mixedCoefficients (sourceField f) (sourceField g) i := by
  unfold mixedCoefficients
  rw [mixedDensityCoefficients_smul_left, shellContactCoefficients_smul_left]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [← smul_add]
  rw [map_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) r
    (canonicalMatrixRead
      (mixedDensityCoefficients (sourceField f) (sourceField g) i +
        shellContactCoefficients (sourceField f) (sourceField g) i))).symm

theorem mixedCoefficients_smul_right (r : ℝ) (f g : Field289) (i : Fin 4) :
    mixedCoefficients (sourceField f) (sourceField (r • g)) i =
      r • mixedCoefficients (sourceField f) (sourceField g) i := by
  unfold mixedCoefficients
  rw [mixedDensityCoefficients_smul_right, shellContactCoefficients_smul_right]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [← smul_add]
  rw [map_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) r
    (canonicalMatrixRead
      (mixedDensityCoefficients (sourceField f) (sourceField g) i +
        shellContactCoefficients (sourceField f) (sourceField g) i))).symm

/-- The real-bilinear package of the original mixed coefficients on the
    source 289-field. -/
def realMixedCoefficientBilinear (i : Fin 4) :
    Field289 →ₗ[ℝ] Field289 →ₗ[ℝ] FiberOperators where
  toFun := fun f =>
    { toFun := fun g => mixedCoefficients (sourceField f) (sourceField g) i
      map_add' := fun g h => mixedCoefficients_add_right f g h i
      map_smul' := fun r g => by
        simpa only [RingHom.id_apply] using
          mixedCoefficients_smul_right r f g i }
  map_add' := fun f g =>
    LinearMap.ext fun h => mixedCoefficients_add_left f g h i
  map_smul' := fun r f =>
    LinearMap.ext fun g => by
      simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk,
        AddHom.coe_mk]
      exact mixedCoefficients_smul_left r f g i

theorem realMixedCoefficientBilinear_source (f g : Field289) (i : Fin 4) :
    realMixedCoefficientBilinear i f g =
      mixedCoefficients (sourceField f) (sourceField g) i := rfl

end LowEnergy.GaussComposite.PhysicalFullFieldScattering
