import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedTransferIR
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMOriginFields
import H0mework.Physics.GaugeAction.P286SourceRelativeWardAlgebra

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMInvariantCurvature
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation StageNineP286SourceRelativeWardAlgebra
open SourcePropagationNativeActionHessian PreparationVacuumMixedFieldReturn
open PreparationVacuumLowerClassical PreparationCoordinates
open ActualEMGaugeCurvature ActualEMDressedTransferIR ActualEMDressedGaugePole
open ActualDressedNoether ActualDressedFullCoulomb ActualEMCompleteOrbit
open PreparationVacuumSoftPoleSelection PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet CanonicalGradedSpatialSource
open PreparationPhysicalNativePoleChargeReturn PreparationVacuumOriginalGreenFeedback
open Filter
open scoped BigOperators Matrix Topology
attribute [local irreducible] nativeGaugeDensity nativeGaugeRawCurvature nativeGaugeLinearCurvature
  nativeGaugeQuadraticCurvature nativeBranchVector fullGaugeCurvature sourceGaugeCurvature0

/-- The actual source Lie pairing is extended bilinearly to Fourier amplitudes. -/
def complexGaugePair (x y : Fin 12→ℂ) : ℂ :=
  2*(x 0*y 0+x 1*y 1+x 2*y 2+x 3*y 3+x 4*y 4+x 5*y 5+
    x 6*y 6+x 7*y 7+x 8*y 8+x 9*y 9+x 10*y 10)+x 6*y 7+x 7*y 6+x 11*y 11

private theorem complex_pair_real (x y : Fin 12→ℝ) :
    complexGaugePair (fun a=>(x a:ℂ)) (fun a=>(y a:ℂ))=(rawGaugePair x y:ℂ) := by
  simp only [complexGaugePair,rawGaugePair,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]

/-- This observable is the Lie-pairing Gram of the complete original curvature, not an action coefficient. -/
def nativeCurvatureGram (jet : NativeFirstJet) (pair other : Fin 6) : ℝ :=
  rawGaugePair (nativeGaugeRawCurvature jet pair) (nativeGaugeRawCurvature jet other)

theorem native_curvature_gram_holonomic (jet : NativeFirstJet) (pair other : Fin 6) :
    nativeCurvatureGram jet pair other=
      p286LiePairing (holonomicGaugeCurvature (nativeConfiguration (affineSignal jet)) 0 pair)
        (holonomicGaugeCurvature (nativeConfiguration (affineSignal jet)) 0 other) := by
  unfold nativeCurvatureGram nativeGaugeRawCurvature
  rw [←rawGaugePair_source]
  simp only [nativeGaugeCurvature_generated,p286CoordinateLiePairing,LinearEquiv.symm_apply_apply]

def curvatureGramFirst (jet : NativeFirstJet) (pair other : Fin 6) : ℝ :=
  rawGaugePair (sourceGaugeCurvature0 pair) (nativeGaugeLinearCurvature jet other)+
    rawGaugePair (nativeGaugeLinearCurvature jet pair) (sourceGaugeCurvature0 other)

def curvatureGramSecond (jet : NativeFirstJet) (pair other : Fin 6) : ℝ :=
  2*(rawGaugePair (sourceGaugeCurvature0 pair) (nativeGaugeQuadraticCurvature jet other)+
    rawGaugePair (nativeGaugeLinearCurvature jet pair) (nativeGaugeLinearCurvature jet other)+
    rawGaugePair (nativeGaugeQuadraticCurvature jet pair) (sourceGaugeCurvature0 other))

private theorem curvature_zero (pair : Fin 6) :
    nativeGaugeRawCurvature 0 pair=sourceGaugeCurvature0 pair := by
  simpa only [zero_smul,zero_pow (by omega : 2≠0),add_zero] using
    nativeGaugeRawCurvature_ray (0:NativeFirstJet) 0 pair

private theorem curvature_ray_first (jet : NativeFirstJet) (pair : Fin 6) (r : ℝ) :
    HasDerivAt (fun (t : ℝ)=>nativeGaugeRawCurvature (t • jet) pair)
      (nativeGaugeLinearCurvature jet pair+(2*r) • nativeGaugeQuadraticCurvature jet pair) r := by
  simpa only [nativeGaugeRawCurvature_ray] using coordinateQuadratic_derivative
    (sourceGaugeCurvature0 pair) (nativeGaugeLinearCurvature jet pair) (nativeGaugeQuadraticCurvature jet pair) r

private theorem curvature_ray_second (jet : NativeFirstJet) (pair : Fin 6) :
    HasDerivAt (deriv (fun (t : ℝ)=>nativeGaugeRawCurvature (t • jet) pair))
      ((2:ℝ) • nativeGaugeQuadraticCurvature jet pair) 0 := by
  simpa only [nativeGaugeRawCurvature_ray] using coordinateQuadratic_second
    (sourceGaugeCurvature0 pair) (nativeGaugeLinearCurvature jet pair) (nativeGaugeQuadraticCurvature jet pair)

/-- Both curvature legs are differentiated on the same original holonomic ray. -/
theorem curvature_gram_first_generated (jet : NativeFirstJet) (pair other : Fin 6) :
    HasDerivAt (fun (r : ℝ)=>nativeCurvatureGram (r • jet) pair other) (curvatureGramFirst jet pair other) 0 := by
  have first (p : Fin 6) : HasDerivAt (fun (r : ℝ)=>nativeGaugeRawCurvature (r • jet) p)
      (nativeGaugeLinearCurvature jet p) 0 := by
    simpa only [mul_zero,zero_smul,add_zero] using curvature_ray_first jet p 0
  have result := rawGaugePair_first _ _ _ _ 0 (first pair) (first other)
  simpa only [nativeCurvatureGram,curvatureGramFirst,zero_smul,curvature_zero] using result

/-- Background times second curvature is retained alongside the two first-curvature legs. -/
theorem curvature_gram_second_generated (jet : NativeFirstJet) (pair other : Fin 6) :
    HasDerivAt (deriv (fun (r : ℝ)=>nativeCurvatureGram (r • jet) pair other))
      (curvatureGramSecond jet pair other) 0 := by
  have first (p : Fin 6) : HasDerivAt (fun (r : ℝ)=>nativeGaugeRawCurvature (r • jet) p)
      (nativeGaugeLinearCurvature jet p) 0 := by
    simpa only [mul_zero,zero_smul,add_zero] using curvature_ray_first jet p 0
  have near (p : Fin 6) : ∀ᶠr in 𝓝 (0:ℝ),DifferentiableAt ℝ
      (fun (t : ℝ)=>nativeGaugeRawCurvature (t • jet) p) r :=
    Filter.Eventually.of_forall (fun (r : ℝ)=>(curvature_ray_first jet p r).differentiableAt)
  have result := rawGaugePair_second _ _ _ _ _ _ (first pair) (first other)
    (curvature_ray_second jet pair) (curvature_ray_second jet other) (near pair) (near other)
  apply result.congr_deriv
  simp only [zero_smul,curvature_zero,curvatureGramSecond,rawGaugePair,Pi.smul_apply,smul_eq_mul]
  ring

/-- The same jet pays the complete original BF/Hodge action, with auxiliary, curvature and coframe terms. -/
theorem curvature_gram_and_original_action (jet : NativeFirstJet) (pair other : Fin 6) :
    HasDerivAt (deriv (fun (r : ℝ)=>nativeCurvatureGram (r • jet) pair other))
        (curvatureGramSecond jet pair other) 0 ∧
      HasDerivAt (deriv (fun (r : ℝ)=>nativeGaugeDensity (r • jet))) (2*gaugeFlatQuadratic jet) 0 := by
  refine ⟨curvature_gram_second_generated jet pair other,?_⟩
  simpa only [nativeGaugeQuadratic_flat] using nativeGaugeDensity_second jet

/-- Infinitesimal gauge invariance uses the original P286 trace pairing in all twelve Lie directions. -/
theorem curvature_pair_orbit_balance (a x y : P286LieBlockData) :
    p286LiePairing (p286LieBracket a x) y+p286LiePairing x (p286LieBracket a y)=0 := by
  have invariant := p286LiePairing_bracket_left x a y
  rw [StageNineP286BracketCalculus.p286LieBracket_skew a x]
  rw [←neg_one_smul ℝ (p286LieBracket x a)]
  rw [p286LiePairing_smul_left,invariant]
  ring

/-- Original background curvature fixes the invariant Fourier reader; no photon direction is inserted. -/
def invariantCurvatureRead (p : Fin 4→ℂ) (f : Fin 289→ℂ) (pair other : Fin 6) : ℂ :=
  complexGaugePair (fun a=>(sourceGaugeCurvature0 pair a:ℂ)) (fullGaugeCurvature p f other)+
    complexGaugePair (fullGaugeCurvature p f pair) (fun a=>(sourceGaugeCurvature0 other a:ℂ))

theorem invariant_curvature_original (p : Fin 4→ℂ) (f : Fin 289→ℂ) (pair other : Fin 6) :
    invariantCurvatureRead p f pair other=
      (curvatureGramFirst (gaugeFourierJet p f false) pair other:ℂ)+Complex.I*
        (curvatureGramFirst (gaugeFourierJet p f true) pair other:ℂ) := by
  unfold invariantCurvatureRead complexGaugePair curvatureGramFirst rawGaugePair
  simp only [full_gauge_curvature_original]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

theorem invariant_curvature_continuous (pair other : Fin 6) :
    Continuous (fun pf : (Fin 4→ℂ) × (Fin 289→ℂ)=>invariantCurvatureRead pf.1 pf.2 pair other) := by
  have curvature (p : Fin 6) (a : Fin 12) := full_gauge_curvature_continuous p a
  unfold invariantCurvatureRead complexGaugePair
  fun_prop

end LowEnergy.GaussComposite.ActualEMInvariantCurvature
