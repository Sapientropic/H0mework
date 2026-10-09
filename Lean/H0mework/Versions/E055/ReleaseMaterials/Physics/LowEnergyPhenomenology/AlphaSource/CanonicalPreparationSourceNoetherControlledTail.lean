import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNoetherModePrice

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNoetherResponsePrice
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMatterEulerFeedback PreparationVacuumPhysicalTailPrice PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open Filter Set MeasureTheory
open scoped Topology Interval BigOperators Matrix
attribute [local irreducible] sourceGreen originalJacobi originalRowLift sourceCompatibility originalReader36

def modeDecayCoefficient (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : ℂ) (i : Fin 289) : ℝ:=
  noetherModeCoefficient q force response (lambda.re/8) (-wave) i

theorem modeDecayCoefficient_nonnegative (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    0 ≤ modeDecayCoefficient q force response wave lambda i :=
  noetherModeCoefficient_nonnegative q force response _ (by positivity) _ _

theorem weightedModeSource_price (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : ℂ) (positive : 0<lambda.re) (t : ℝ) (future : 0≤t) (i : Fin 289) :
    ‖laplaceWeight lambda t*(modeJet q force response wave t i).value‖≤
      modeDecayCoefficient q force response wave lambda i*Real.exp (-(lambda.re/2)*t) :=by
  have source:=noetherRealMode_price q force response (lambda.re/8) t (by positivity) future (-wave) i
  rw [norm_mul,laplace_norm]
  refine (mul_le_mul_of_nonneg_left source (Real.exp_pos _).le).trans_eq ?_
  change Real.exp (-lambda.re*t)*(modeDecayCoefficient q force response wave lambda i*
    Real.exp (4*(lambda.re/8)*t))=_
  rw [mul_left_comm,←Real.exp_add]
  congr 1
  congr 1
  ring

theorem weightedModeSource_integrable (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    IntegrableOn (fun t=>laplaceWeight lambda t*(modeJet q force response wave t i).value) (Ioi (0:ℝ)) :=by
  have majorant : IntegrableOn (fun t=>modeDecayCoefficient q force response wave lambda i*
      Real.exp (-(lambda.re/2)*t)) (Ioi (0:ℝ)):=
    (integrableOn_exp_mul_Ioi (a:=-(lambda.re/2)) (by linarith) 0).const_mul _
  have continuous : Continuous (fun t=>laplaceWeight lambda t*(modeJet q force response wave t i).value):=by
    have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
    exact weight.mul (realEulerTimeJets_continuous q force response (-wave) i).1
  apply majorant.mono' continuous.aestronglyMeasurable.restrict
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  exact weightedModeSource_price q force response wave lambda positive t ht.le i

def modeHalfForcing (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : ℂ) : Fin 289→ℂ:=
  fun i=>∫t in Ioi (0:ℝ),laplaceWeight lambda t*(modeJet q force response wave t i).value

theorem modeForcing_halfAxis (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    Tendsto (fun T=>modeForcing q force response wave lambda T i) atTop
      (𝓝 (modeHalfForcing q force response wave lambda i)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (weightedModeSource_integrable q force response wave lambda positive i) tendsto_id

def explicitModeTail (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (i : Fin 289) : ℝ:=
  (2/lambda.re)*modeDecayCoefficient q force response wave lambda i*Real.exp (-(lambda.re/2)*T)

theorem modeForcing_tail_price (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : ℂ) (positive : 0<lambda.re)
    (T : ℝ) (future : 0≤T) (i : Fin 289) :
    ‖modeHalfForcing q force response wave lambda i-modeForcing q force response wave lambda T i‖≤
      explicitModeTail q force response wave lambda T i :=by
  have integral:=weightedModeSource_integrable q force response wave lambda positive i
  have tail:=integral.mono_set (Ioi_subset_Ioi future)
  have equation:=intervalIntegral.integral_interval_add_Ioi integral tail
  have difference : modeHalfForcing q force response wave lambda i-modeForcing q force response wave lambda T i=
      ∫t in Ioi T,laplaceWeight lambda t*(modeJet q force response wave t i).value:=by
    apply sub_eq_iff_eq_add.mpr
    simpa only [modeHalfForcing,modeForcing,add_comm] using equation.symm
  have majorant : IntegrableOn (fun t=>modeDecayCoefficient q force response wave lambda i*
      Real.exp (-(lambda.re/2)*t)) (Ioi T):=
    (integrableOn_exp_mul_Ioi (a:=-(lambda.re/2)) (by linarith) T).const_mul _
  have bound : ∀ᵐt ∂volume.restrict (Ioi T),
      ‖laplaceWeight lambda t*(modeJet q force response wave t i).value‖≤
        modeDecayCoefficient q force response wave lambda i*Real.exp (-(lambda.re/2)*t) :=by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    exact weightedModeSource_price q force response wave lambda positive t (future.trans ht.le) i
  rw [difference]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae tail.norm majorant bound).trans_eq ?_)
  rw [integral_const_mul,integral_exp_mul_Ioi (show -(lambda.re/2)<0 by linarith) T]
  unfold explicitModeTail
  field_simp

def modeHalfField (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩ (modeHalfForcing q force response wave lambda.val)

theorem modeHalfField_equation (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) :
    originalJacobi (fullMomentum (physicalSpatial wave) lambda.val)*ᵥmodeHalfField q force response wave lambda=
      modeHalfForcing q force response wave lambda.val-originalRowLift (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
        sourceCompatibility (fullMomentum (physicalSpatial wave) lambda.val) (modeHalfForcing q force response wave lambda.val) :=
  original_forced_field ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩ _

def modeFieldCoefficient (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) (row : Fin 289) : ℝ:=
  ∑i : Fin 289,‖sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩ row i‖*
    modeDecayCoefficient q force response wave lambda.val i

def explicitModeFieldTail (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) (T : ℝ) (row : Fin 289) : ℝ:=
  (2/lambda.val.re)*modeFieldCoefficient q force response wave lambda row*Real.exp (-(lambda.val.re/2)*T)

theorem modeHalfField_tail_price (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) (positive : 0<lambda.val.re)
    (T : ℝ) (future : 0≤T) (row : Fin 289) :
    ‖modeHalfField q force response wave lambda row-modeField q force response wave lambda T row‖≤
      explicitModeFieldTail q force response wave lambda T row :=by
  change ‖(∑i : Fin 289,sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩ row i*
      modeHalfForcing q force response wave lambda.val i)-
    (∑i : Fin 289,sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩ row i*
      modeForcing q force response wave lambda.val T i)‖≤_
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have each : (∑i : Fin 289,‖sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩ row i*
      modeHalfForcing q force response wave lambda.val i-
    sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩ row i*
      modeForcing q force response wave lambda.val T i‖)≤
      ∑i : Fin 289,‖sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩ row i‖*
        explicitModeTail q force response wave lambda.val T i:=by
    apply Finset.sum_le_sum
    intro i _
    rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (modeForcing_tail_price q force response wave lambda.val positive T future i) (norm_nonneg _)
  refine each.trans_eq ?_
  simp only [explicitModeTail,explicitModeFieldTail,modeFieldCoefficient,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _=>by ring)

def modeHalfCurvature (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) : Fin 36→ℂ:=
  originalReader36 (fullMomentum (physicalSpatial wave) lambda.val)*ᵥmodeHalfField q force response wave lambda

def explicitModeCurvatureTail (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) (T : ℝ) (row : Fin 36) : ℝ:=
  ∑i : Fin 289,‖originalReader36 (fullMomentum (physicalSpatial wave) lambda.val) row i‖*
    explicitModeFieldTail q force response wave lambda T i

theorem modeHalfCurvature_tail_price (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (positive : 0<lambda.val.re) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (T : ℝ) (future : 0≤T) (row : Fin 36) :
    ‖modeHalfCurvature q force true wave lambda row-deriv (actionFieldCurvatureCurve q force wave lambda T) 0 row‖≤
      explicitModeCurvatureTail q force true wave lambda T row :=by
  rw [(actionFieldCurvature_generated q force wave lambda hz hw T).deriv]
  change ‖(∑i : Fin 289,originalReader36 (fullMomentum (physicalSpatial wave) lambda.val) row i*
      modeHalfField q force true wave lambda i)-
    (∑i : Fin 289,originalReader36 (fullMomentum (physicalSpatial wave) lambda.val) row i*
      modeField q force true wave lambda T i)‖≤_
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (modeHalfField_tail_price q force true wave lambda positive T future i) (norm_nonneg _)

theorem explicitModeTail_zero (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    Tendsto (fun T=>explicitModeTail q force response wave lambda T i) atTop (𝓝 0) :=by
  have decay : Tendsto (fun T : ℝ=>Real.exp (-(lambda.re/2)*T)) atTop (𝓝 0):=by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (lambda.re/2) (by positivity)
  simpa only [explicitModeTail,mul_zero] using decay.const_mul
    ((2/lambda.re)*modeDecayCoefficient q force response wave lambda i)

theorem explicitModeFieldTail_zero (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) (positive : 0<lambda.val.re) (row : Fin 289) :
    Tendsto (fun T=>explicitModeFieldTail q force response wave lambda T row) atTop (𝓝 0) :=by
  have decay : Tendsto (fun T : ℝ=>Real.exp (-(lambda.val.re/2)*T)) atTop (𝓝 0):=by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (lambda.val.re/2) (by positivity)
  simpa only [explicitModeFieldTail,mul_zero] using decay.const_mul
    ((2/lambda.val.re)*modeFieldCoefficient q force response wave lambda row)

theorem explicitModeCurvatureTail_zero (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) (positive : 0<lambda.val.re) (row : Fin 36) :
    Tendsto (fun T=>explicitModeCurvatureTail q force response wave lambda T row) atTop (𝓝 0) :=by
  have fields:=tendsto_finsetSum Finset.univ (fun i _=>
    (explicitModeFieldTail_zero q force response wave lambda positive i).const_mul
      ‖originalReader36 (fullMomentum (physicalSpatial wave) lambda.val) row i‖)
  simpa only [explicitModeCurvatureTail,mul_zero,Finset.sum_const_zero] using fields

end LowEnergy.PreparationVacuumNoetherResponsePrice
