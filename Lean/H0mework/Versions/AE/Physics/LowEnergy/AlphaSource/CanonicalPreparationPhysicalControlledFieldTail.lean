import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationPhysicalFiveSourcePrice

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalTailPrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumOriginalGreenFeedback
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
attribute [local irreducible] sourceGreen scalarCoefficient sourceTail fieldTail factorialBudget variationBudget

/-- Eta controls only truncation error and is generated from the requested damping. -/
def decayCoefficient (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (i : Fin 289) : ℝ:=scalarCoefficient q force response (lambda.re/8) i

theorem decayCoefficient_nonnegative (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) : 0≤decayCoefficient q force response lambda i:=
  scalarCoefficient_nonnegative q force response _ (by positivity) i

theorem weightedSource_envelope (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (t : ℝ) (future : 0≤t) (i : Fin 289) :
    ‖laplaceWeight lambda t*(fullSourceJet q force response t i).value‖≤
      decayCoefficient q force response lambda i*Real.exp (-(lambda.re/2)*t) :=by
  have eta : 0<lambda.re/8:=by positivity
  have source:=actualSource_price q force response (lambda.re/8) t eta future i
  rw [norm_mul,laplace_norm]
  refine (mul_le_mul_of_nonneg_left source (Real.exp_pos _).le).trans_eq ?_
  change Real.exp (-lambda.re*t)*(decayCoefficient q force response lambda i*
    Real.exp (4*(lambda.re/8)*t))=_
  rw [mul_left_comm,←Real.exp_add]
  congr 1
  congr 1
  ring

def explicitSourceTail (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (T : ℝ) (i : Fin 289) : ℝ:=
  (2/lambda.re)*decayCoefficient q force response lambda i*Real.exp (-(lambda.re/2)*T)

theorem sourceTail_price (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (T : ℝ) (nonnegative : 0≤T) (i : Fin 289) :
    sourceTail q force response lambda T i≤explicitSourceTail q force response lambda T i :=by
  have actual : IntegrableOn (fun r=>‖laplaceWeight lambda r*(fullSourceJet q force response r i).value‖) (Ioi (0:ℝ)):=by
    unfold IntegrableOn
    convert (actual_jet_integrable q force response lambda positive i 0).norm using 1; rfl
  have tail:=actual.mono_set (Ioi_subset_Ioi nonnegative)
  have majorant : IntegrableOn (fun r=>decayCoefficient q force response lambda i*Real.exp (-(lambda.re/2)*r)) (Ioi T):=
    (integrableOn_exp_mul_Ioi (a:=-(lambda.re/2)) (by linarith) T).const_mul _
  have bound : ∀ᵐr ∂volume.restrict (Ioi T),
      ‖laplaceWeight lambda r*(fullSourceJet q force response r i).value‖≤
        decayCoefficient q force response lambda i*Real.exp (-(lambda.re/2)*r) :=by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro r hr
    exact weightedSource_envelope q force response lambda positive r (nonnegative.trans hr.le) i
  have integral:=(integral_mono_ae tail majorant bound)
  unfold sourceTail
  refine integral.trans_eq ?_
  change (∫r in Ioi T,decayCoefficient q force response lambda i*Real.exp (-(lambda.re/2)*r))=_
  rw [integral_const_mul,integral_exp_mul_Ioi (show -(lambda.re/2)<0 by linarith) T]
  unfold explicitSourceTail
  field_simp

theorem actualForcing_price (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (T : ℝ) (nonnegative : 0≤T) (i : Fin 289) :
    ‖halfForcing q force response lambda i-fullForcing q force response lambda T i‖≤
      explicitSourceTail q force response lambda T i :=
  (forcingTail_bound q force response lambda positive T nonnegative i).trans
    (sourceTail_price q force response lambda positive T nonnegative i)

def fieldCoefficient (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (row : Fin 289) : ℝ:=
  ∑i : Fin 289,‖sourceGreen ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val,lambda.property⟩ row i‖*
    decayCoefficient q force response lambda.val i

def explicitFieldTail (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (T : ℝ) (row : Fin 289) : ℝ:=
  (2/lambda.val.re)*fieldCoefficient q force response k lambda row*Real.exp (-(lambda.val.re/2)*T)

theorem fieldTail_price (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re)
    (T : ℝ) (nonnegative : 0≤T) (row : Fin 289) :
    fieldTail q force response k lambda T row≤explicitFieldTail q force response k lambda T row :=by
  unfold fieldTail
  have price : (∑i : Fin 289,‖sourceGreen ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val,lambda.property⟩ row i‖*
      sourceTail q force response lambda.val T i)≤
    ∑i : Fin 289,‖sourceGreen ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val,lambda.property⟩ row i‖*
      explicitSourceTail q force response lambda.val T i:=by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (sourceTail_price q force response lambda.val positive T nonnegative i) (norm_nonneg _)
  refine price.trans_eq ?_
  unfold explicitSourceTail explicitFieldTail fieldCoefficient
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem actualField_price (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re)
    (T : ℝ) (nonnegative : 0≤T) (row : Fin 289) :
    ‖halfField q force response k lambda row-physicalField q force response k lambda T row‖≤
      explicitFieldTail q force response k lambda T row :=
  (actual_fieldTail_bound q force response k lambda positive T nonnegative row).trans
    (fieldTail_price q force response k lambda positive T nonnegative row)

theorem explicitSourceTail_zero (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    Tendsto (fun T=>explicitSourceTail q force response lambda T i) atTop (𝓝 0) :=by
  have decay : Tendsto (fun T : ℝ=>Real.exp (-(lambda.re/2)*T)) atTop (𝓝 0):=by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (lambda.re/2) (by positivity)
  simpa only [explicitSourceTail,mul_zero] using decay.const_mul ((2/lambda.re)*decayCoefficient q force response lambda i)

theorem explicitFieldTail_zero (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re) (row : Fin 289) :
    Tendsto (fun T=>explicitFieldTail q force response k lambda T row) atTop (𝓝 0) :=by
  have decay : Tendsto (fun T : ℝ=>Real.exp (-(lambda.val.re/2)*T)) atTop (𝓝 0):=by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (lambda.val.re/2) (by positivity)
  simpa only [explicitFieldTail,mul_zero] using decay.const_mul ((2/lambda.val.re)*fieldCoefficient q force response k lambda row)

end LowEnergy.PreparationVacuumPhysicalTailPrice
