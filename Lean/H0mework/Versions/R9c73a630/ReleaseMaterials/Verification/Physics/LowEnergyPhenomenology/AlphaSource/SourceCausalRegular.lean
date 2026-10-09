import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualSoftSelection
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumCausalPoleResponse
open CanonicalGradedSpatialSource PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalFeedback PreparationVacuumSoftPoleSelection
open Filter Set
open scoped Matrix BigOperators Topology

def fixedMomentum (k : PhysicalMomentum) (lambda : ℂ) : Fin 4→ℂ:=
  fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda

def causalLambda (eta omega : ℝ) : ℂ:=(eta:ℂ)-Complex.I*(omega:ℂ)

def causalMomentum (eta omega : ℝ) (k : PhysicalMomentum) : Fin 4→ℂ:=fixedMomentum k (causalLambda eta omega)

theorem causalLambda_re (eta omega : ℝ) : (causalLambda eta omega).re=eta:=by
  simp [causalLambda]

theorem causalLambda_im (eta omega : ℝ) : (causalLambda eta omega).im= -omega:=by
  simp [causalLambda]

theorem fixedMomentum_sheet (epsilon s : ℝ) (n : PhysicalMomentum) :
    fixedMomentum (epsilon^2 • n) (sheetLambda epsilon s)=frequencyRay epsilon s n:=by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · change -Complex.I*((epsilon^2*s:ℝ):ℂ)= -Complex.I*((s*epsilon^2:ℝ):ℂ)
    rw [mul_comm (epsilon^2) s]
  · rfl

theorem causalMomentum_zero (epsilon s : ℝ) (n : PhysicalMomentum) :
    causalMomentum 0 (sourceFrequency epsilon s) (epsilon^2 • n)=frequencyRay epsilon s n:=by
  simpa only [causalMomentum,causalLambda,Complex.ofReal_zero,zero_sub,sheetLambda,neg_mul] using fixedMomentum_sheet epsilon s n

private theorem sourceMatrix_analytic (terms : List SourceTerm) (k : PhysicalMomentum) (i j : Fin 289) (z : ℂ) :
    AnalyticAt ℂ (fun lambda=>sourceMatrix terms (fixedMomentum k lambda) i j) z:=by
  induction terms with
  | nil=>exact analyticAt_const
  | cons a rest ih=>
    have term : AnalyticAt ℂ (fun lambda=>a.matrix (fixedMomentum k lambda) i j) z:=by
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value fixedMomentum fullMomentum
        change AnalyticAt ℂ (fun lambda=>coefficientValue a.coefficient*
          (lambda^a.powers.temporal*(physicalSpatial k 0)^a.powers.first*
            (physicalSpatial k 1)^a.powers.second*(physicalSpatial k 2)^a.powers.third)) z
        exact analyticAt_const.mul ((((analyticAt_id.pow _).mul analyticAt_const).mul analyticAt_const).mul analyticAt_const)
      · exact analyticAt_const
    exact term.add ih

/-- The original entire determinant is generated directly by all active source terms. -/
theorem sourceDeterminant_analytic (k : PhysicalMomentum) (z : ℂ) :
    AnalyticAt ℂ (fun lambda=>(extendedKernel (fixedMomentum k lambda)).det) z:=by
  have entry (i j : Fin 289) : AnalyticAt ℂ (fun lambda=>extendedKernel (fixedMomentum k lambda) i j) z:=
    (sourceMatrix_analytic activeTerms k i j z).add analyticAt_const
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro sigma _
  apply AnalyticAt.mul analyticAt_const
  exact Finset.analyticAt_fun_prod _ (fun i _=>entry _ i)

/-- Real source-generated punctured points rule out the locally-zero analytic alternative. -/
theorem sourceSheet_complex_regular (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀ᶠ lambda in 𝓝[≠] (sheetLambda e.val (sourceSheet branch n unit e.val)),
      fixedMomentum (e.val^2 • n) lambda∈regularSource:=by
  filter_upwards [sourceSheet_regular_near branch n unit] with e realRegular
  let center:=sourceSheet branch n unit e.val
  rcases (sourceDeterminant_analytic (e.val^2 • n) (sheetLambda e.val center)).eventually_eq_zero_or_eventually_ne_zero with zero|nonzero
  · have continuous : Continuous (sheetLambda e.val):=by unfold sheetLambda sourceFrequency;fun_prop
    have along := (continuous.tendsto center).eventually zero
    have punctured:=along.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] center≤𝓝 center)
    obtain ⟨t,⟨_,_,regular⟩,vanish⟩:=(realRegular.and punctured).exists
    rw [fixedMomentum_sheet] at vanish
    exact False.elim ((isUnit_iff_ne_zero.mp regular) vanish)
  · filter_upwards [nonzero] with lambda nonzero
    exact isUnit_iff_ne_zero.mpr nonzero

private theorem causal_axis_tendsto (omega : ℝ) :
    Tendsto (fun eta : ℝ=>causalLambda eta omega) (𝓝[>] 0) (𝓝[≠] (-Complex.I*(omega:ℂ))):=by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have continuous : Continuous (fun eta : ℝ=>causalLambda eta omega):=by unfold causalLambda;fun_prop
    simpa only [causalLambda,Complex.ofReal_zero,zero_sub,neg_mul] using
      (continuous.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  · filter_upwards [self_mem_nhdsWithin] with eta positive
    change causalLambda eta omega≠ -Complex.I*(omega:ℂ)
    intro equal
    have real:=congrArg Complex.re equal
    simp only [causalLambda_re,Complex.neg_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_self,neg_zero] at real
    exact ne_of_gt positive real

/-- The same physical sheet generates a nonempty damped domain for the original uncleared full field. -/
theorem sourceSheet_causal_regular (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀ᶠ eta in 𝓝[>] (0:ℝ),
      causalMomentum eta (sourceFrequency e.val (sourceSheet branch n unit e.val)) (e.val^2 • n)∈regularSource:=by
  filter_upwards [sourceSheet_complex_regular branch n unit] with e legal
  exact (causal_axis_tendsto (sourceFrequency e.val (sourceSheet branch n unit e.val))).eventually legal

theorem sourceSheet_causal_nonempty (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∃e : scaleDomain,∃eta : ℝ,0<eta ∧
      causalMomentum eta (sourceFrequency e.val (sourceSheet branch n unit e.val)) (e.val^2 • n)∈regularSource:=by
  let : scaleApproach.NeBot:=scaleApproach_nonempty
  obtain ⟨e,legal⟩:=(sourceSheet_causal_regular branch n unit).exists
  have positive : ∀ᶠ eta : ℝ in 𝓝[>] 0,0<eta:=self_mem_nhdsWithin
  obtain ⟨eta,positive,regular⟩:=(positive.and legal).exists
  exact ⟨e,eta,positive,regular⟩

end LowEnergy.PreparationVacuumCausalPoleResponse
