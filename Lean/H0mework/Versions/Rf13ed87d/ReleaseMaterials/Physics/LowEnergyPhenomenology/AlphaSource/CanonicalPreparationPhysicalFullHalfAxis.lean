import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalSourceGrowth
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalHalfAxis
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalGreenFeedback
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix Interval InnerProductSpace
attribute [local irreducible] originalJacobi originalChange originalReadback originalRowLift
  sourceGreen extendedKernel sourceCompatibility

theorem weighted_integrable (f : ℝ→ℂ) (continuous : Continuous f) (hf : SourceSubexp f)
    (lambda : ℂ) (positive : 0<lambda.re) :
    IntegrableOn (fun r=>laplaceWeight lambda r*f r) (Ioi (0:ℝ)) :=by
  have half : 0<lambda.re/2:=by positivity
  have small : ∀ᶠr : ℝ in atTop,Real.exp (-(lambda.re/2)*r)*‖f r‖<1:=
    (hf (lambda.re/2) half).eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))
  obtain ⟨A,hA⟩:=eventually_atTop.mp small
  let B:=max A 0
  have bound (r : ℝ) (hr : B<r) : ‖laplaceWeight lambda r*f r‖≤Real.exp (-(lambda.re/2)*r):=by
    have s:=(hA r ((le_max_left A 0).trans hr.le)).le
    have w : Real.exp (-lambda.re*r)=Real.exp (-(lambda.re/2)*r)*Real.exp (-(lambda.re/2)*r):=by
      rw [←Real.exp_add];congr 1;ring
    calc
      _=Real.exp (-lambda.re*r)*‖f r‖:=by rw [norm_mul,laplace_norm]
      _=Real.exp (-(lambda.re/2)*r)*(Real.exp (-(lambda.re/2)*r)*‖f r‖):=by rw [w];ring
      _≤Real.exp (-(lambda.re/2)*r)*1:=mul_le_mul_of_nonneg_left s (Real.exp_pos _).le
      _=_:=mul_one _
  have majorant : IntegrableOn (fun r : ℝ=>Real.exp (-(lambda.re/2)*r)) (Ioi B):=by
    have h:=(integrableOn_Ioi_comp_mul_left_iff (fun r : ℝ=>Real.exp (-r)) B half).mpr
      (integrableOn_exp_neg_Ioi ((lambda.re/2)*B))
    simpa only [neg_mul] using h
  have wcont : Continuous (fun r=>laplaceWeight lambda r*f r):=by
    apply Continuous.mul
    · unfold laplaceWeight;fun_prop
    · exact continuous
  have tail : IntegrableOn (fun r=>laplaceWeight lambda r*f r) (Ioi B):=by
    apply majorant.mono' wcont.aestronglyMeasurable.restrict
    apply (ae_restrict_mem measurableSet_Ioi).mono
    exact bound
  have finite : IntegrableOn (fun r=>laplaceWeight lambda r*f r) (Ioc 0 B):=
    (wcont.intervalIntegrable (0:ℝ) B).1
  rw [←Ioc_union_Ioi_eq_Ioi (show (0:ℝ)≤B from le_max_right A 0)]
  exact finite.union tail

theorem actual_jet_integrable (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) (n : Fin 3) :
    IntegrableOn (fun r=>laplaceWeight lambda r*jetEntry (fullSourceJet q force response r i) n) (Ioi (0:ℝ)) :=by
  have h:=fullSourceJets_continuous q force response i
  have continuous : Continuous (fun r=>jetEntry (fullSourceJet q force response r i) n):=by
    fin_cases n
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  exact weighted_integrable _ continuous (fullJetEntry_subexp q force response i n) lambda positive

def halfForcing (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (lambda : ℂ) : Fin 289→ℂ:=
  fun i=>∫r in Ioi (0:ℝ),laplaceWeight lambda r*(fullSourceJet q force response r i).value

theorem actual_forcing_limit (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    Tendsto (fun T=>fullForcing q force response lambda T i) atTop (𝓝 (halfForcing q force response lambda i)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (actual_jet_integrable q force response lambda positive i 0) tendsto_id

private theorem listSubexp {ι : Type*} (ts : List ι) (f : ι→ℝ→ℂ)
    (h : ∀a∈ts,SourceSubexp (f a)) : SourceSubexp (fun r=>(ts.map (fun a=>f a r)).sum) :=by
  induction ts with
  | nil=>exact subexp_const 0
  | cons a rest ih=>
    simpa only [List.map_cons,List.sum_cons] using
      subexp_add (h a (by simp)) (ih (fun b hb=>h b (by simp [hb])))

theorem fullTimeSource_subexp (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (row : Fin 289) : SourceSubexp (fun r=>fullTimeSource q force response spatial r row) :=by
  unfold fullTimeSource
  apply listSubexp
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    exact subexp_mul (subexp_const _) (fullJetEntry_subexp q force response a.val.column (nativeTimeOrder a))
  · simp only [if_neg same]
    exact subexp_const 0

theorem actual_timeSource_integrable (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (positive : 0<lambda.re) (row : Fin 289) :
    IntegrableOn (fun r=>laplaceWeight lambda r*fullTimeSource q force response spatial r row) (Ioi (0:ℝ)) :=
  weighted_integrable _ (fullTimeSource_continuous q force response spatial row)
    (fullTimeSource_subexp q force response spatial row) lambda positive

def halfTimeSource (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) : Fin 289→ℂ:=
  fun row=>∫r in Ioi (0:ℝ),laplaceWeight lambda r*fullTimeSource q force response spatial r row

/-- The original source initial co-source is retained after the actual terminal decays. -/
theorem halfForcing_readback (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (positive : 0<lambda.re) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥhalfForcing q force response lambda) row=
      halfTimeSource q force response spatial lambda row+fullBoundary q force response spatial lambda 0 row :=by
  have left : Tendsto (fun T=>(originalReadback (fullMomentum spatial lambda)*ᵥfullForcing q force response lambda T) row)
      atTop (𝓝 ((originalReadback (fullMomentum spatial lambda)*ᵥhalfForcing q force response lambda) row)) :=by
    simp only [Matrix.mulVec,dotProduct]
    apply tendsto_finsetSum
    intro i _
    exact (actual_forcing_limit q force response lambda positive i).const_mul _
  have integral:=intervalIntegral_tendsto_integral_Ioi 0
    (actual_timeSource_integrable q force response spatial lambda positive row) tendsto_id
  have right:=integral.sub ((fullBoundary_decay q force response spatial lambda positive row).sub_const
    (fullBoundary q force response spatial lambda 0 row))
  simp only [zero_sub,sub_neg_eq_add] at right
  have same : (fun T=>(originalReadback (fullMomentum spatial lambda)*ᵥfullForcing q force response lambda T) row)=
      (fun T=>(∫r in (0:ℝ)..T,laplaceWeight lambda r*fullTimeSource q force response spatial r row)-
        (fullBoundary q force response spatial lambda T row-fullBoundary q force response spatial lambda 0 row)) :=
    funext (fun T=>fullForcing_readback q force response spatial lambda T row)
  exact tendsto_nhds_unique left (same.symm ▸ right)

def halfField (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val,lambda.property⟩
    (halfForcing q force response lambda.val)

theorem actual_field_limit (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re) (row : Fin 289) :
    Tendsto (fun T=>physicalField q force response k lambda T row) atTop (𝓝 (halfField q force response k lambda row)) :=by
  simp only [physicalField,halfField,PreparationVacuumOriginalGreenFeedback.sourceField,Matrix.mulVec,dotProduct]
  apply tendsto_finsetSum
  intro i _
  exact (actual_forcing_limit q force response lambda.val positive i).const_mul _

theorem halfField_equation (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val)*ᵥhalfField q force response k lambda=
      halfForcing q force response lambda.val-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val)
            (halfForcing q force response lambda.val) :=
  original_forced_field ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val,lambda.property⟩
    (halfForcing q force response lambda.val)

theorem halfField_cosources (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re) :
    halfField q force response k lambda=
      originalChange (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val)*ᵥ
        ((contactInverse (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val)+activeProjection*
          (extendedKernel (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val))⁻¹)*ᵥ
            (fun row=>halfTimeSource q force response (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val row+
              fullBoundary q force response (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val 0 row)) :=by
  have read : originalReadback (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val)*ᵥ
      halfForcing q force response lambda.val=_ :=
    funext (halfForcing_readback q force response (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val positive)
  unfold halfField PreparationVacuumOriginalGreenFeedback.sourceField sourceGreen
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,read]

/-- The numerical tail is a source integral, independent of any target coupling. -/
def sourceTail (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (T : ℝ) (i : Fin 289) : ℝ:=
  ∫r in Ioi T,‖laplaceWeight lambda r*(fullSourceJet q force response r i).value‖

theorem sourceTail_zero (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    Tendsto (fun T=>sourceTail q force response lambda T i) atTop (𝓝 0) :=by
  have actual : IntegrableOn (fun r=>‖laplaceWeight lambda r*(fullSourceJet q force response r i).value‖) (Ioi (0:ℝ)):=by
    unfold IntegrableOn
    convert (actual_jet_integrable q force response lambda positive i 0).norm using 1; rfl
  have limit:=intervalIntegral_tendsto_integral_Ioi 0 actual tendsto_id
  have tailLimit:=limit.const_sub (∫r in Ioi (0:ℝ),‖laplaceWeight lambda r*(fullSourceJet q force response r i).value‖)
  apply (show Tendsto _ atTop (𝓝 (0:ℝ)) from by simpa only [sub_self] using tailLimit).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  have same:=intervalIntegral.integral_interval_add_Ioi actual (actual.mono_set (Ioi_subset_Ioi hT))
  change _=sourceTail q force response lambda T i
  apply sub_eq_iff_eq_add.mpr
  convert! same.symm using 1; first | rfl | simp only [sourceTail,add_comm,id_eq]

theorem forcingTail_bound (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (T : ℝ) (nonnegative : 0≤T) (i : Fin 289) :
    ‖halfForcing q force response lambda i-fullForcing q force response lambda T i‖ ≤ sourceTail q force response lambda T i :=by
  have integral : IntegrableOn (fun r=>laplaceWeight lambda r*(fullSourceJet q force response r i).value) (Ioi (0:ℝ)):=by
    simpa [jetEntry] using actual_jet_integrable q force response lambda positive i 0
  have tail:=integral.mono_set (Ioi_subset_Ioi nonnegative)
  have equation:=intervalIntegral.integral_interval_add_Ioi integral tail
  have difference : halfForcing q force response lambda i-fullForcing q force response lambda T i=
      ∫r in Ioi T,laplaceWeight lambda r*(fullSourceJet q force response r i).value :=by
    apply sub_eq_iff_eq_add.mpr
    simpa only [halfForcing,fullForcing,add_comm] using equation.symm
  rw [difference]
  exact norm_integral_le_integral_norm _

def fieldTail (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (T : ℝ) (row : Fin 289) : ℝ:=
  ∑i : Fin 289,‖sourceGreen
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val,lambda.property⟩ row i‖*
      sourceTail q force response lambda.val T i

theorem fieldTail_zero (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re) (row : Fin 289) :
    Tendsto (fun T=>fieldTail q force response k lambda T row) atTop (𝓝 0) :=by
  unfold fieldTail
  have h:=tendsto_finsetSum Finset.univ (fun i _=>(sourceTail_zero q force response lambda.val positive i).const_mul
    ‖sourceGreen ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial k) lambda.val,lambda.property⟩ row i‖)
  simpa only [mul_zero,Finset.sum_const_zero] using h

theorem actual_fieldTail_bound (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re)
    (T : ℝ) (nonnegative : 0≤T) (row : Fin 289) :
    ‖halfField q force response k lambda row-physicalField q force response k lambda T row‖ ≤ fieldTail q force response k lambda T row :=by
  simp only [halfField,physicalField,PreparationVacuumOriginalGreenFeedback.sourceField,Matrix.mulVec,dotProduct,fieldTail]
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (forcingTail_bound q force response lambda.val positive T nonnegative i) (norm_nonneg _)

end LowEnergy.PreparationVacuumPhysicalHalfAxis
