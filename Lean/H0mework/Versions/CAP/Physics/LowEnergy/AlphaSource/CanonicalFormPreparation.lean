import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.BoundedRemainder
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompletion
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparedFrequency

/-! A form factor and remainder generate a common unit near-state, then the
original CAR and full-Y consumers read that same state. The actual source
factor, remainder and preparation identity must still instantiate this mouth. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalFormPreparation
open GaussCoreHilbert GaussDensityCore GaussComposite.SourceGraph
open CanonicalScalarPreparation CanonicalPreparationCore.Completed
open CanonicalPreparationCreation CanonicalGradedSpatialSource
open CanonicalGradedSpatial (Localizer)
open GaussHistoryHilbert (physicalChart)
open MeasureTheory Set Filter
open scoped Topology ContDiff Distributions LinearPMap

open SaturationMonoid.Quantum.Forms

instance localized_complete (phi : Localizer) : CompleteSpace (zeroLocalizedSpace phi) :=
  (LinearMap.range (zeroCutoff phi).toLinearMap).isClosed_topologicalClosure.completeSpace_coe

theorem cutoff_seed_nonzero (phi : Localizer)
    (atSource : phi GaussHistoryHilbert.sourcePoint.val≠0) :
    zeroCutoff phi (zeroCore (complexCutoff phi))≠0 := by
  intro zero
  rw [zeroCutoff_core] at zero
  change scalarLp 0 (cutCore phi (complexCutoff phi))=0 at zero
  have ae : (fun z : physicalChart => cutCore phi (complexCutoff phi) z)=ᵐ[
      GaussHistoryHilbert.numberMeasure 0] (fun _ => (0 : ℂ)) :=
    (scalarLp_ae 0 (cutCore phi (complexCutoff phi))).symm.trans
      (zero ▸ Lp.coeFn_zero ℂ 2 (GaussHistoryHilbert.numberMeasure 0))
  have actual := congrFun (Measure.eq_of_ae_eq ae
    ((cutCore phi (complexCutoff phi)).continuous.comp continuous_subtype_val)
    continuous_const) GaussHistoryHilbert.sourcePoint
  change (phi GaussHistoryHilbert.sourcePoint.val : ℂ)*
    (phi GaussHistoryHilbert.sourcePoint.val : ℂ)=0 at actual
  exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr atSource)
    (Complex.ofReal_ne_zero.mpr atSource)) actual

/-- Nontriviality comes from the same cutoff at the actual source point;
the proof does not select this test as the near-state. -/
theorem localized_nontrivial (phi : Localizer)
    (atSource : phi GaussHistoryHilbert.sourcePoint.val≠0) :
    Nontrivial (zeroLocalizedSpace phi) := by
  let u : zeroLocalizedSpace phi :=
    ⟨zeroCutoff phi (zeroCore (complexCutoff phi)),
      (LinearMap.range (zeroCutoff phi).toLinearMap).le_topologicalClosure
        ⟨zeroCore (complexCutoff phi),rfl⟩⟩
  apply nontrivial_of_ne u 0
  intro equal
  exact cutoff_seed_nonzero phi atSource (congrArg Subtype.val equal)

theorem seedBase_native_charge (f : ScalarSpace) :
    CanonicalGradedCharge.chargeReader GaussComposite.nativeY (seedBase f)=-seedBase f := by
  refine scalarCore_dense.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [seedBase_core,CanonicalGradedCharge.chargeReader_core,
    GaussComposite.source_section_charge (seedSection g) g (seedSection_apply g),map_neg]

theorem created_native_charge (phi : Localizer) (f : zeroLocalizedSpace phi) :
    CanonicalGradedCharge.chargeReader GaussComposite.nativeY
      (prepared (zeroLocalizedProfile phi f))=-prepared (zeroLocalizedProfile phi f) := by
  rw [zeroLocalized_sourceCreated,sourceCreated_numberRaise]
  exact seedBase_native_charge _

theorem created_native_unit_read (phi : Localizer) (f : zeroLocalizedSpace phi) (unit : ‖f‖=1) :
    inner ℂ (prepared (zeroLocalizedProfile phi f))
      (CanonicalGradedCharge.chargeReader GaussComposite.nativeY
        (prepared (zeroLocalizedProfile phi f)))=-1 := by
  rw [created_native_charge,inner_neg_right,inner_self_eq_norm_sq_to_K,
    zeroLocalized_physical_norm,unit]
  norm_num

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem form_to_created_state (phi : Localizer)
    (atSource : phi GaussHistoryHilbert.sourcePoint.val≠0)
    (A : zeroLocalizedSpace phi →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set (zeroLocalizedSpace phi)))
    (R : zeroLocalizedSpace phi →L[ℂ] zeroLocalizedSpace phi) (selfAdjoint : IsSelfAdjoint R)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ x : (BoundedRemainder.operator A closed dense R).domain,
      ‖prepared (zeroLocalizedProfile phi x.val)‖=1 ∧
      ‖BoundedRemainder.operator A closed dense R x-(BoundedRemainder.energy A closed R : ℂ) • x.val‖<epsilon ∧
      prepared (zeroLocalizedProfile phi x.val)=
        sourceCreated (GaussHalfDensity.halfDensityEquiv 0 x.val.val) ∧
      (∀ y : A.domain, inner ℂ (BoundedRemainder.operator A closed dense R x) y.val=
        inner ℂ (A (BoundedRemainder.factorPoint A closed dense R x)) (A y)+
          inner ℂ x.val (R y.val)) ∧
      inner ℂ (prepared (zeroLocalizedProfile phi x.val))
        (CanonicalGradedCharge.chargeReader GaussComposite.nativeY
          (prepared (zeroLocalizedProfile phi x.val)))=-1 ∧
      (∀ (addition : Bool) (a s : Fin 2),
        ‖completedLeg addition a s (zeroLocalizedProfile phi x.val)‖≤
          legBound*localBound (outerCutoff phi)) ∧
      ∀ (p k : PhysicalMomentum) (q : SourceQuantumScalarChart.NativeLie)
        (cut : ℕ) (z w : ℂ) (hz : 0<z.im) (hw : 0<w.im)
        (left right : Bool) (a s b t : Fin 2),
        Tendsto (fun ts : ℝ×ℝ => CanonicalPreparedFrequency.timeRead p k q cut z w
          (ne_of_gt hz) (ne_of_gt hw) ts.1 ts.2 left right a s b t
          (zeroLocalizedProfile phi x.val) (zeroLocalizedProfile phi x.val)) (atTop×ˢatTop)
          (𝓝 (CanonicalPreparedFrequency.frequencyRead p k q cut z w
            (ne_of_gt hz) (ne_of_gt hw) left right a s b t
            (zeroLocalizedProfile phi x.val) (zeroLocalizedProfile phi x.val))) := by
  let := localized_nontrivial phi atSource
  obtain ⟨x,unit,near,pair⟩ := BoundedRemainder.form_preparation A closed dense R selfAdjoint epsilon positive
  refine ⟨x,zeroLocalized_unit phi x.val unit,near,
    zeroLocalized_sourceCreated phi x.val,pair,created_native_unit_read phi x.val unit,?_,?_⟩
  · intro addition a s
    simpa only [unit,mul_one] using zeroLocalized_eight_legs phi x.val addition a s
  · intro p k q cut z w hz hw left right a s b t
    exact CanonicalPreparedFrequency.prepared_causal_limit p k q cut z w hz hw
      left right a s b t _ _

end LowEnergy.CanonicalFormPreparation
