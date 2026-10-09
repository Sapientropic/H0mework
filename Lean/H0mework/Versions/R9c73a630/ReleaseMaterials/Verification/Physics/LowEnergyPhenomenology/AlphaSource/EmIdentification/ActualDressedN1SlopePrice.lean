import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedN1TimePrice

set_option autoImplicit false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedN1Price
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse ActualDressedNumberZero ActualDressedNumberField
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalN1WardCollapse
open ActualDressedPreparedPrice
open scoped Topology BigOperators Interval
attribute [local irreducible] sourceN1Projection physicalTime timeSlope jointGenerator jointCurrent
  actualC actualA SourceGraph.prepared
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℝ (E→L[ℂ]E):=NormedAlgebra.restrictScalars ℝ ℂ _

private theorem time_continuous (G : E→L[ℂ]E) : Continuous (SourceFiniteUnitary.time G) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • G) t).continuousAt)

private theorem variation_apply (G B : E→L[ℂ]E) (t : ℝ) (v : E) :
    CanonicalGradedVariation.variation G B t v=∫ s in (0:ℝ)..t,
      SourceFiniteUnitary.time G s ((-Complex.I) • (B (SourceFiniteUnitary.time G (t-s) v))) := by
  have ct:=time_continuous G
  have hi : IntervalIntegrable (fun s : ℝ => SourceFiniteUnitary.time G s * ((-Complex.I) • B) *
      SourceFiniteUnitary.time G (t-s)) MeasureTheory.volume 0 t :=
    ((ct.mul continuous_const).mul (ct.comp (continuous_const.sub continuous_id))).intervalIntegrable 0 t
  have h:=ContinuousLinearMap.intervalIntegral_apply hi v
  simpa only [CanonicalGradedVariation.variation,CanonicalGradedVariation.variationBetween,
    zero_smul,add_zero,mul_apply_eq_comp,smul_apply] using h

private theorem variation_integrand_continuous (G B : E→L[ℂ]E) (t : ℝ) (v : E) :
    Continuous (fun s : ℝ => SourceFiniteUnitary.time G s
      ((-Complex.I) • (B (SourceFiniteUnitary.time G (t-s) v)))) :=
  (time_continuous G).clm_apply ((B.continuous.comp
    (((time_continuous G).comp (continuous_const.sub continuous_id)).clm_apply continuous_const)).const_smul (-Complex.I))

private theorem restricted_variation_range (G B P : E→L[ℂ]E)
    (timeRange : ∀s x,P x=x→P (SourceFiniteUnitary.time G s x)=SourceFiniteUnitary.time G s x)
    (currentRange : ∀x,P x=x→P (B x)=B x) (t : ℝ) (v : E) (sector : P v=v) :
    P (CanonicalGradedVariation.variation G B t v)=CanonicalGradedVariation.variation G B t v := by
  let f:=fun s : ℝ => SourceFiniteUnitary.time G s ((-Complex.I) • (B (SourceFiniteUnitary.time G (t-s) v)))
  have hi : IntervalIntegrable f MeasureTheory.volume 0 t:=
    (variation_integrand_continuous G B t v).intervalIntegrable 0 t
  calc
    _=P (∫ s in (0:ℝ)..t,f s):=congrArg P (variation_apply G B t v)
    _=∫ s in (0:ℝ)..t,P (f s):=(P.intervalIntegral_comp_comm hi).symm
    _=∫ s in (0:ℝ)..t,f s:=by
      apply intervalIntegral.integral_congr
      intro s _
      apply timeRange
      rw [map_smul,currentRange _ (timeRange (t-s) v sector)]
    _=CanonicalGradedVariation.variation G B t v:=(variation_apply G B t v).symm

private theorem interval_times (t s : ℝ) (hs : s  ∈  Ι (0:ℝ) t) : |s|  ≤  |t| ∧ |t-s|  ≤  |t| := by
  by_cases ht : 0  ≤  t
  · rw [Set.uIoc_of_le ht] at hs
    rw [abs_of_pos hs.1,abs_of_nonneg ht,abs_of_nonneg (sub_nonneg.mpr hs.2)]
    constructor
    · exact hs.2
    · linarith [hs.1]
  · have ht' : t  ≤  0:=le_of_not_ge ht
    rw [Set.uIoc_of_ge ht'] at hs
    rw [abs_of_nonpos hs.2,abs_of_nonpos ht',abs_of_nonpos (sub_nonpos.mpr (le_of_lt hs.1))]
    constructor <;> linarith [hs.1,hs.2]


private theorem restricted_variation_price (G B P : E→L[ℂ]E)
    (timeRange : ∀s x,P x=x→P (SourceFiniteUnitary.time G s x)=SourceFiniteUnitary.time G s x)
    (currentRange : ∀x,P x=x→P (B x)=B x) (t M : ℝ) (positive : 0 ≤ M)
    (timePrice : ∀s,|s| ≤ |t|→∀x,P x=x→‖SourceFiniteUnitary.time G s x‖ ≤ M*‖x‖)
    (v : E) (sector : P v=v) :
    ‖CanonicalGradedVariation.variation G B t v‖ ≤ |t| *‖B‖*M^2*‖v‖ := by
  have bound (s : ℝ) (hs : s ∈ Ι (0:ℝ) t) :
      ‖SourceFiniteUnitary.time G s ((-Complex.I) • (B (SourceFiniteUnitary.time G (t-s) v)))‖ ≤
        M^2*‖B‖*‖v‖ := by
    have st:=interval_times t s hs
    have inner:=timePrice (t-s) st.2 v sector
    have sn : P ((-Complex.I) • (B (SourceFiniteUnitary.time G (t-s) v)))=
        (-Complex.I) • (B (SourceFiniteUnitary.time G (t-s) v)) := by
      rw [map_smul,currentRange _ (timeRange (t-s) v sector)]
    have outer:=timePrice s st.1 _ sn
    rw [norm_smul,norm_neg,Complex.norm_I,one_mul] at outer
    calc
      _ ≤ M*‖B (SourceFiniteUnitary.time G (t-s) v)‖:=outer
      _ ≤ M*(‖B‖*(M*‖v‖)):=mul_le_mul_of_nonneg_left
        ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left inner (norm_nonneg B))) positive
      _=_:=by ring
  have estimate:=intervalIntegral.norm_integral_le_of_norm_le_const bound
  calc
    _=‖∫ s in (0:ℝ)..t,SourceFiniteUnitary.time G s
        ((-Complex.I) • (B (SourceFiniteUnitary.time G (t-s) v)))‖:=congrArg norm (variation_apply G B t v)
    _ ≤ _:=estimate.trans_eq (by rw [sub_zero]; ring)
end Generic

private theorem actual_time_N1 (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (v : H) (sector : sourceN1Projection v=v) :
    sourceN1Projection (physicalTime p F t 0 v)=physicalTime p F t 0 v := by
  have source:=congrArg (fun A : H→L[ℂ]H  =>  A v) (actual_joint_time_number_one_range p F t 0)
  simpa only [mul_apply_eq_comp,sector] using source

private theorem actual_current_N1 (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (v : H) (sector : sourceN1Projection v=v) :
    sourceN1Projection (jointCurrent p F 0 0 force v)=jointCurrent p F 0 0 force v := by
  have source:=congrArg (fun A : H→L[ℂ]H  =>  A v) (actual_joint_current_number_one p F 0 force)
  simpa only [mul_apply_eq_comp,sector] using source

theorem actual_timeSlope_N1_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t : ℝ) (v : H) (sector : sourceN1Projection v=v) :
    sourceN1Projection (timeSlope force p F t v)=timeSlope force p F t v := by
  have timerange : ∀s x,sourceN1Projection x=x→
      sourceN1Projection (SourceFiniteUnitary.time (jointGenerator p F 0 0) s x)=
        SourceFiniteUnitary.time (jointGenerator p F 0 0) s x := by
    intro s x hx
    simpa only [physicalTime] using actual_time_N1 p F s x hx
  simpa only [timeSlope] using restricted_variation_range (jointGenerator p F 0 0)
    (jointCurrent p F 0 0 force) sourceN1Projection timerange (actual_current_N1 p F force) t v sector

theorem actual_timeSlope_N1_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t : ℝ) (v : H) (sector : sourceN1Projection v=v) :
    ‖timeSlope force p F t v‖ ≤ |t| *‖jointCurrent p F 0 0 force‖*
      (occupationPrice 1 ‖actualA p F‖ |t|)^2*‖v‖ := by
  have timerange : ∀s x,sourceN1Projection x=x→
      sourceN1Projection (SourceFiniteUnitary.time (jointGenerator p F 0 0) s x)=
        SourceFiniteUnitary.time (jointGenerator p F 0 0) s x := by
    intro s x hx
    simpa only [physicalTime] using actual_time_N1 p F s x hx
  have price : ∀s,|s| ≤ |t|→∀x,sourceN1Projection x=x→
      ‖SourceFiniteUnitary.time (jointGenerator p F 0 0) s x‖ ≤ occupationPrice 1 ‖actualA p F‖ |t| *‖x‖ := by
    intro s hs x hx
    have h:=(actual_time_N1_price p F s x hx).trans
      (mul_le_mul_of_nonneg_right (occupationPrice_mono 1 ‖actualA p F‖ |s| |t|
        (norm_nonneg _) (abs_nonneg s) hs) (norm_nonneg x))
    simpa only [physicalTime] using h
  simpa only [timeSlope] using restricted_variation_price (jointGenerator p F 0 0)
    (jointCurrent p F 0 0 force) sourceN1Projection timerange (actual_current_N1 p F force) t
    (occupationPrice 1 ‖actualA p F‖ |t|) (occupationPrice_nonneg 1 _ _ (norm_nonneg _) (abs_nonneg t))
    price v sector

theorem actual_background_timeSlope_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t : ℝ) (profile : SourceGraph.Profile) :
    ‖timeSlope force p F t (SourceGraph.prepared profile)‖ ≤
      |t| *‖jointCurrent p F 0 0 force‖*(occupationPrice 1 ‖actualA p F‖ |t|)^2*‖SourceGraph.prepared profile‖ :=
  actual_timeSlope_N1_price p F force t (SourceGraph.prepared profile) (actual_background_number_one profile)

end LowEnergy.GaussComposite.ActualDressedN1Price
