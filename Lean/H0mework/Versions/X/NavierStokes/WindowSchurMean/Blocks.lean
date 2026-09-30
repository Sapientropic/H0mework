import H0mework.Versions.X.NavierStokes.WindowSchurMean.Action

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanBlocks
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM)
open NativeWindowHistoryOseen (H action adjoint lift)
open NativeWindowHistoryMeanProjection (embed mean projection)
open NativeWindowHistoryMeanAction (frozen meanOperator creation)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private theorem add_smul_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g h : Lp E 2 averageMeasure) (a b c : ℝ → E) (scalar : ℝ)
    (fa : f=ᵐ[averageMeasure] a) (gb : g=ᵐ[averageMeasure] b) (hc : h=ᵐ[averageMeasure] c)
    (same : ∀ t,a t+b t=scalar • c t) : f+g=scalar • h := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add f g,Lp.coeFn_smul scalar h,fa,gb,hc] with t add smul first last third
  rw [add,Pi.add_apply,smul,Pi.smul_apply,first,last,third,same]

private theorem raw_sum (nu : Viscosity) (M : ℕ) (w : ComplexVorticityHilbertState) :
    frozenOperator (modes M) nu w+frozenOperator (modes M) nu (-w)=(2 : ℝ) • frozenOperator (modes M) nu 0 := by
  rw [NativeAffineTransport.frozen_split (modes M) nu w,NativeAffineTransport.frozen_split (modes M) nu (-w),map_neg]
  module

def diffusion (nu : Viscosity) (M : ℕ) : wholePhysical →L[ℝ] wholePhysical := lift M (frozen nu M 0)

theorem fiber_sum (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    NativeWindowHistoryOseen.forwardFiber seed M time v+NativeWindowHistoryOseen.dualFiber seed M time v=
      (2 : ℝ) • diffusion nu M v := by
  let r:=restrictCLM (modes M) (modes_zero M) (modes_closed M) v
  change includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.forward seed M time r)+
    includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.dual seed M time r)=
      (2 : ℝ) • includeCLM (modes M) (modes_closed M) (frozen nu M 0 r)
  rw [← map_add,← map_smul]
  apply congrArg (includeCLM (modes M) (modes_closed M))
  apply Subtype.ext
  change frozenOperator (modes M) nu (NativeWindowTraceAdjoint.advector seed M time) r.1+
    frozenOperator (modes M) nu (-NativeWindowTraceAdjoint.advector seed M time) r.1=
      (2 : ℝ) • frozenOperator (modes M) nu (NativeWindowTraceAdjoint.curlMap M 0) r.1
  rw [map_zero]
  exact congrArg (fun A : ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState => A r.1) (raw_sum nu M _)

theorem action_sum (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    action seed M time v+adjoint seed M time v=(2 : ℝ) • (diffusion nu M).compLpL 2 averageMeasure v := by
  simpa only [] using! add_smul_ae (E := wholePhysical) (action seed M time v) (adjoint seed M time v)
    ((diffusion nu M).compLpL 2 averageMeasure v) _ _ _ (2 : ℝ)
    (NativeWindowHistoryOseen.action_ae seed M time v) (NativeWindowHistoryOseen.adjoint_ae seed M time v)
    ((diffusion nu M).coeFn_compLpL v) (fun lag => fiber_sum seed M (time-lag) (v lag))

def annihilation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] wholePhysical :=
  mean.comp ((action seed M time).comp NativeWindowHistoryMeanProjection.residual)

def bath (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  NativeWindowHistoryMeanProjection.residual.comp ((action seed M time).comp NativeWindowHistoryMeanProjection.residual)

theorem creation_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u : wholePhysical) (v : H) :
    inner ℝ (creation seed M time u) v=inner ℝ (action seed M time (embed u)) (NativeWindowHistoryMeanProjection.residual v) :=
  NativeWindowHistoryMeanProjection.residual_symmetric _ _

private theorem diffusion_cross (nu : Viscosity) (M : ℕ) (u : wholePhysical) (v : H) :
    inner ℝ (embed u) ((2 : ℝ) • (diffusion nu M).compLpL 2 averageMeasure (NativeWindowHistoryMeanProjection.residual v))=0 := by
  rw [real_inner_smul_right (embed u),← NativeWindowHistoryMeanProjection.residual_comp,
    NativeWindowHistoryMeanProjection.embed_orthogonal,mul_zero]

private theorem adjoint_cross {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A D : E →L[ℝ] E) (u v w : E) (dual : inner ℝ (A u) v=inner ℝ u (D v))
    (sum : A v+D v=w) (perpendicular : inner ℝ u w=0) : inner ℝ u (A v)+inner ℝ (A u) v=0 := by
  rw [dual,← inner_add_right,sum,perpendicular]

theorem annihilation_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u : wholePhysical) (v : H) :
    inner ℝ u (annihilation seed M time v)=inner ℝ (embed u) (action seed M time (NativeWindowHistoryMeanProjection.residual v)) := by
  simpa only [annihilation,ContinuousLinearMap.comp_apply] using!
    (NativeWindowHistoryMeanProjection.embed_pairing u (action seed M time (NativeWindowHistoryMeanProjection.residual v))).symm

private theorem source_cross (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u : wholePhysical) (v : H) :
    inner ℝ (embed u) (action seed M time (NativeWindowHistoryMeanProjection.residual v))+inner ℝ (action seed M time (embed u)) (NativeWindowHistoryMeanProjection.residual v)=0 := by
  simpa only [] using! adjoint_cross (E := H) (action seed M time) (adjoint seed M time) (embed u) (NativeWindowHistoryMeanProjection.residual v)
    ((2 : ℝ) • (diffusion nu M).compLpL 2 averageMeasure (NativeWindowHistoryMeanProjection.residual v))
    (NativeWindowHistoryOseen.action_adjoint seed M time (embed u) (NativeWindowHistoryMeanProjection.residual v))
    (action_sum seed M time (NativeWindowHistoryMeanProjection.residual v)) (diffusion_cross nu M u v)

theorem coupling_green (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u : wholePhysical) (v : H) :
    inner ℝ u (annihilation seed M time v)+inner ℝ (creation seed M time u) v=0 := by
  exact (congrArg₂ (fun x y : ℝ => x+y) (annihilation_pairing seed M time u v)
    (creation_pairing seed M time u v)).trans (source_cross seed M time u v)

theorem annihilation_adjoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    annihilation seed M time=-(ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := wholePhysical) (F := H) (creation seed M time)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  have same := coupling_green seed M time u v
  rw [neg_apply,inner_neg_right,ContinuousLinearMap.adjoint_inner_right (𝕜 := ℝ) (E := wholePhysical) (F := H)]
  linarith only [same]

private theorem compressed_sign {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q A : E →L[ℝ] E) (symmetric : ∀ u v,inner ℝ (Q u) v=inner ℝ u (Q v))
    (dissipative : ∀ v,inner ℝ v (A v) ≤ 0) (v : E) : inner ℝ v (Q (A (Q v))) ≤ 0 :=
  (symmetric v (A (Q v))).symm.trans_le (dissipative (Q v))

theorem bath_dissipative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    inner ℝ v (bath seed M time v) ≤ 0 := by
  simpa only [bath,ContinuousLinearMap.comp_apply] using!
    compressed_sign (E := H) NativeWindowHistoryMeanProjection.residual (action seed M time)
      NativeWindowHistoryMeanProjection.residual_symmetric (NativeWindowHistoryOseen.action_dissipative seed M time) v

private theorem mapped_split {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (A P Q : E →L[ℝ] E)
    (v : E) (sum : P v+Q v=v) : L (A v)=L (A (P v))+L (A (Q v)) := by
  conv_lhs => rw [← sum]
  rw [map_add,map_add]

theorem mean_action_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    mean (action seed M time v)=meanOperator seed M time (mean v)+annihilation seed M time v := by
  have same := mapped_split (E := H) (F := wholePhysical) mean (action seed M time) projection NativeWindowHistoryMeanProjection.residual v
    (NativeWindowHistoryMeanProjection.split v)
  exact same.trans (congrArg (fun w : wholePhysical => w+annihilation seed M time v)
    (NativeWindowHistoryMeanAction.mean_action seed M time (mean v)))

theorem residual_action_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    NativeWindowHistoryMeanProjection.residual (action seed M time v)=creation seed M time (mean v)+bath seed M time v := by
  simpa only [creation,bath,ContinuousLinearMap.comp_apply,NativeWindowHistoryMeanProjection.projection] using!
    mapped_split (E := H) (F := H) NativeWindowHistoryMeanProjection.residual (action seed M time) projection
      NativeWindowHistoryMeanProjection.residual v (NativeWindowHistoryMeanProjection.split v)

private theorem source_read {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : H →L[ℝ] E) (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (fun t => L (NativeWindowTraceWholeHistory.finiteHistory seed t M))
      (L (action seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M))+
        L (NativeWindowHistoryOseen.forcingHistory seed M time)) time := by
  have actual := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := H) (E := E) time L.hasFDerivAt
    (NativeWindowHistoryOseen.source_hasDerivAt seed M time)
  simpa only [Function.comp_def,map_add] using! actual

theorem source_mean_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (fun t => mean (NativeWindowTraceWholeHistory.finiteHistory seed t M))
      (meanOperator seed M time (mean (NativeWindowTraceWholeHistory.finiteHistory seed time M))+
        annihilation seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M)+
          mean (NativeWindowHistoryOseen.forcingHistory seed M time)) time := by
  have actual := source_read (E := wholePhysical) mean seed M time
  have rate := congrArg (fun w : wholePhysical => w+mean (NativeWindowHistoryOseen.forcingHistory seed M time))
    (mean_action_split seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M))
  exact rate ▸ actual

theorem source_residual_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (fun t => NativeWindowHistoryMeanProjection.residual (NativeWindowTraceWholeHistory.finiteHistory seed t M))
      (creation seed M time (mean (NativeWindowTraceWholeHistory.finiteHistory seed time M))+
        bath seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M)+
          NativeWindowHistoryMeanProjection.residual (NativeWindowHistoryOseen.forcingHistory seed M time)) time := by
  have actual := source_read (E := H) NativeWindowHistoryMeanProjection.residual seed M time
  have rate := congrArg (fun w : H => w+NativeWindowHistoryMeanProjection.residual (NativeWindowHistoryOseen.forcingHistory seed M time))
    (residual_action_split seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M))
  exact rate ▸ actual

theorem source_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    NativeWindowHistoryMeanProjection.residual (NativeWindowTraceWholeHistory.finiteHistory seed (-2) M)=0 := by
  have same := NativeWindowHistoryMeanProjection.residual_comp (NativeWindowTraceWholeHistory.projection M)
    (NativeWindowTraceWholeHistory.history seed (-2))
  have zero := congrArg ((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure)
    (NativeWindowHistoryMeanProjection.preparation_residual seed)
  simpa only [NativeWindowTraceWholeHistory.finiteHistory] using! same.trans
    (zero.trans (((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure).map_zero))

private theorem weighted_annihilation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (T : wholePhysical →L[ℝ] wholePhysical) (u : wholePhysical) (v : H) :
    inner ℝ (embed u) (T.compLpL 2 averageMeasure (action seed M time (NativeWindowHistoryMeanProjection.residual v)))=
      inner ℝ (T.adjoint u) (annihilation seed M time v) := by
  rw [NativeWindowHistoryMeanProjection.embed_pairing,NativeWindowHistoryMeanProjection.mean_comp]
  exact (ContinuousLinearMap.adjoint_inner_left T (annihilation seed M time v) u).symm

private theorem weighted_creation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (T : wholePhysical →L[ℝ] wholePhysical) (u : wholePhysical) (v : H) :
    inner ℝ (NativeWindowHistoryMeanProjection.residual v) (T.compLpL 2 averageMeasure (action seed M time (embed u)))=
      inner ℝ v (T.compLpL 2 averageMeasure (creation seed M time u)) := by
  have one := NativeWindowHistoryMeanProjection.residual_symmetric v
    (T.compLpL 2 averageMeasure (action seed M time (embed u)))
  have two := congrArg (fun w : H => inner ℝ v w)
    (NativeWindowHistoryMeanProjection.residual_comp T (action seed M time (embed u)))
  simpa only [creation,ContinuousLinearMap.comp_apply] using! one.trans two

theorem weighted_coupling (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (T : wholePhysical →L[ℝ] wholePhysical) (u : wholePhysical) (v : H) :
    inner ℝ (embed u) (T.compLpL 2 averageMeasure (action seed M time (NativeWindowHistoryMeanProjection.residual v)))+
      inner ℝ (NativeWindowHistoryMeanProjection.residual v) (T.compLpL 2 averageMeasure (action seed M time (embed u)))=
        inner ℝ v (T.compLpL 2 averageMeasure (creation seed M time u)-creation seed M time (T.adjoint u)) := by
  have one := weighted_annihilation seed M time T u v
  have two := weighted_creation seed M time T u v
  have cancel := coupling_green seed M time (T.adjoint u) v
  have difference := inner_sub_right (𝕜 := ℝ) v (T.compLpL 2 averageMeasure (creation seed M time u))
    (creation seed M time (T.adjoint u))
  have symmetric := real_inner_comm (F := H) v (creation seed M time (T.adjoint u))
  linarith only [one,two,cancel,difference,symmetric]

theorem metric_coupling (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector) (R : ℕ)
    (u : wholePhysical) (v : H) :
    inner ℝ (embed u) (NativeWindowTraceWholeHistory.metricAction seed frame M F R
      (action seed M time (NativeWindowHistoryMeanProjection.residual v)))+
      inner ℝ (NativeWindowHistoryMeanProjection.residual v) (NativeWindowTraceWholeHistory.metricAction seed frame M F R
        (action seed M time (embed u)))=
      inner ℝ v (NativeWindowTraceWholeHistory.metricAction seed frame M F R (creation seed M time u)-
        creation seed M time ((NativeWindowTraceWholeHistory.metric seed frame M F R).adjoint u)) :=
  weighted_coupling seed M time (NativeWindowTraceWholeHistory.metric seed frame M F R) u v

theorem operator_compression (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    meanOperator seed M time=mean.comp ((action seed M time).comp embed) := by
  apply ContinuousLinearMap.ext
  intro v
  exact (NativeWindowHistoryMeanAction.mean_action seed M time v).symm

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem creation_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    creation seed M (step.2.clockAdvance+time)=creation step.1 M time :=
  congrArg (fun A : H →L[ℝ] H => NativeWindowHistoryMeanProjection.residual.comp (A.comp embed))
    (congrArg Prod.fst (NativeWindowHistoryOseen.whole_next seed M step generated time nonnegative))

theorem blocks_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    (meanOperator seed M (step.2.clockAdvance+time),creation seed M (step.2.clockAdvance+time),
      annihilation seed M (step.2.clockAdvance+time),bath seed M (step.2.clockAdvance+time))=
    (meanOperator step.1 M time,creation step.1 M time,annihilation step.1 M time,bath step.1 M time) := by
  have same : action seed M (step.2.clockAdvance+time)=action step.1 M time :=
    congrArg Prod.fst (NativeWindowHistoryOseen.whole_next seed M step generated time nonnegative)
  simp only [operator_compression,creation,annihilation,bath,same]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanBlocks
