import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatial
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.Response
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianCommutator
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.ResidualEnergy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianViscous
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H action forcingHistory rateHistory)
open NativeWindowTraceWholeHistory (gradient finiteHistory)
open NativeWindowHistorySchurCompletion (completion commonForce)
open NativeWindowHistorySchurTemporalControl (energy temporalResponse temporalBudget)
open NativeWindowHistoryMeanProjection (embed)
open NativeWindowHistorySchurAdvectorAction (xAction wAction)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowHistoryJacobianControl (form heat jacobian correction)
open NativeWindowHistoryJacobianSpatial (spatial form_skew spatial_square energy_gradient mass_gradient)
noncomputable section
variable {nu : Viscosity}

def bracket (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) : H →L[ℝ] H :=
  (spatial M j).comp (jacobian seed M time)-(jacobian seed M time).comp (spatial M j)

theorem bracket_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) (v : H) :
    bracket seed M time j v= -NativeWindowHistoryDynamicHistory.kernelAction seed M time
      (NativeWindowHistoryJacobianCommutator.advectorDerivative seed M j time (correction seed M time v))-
        NativeWindowHistoryDynamicHistory.kernelAction seed M time
          (NativeWindowHistoryJacobianCommutator.transposeDerivative seed M j time v) :=
  NativeWindowHistoryJacobianCommutator.jacobian_commutator seed M j time v

def diagonal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) : ℝ :=
  -2*nu.coeff*(∑j : Coordinate,form nu M (spatial M j v) (jacobian seed M time (spatial M j v)))

def commutatorWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) : ℝ :=
  -2*nu.coeff*(∑j : Coordinate,form nu M v (bracket seed M time j (spatial M j v)))

private theorem viscous_green {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G L J : E →L[ℝ] E) (D : Coordinate → E →L[ℝ] E)
    (skew : ∀j u v,inner ℝ u (G (D j v))= -inner ℝ (D j u) (G v))
    (square : ∀v,(∑j,D j (D j v))= -L v) (v : E) :
    inner ℝ v (G (J (L v)))=(∑j,inner ℝ (D j v) (G (J (D j v))))+
      ∑j,inner ℝ v (G (((D j).comp J-J.comp (D j)) (D j v))) := by
  have split:L v= -(∑j,D j (D j v)) := by simpa only [neg_neg] using (congrArg Neg.neg (square v)).symm
  rw [split,map_neg,map_neg,inner_neg_right,map_sum,map_sum,inner_sum,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub,inner_sub_right]
  linarith only [skew j v (J (D j v))]

theorem viscous_identity (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    -2*nu.coeff*form nu M v (jacobian seed M time (laplacianAction nu M v))=
      diagonal seed M time v+commutatorWork seed M time v := by
  have source:=viscous_green (E := H) (heat nu M) (laplacianAction nu M) (jacobian seed M time) (spatial M)
    (form_skew nu M) (spatial_square nu M) v
  have actual:=congrArg (fun x : ℝ => -2*nu.coeff*x) source
  simpa only [form,diagonal,commutatorWork,bracket,mul_add] using! actual

theorem source_diagonal (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      diagonal seed M time (temporalResponse seed M time)≤
        -nu.coeff^2*‖laplacianAction nu M (temporalResponse seed M time)‖^2+C := by
  obtain ⟨low,B,B0,source⟩:=NativeWindowHistoryJacobianControl.source_coercivity seed horizon nonnegative (1/2) (by norm_num)
  refine ⟨low,2*B*max 0 (temporalBudget seed horizon),by positivity,fun M above time inside => ?_⟩
  let w:=temporalResponse seed M time
  have paid:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ => source M above time inside (spatial M j w)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,energy_gradient,mass_gradient nu] at paid
  have scaled:=mul_le_mul_of_nonneg_left paid (show 0≤2*nu.coeff from by positivity [nu.coeff_pos])
  have initial:=NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside
  have mass:=sq_nonneg ‖w‖
  have grad0:=NativeWindowHistoryMeanGradient.gradient_nonnegative seed M w
  have gradientBound:nu.coeff*gradient M w ≤ max 0 (temporalBudget seed horizon) := by
    change energy nu M w≤_ at initial
    unfold energy at initial
    linarith only [initial,mass,le_max_right 0 (temporalBudget seed horizon)]
  have extra:=mul_le_mul_of_nonneg_left gradientBound (show 0≤2*B from by positivity)
  change -2*nu.coeff*(∑j : Coordinate,form nu M (spatial M j w) (jacobian seed M time (spatial M j w)))≤_
  nlinarith only [scaled,extra,mul_nonneg nu.coeff_pos.le grad0]

def reaction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  xAction seed M time (temporalResponse seed M time)+wAction seed M time (temporalResponse seed M time)+
    completion seed M time-embed (commonForce seed M time)+forcingHistory seed M time

private theorem source_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A L Nx Nw : E →L[ℝ] E) (a : ℝ) (h x w c f : E) (split : h=x+w)
    (resolved : x-A x=c) (acted : A w=(-a) • L w+Nx w+Nw w) :
    A h+f=(-a) • L w+(Nx w+Nw w+x-c+f) := by
  rw [split,map_add,acted,← resolved]
  abel

theorem rate_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    rateHistory seed M time=(-nu.coeff) • laplacianAction nu M (temporalResponse seed M time)+reaction seed M time := by
  have actual:=congrArg (fun A : H →L[ℝ] H => A (temporalResponse seed M time))
    (NativeWindowHistorySchurAdvectorAction.source_action_split seed M time)
  have heatRead:=NativeWindowHistorySchurAdvectorEnergy.diffusion_history nu M (temporalResponse seed M time)
  change action seed M time (temporalResponse seed M time)=
    ((NativeWindowHistoryMeanBlocks.diffusion nu M).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure
      (temporalResponse seed M time)+xAction seed M time (temporalResponse seed M time))+wAction seed M time (temporalResponse seed M time) at actual
  have acted:=actual.trans (congrArg (fun x : H => (x+xAction seed M time (temporalResponse seed M time))+
    wAction seed M time (temporalResponse seed M time)) heatRead)
  exact (NativeWindowHistoryOseen.source_equation seed M time).trans
    (source_split (E := H) (action seed M time) (laplacianAction nu M) (xAction seed M time) (wAction seed M time)
      nu.coeff (finiteHistory seed time M) (completion seed M time) (temporalResponse seed M time)
      (embed (commonForce seed M time)) (forcingHistory seed M time)
      (NativeWindowHistorySchurCompletion.source_split seed M time)
      (NativeWindowHistorySchurCompletion.completion_equation seed M time) acted)

def reactionWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  2*form nu M (temporalResponse seed M time) (jacobian seed M time (reaction seed M time))

private theorem adjoint_read {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (G J : E →L[ℝ] E) (symmetric : ∀u v,inner ℝ u (G v)=inner ℝ v (G u)) (q v : E) :
    2*inner ℝ q (J.adjoint (G v))=2*inner ℝ v (G (J q)) := by
  rw [ContinuousLinearMap.adjoint_inner_right,symmetric]

theorem joint_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryDynamicEnergy.jointWork seed M time=
      2*form nu M (temporalResponse seed M time) (jacobian seed M time (rateHistory seed M time)) := by
  have read:=congrArg (fun v : H => 2*inner ℝ (rateHistory seed M time) v)
    (NativeWindowHistoryJacobianControl.source_test seed M time)
  apply read.symm.trans
  simpa only [form] using! adjoint_read (E := H) (heat nu M) (jacobian seed M time)
    (NativeWindowHistoryJacobianControl.form_symmetric nu M) (rateHistory seed M time) (temporalResponse seed M time)

private theorem split_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G J L : E →L[ℝ] E) (v r : E) (a : ℝ) :
    2*inner ℝ v (G (J ((-a) • L v+r)))= -2*a*inner ℝ v (G (J (L v)))+2*inner ℝ v (G (J r)) := by
  simp only [map_add,map_smul,inner_add_right,real_inner_smul_right]
  ring

theorem joint_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryDynamicEnergy.jointWork seed M time=
      diagonal seed M time (temporalResponse seed M time)+commutatorWork seed M time (temporalResponse seed M time)+
        reactionWork seed M time := by
  have source:=(joint_read seed M time).trans (congrArg (fun q : H => 2*form nu M (temporalResponse seed M time)
    (jacobian seed M time q)) (rate_split seed M time))
  have split:=split_pair (E := H) (heat nu M) (jacobian seed M time) (laplacianAction nu M)
    (temporalResponse seed M time) (reaction seed M time) nu.coeff
  exact source.trans (split.trans (congrArg (fun x : ℝ => x+reactionWork seed M time)
    (viscous_identity seed M time (temporalResponse seed M time))))

private theorem gate (a j d c r W H B C nu epsilon : ℝ)
    (diagonalPaid : d≤ -nu^2*W+B) (source : a-j≤epsilon*H+C) (original : j=d+c+r) :
    a≤ -nu^2*W+epsilon*H+(B+C)+c+r := by linarith only [diagonalPaid,source,original]

theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      NativeWindowHistoryDynamicEnergy.sourceRate seed M time≤
        -nu.coeff^2*‖laplacianAction nu M (temporalResponse seed M time)‖^2+
          epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C+
            commutatorWork seed M time (temporalResponse seed M time)+reactionWork seed M time := by
  obtain ⟨low,B,B0,diagonalPaid⟩:=source_diagonal seed horizon nonnegative
  have sourceBudget:=NativeWindowHistoryDynamicEnergy.source_generator (nu := nu) seed horizon epsilon positive
  obtain ⟨C,C0,source⟩:=sourceBudget
  refine ⟨low,B+C,add_nonneg B0 C0,fun M above time inside => ?_⟩
  have first:=diagonalPaid M above time inside
  have last:=(le_abs_self _).trans (source M time inside)
  have original:=joint_split seed M time
  exact gate _ _ _ _ _ _ _ B C nu.coeff epsilon first last original

theorem bare_form (nu : Viscosity) (M : ℕ) (h a : H) :
    NativeWindowHistorySchurBarePairing.pairing nu.coeff h (laplacianAction nu M h) a=2*form nu M h a := by
  have read:form nu M h a=inner ℝ h a+nu.coeff*inner ℝ (laplacianAction nu M h) a :=
    (NativeWindowHistoryJacobianControl.form_symmetric nu M h a).trans
      ((NativeWindowHistoryJacobianControl.form_split nu M a h).trans
        (congrArg₂ (fun x y : ℝ => x+nu.coeff*y) (real_inner_comm h a) (real_inner_comm (laplacianAction nu M h) a)))
  have same:=congrArg (2*·) read
  change 2*inner ℝ h a+2*nu.coeff*inner ℝ (laplacianAction nu M h) a=2*form nu M h a
  linarith only [same]

def signedTransfer (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  2*form nu M (completion seed M time) (rateHistory seed M time)+
    2*form nu M (temporalResponse seed M time) (correction seed M time (rateHistory seed M time))

private theorem add_force {E : Type*} [AddCommGroup E] (a l c w f : E) (source : a+l=c+w) :
    (a+f)+l=c+(w+f) := by
  calc
    _=(a+l)+f := by abel
    _=(c+w)+f := congrArg (fun x : E => x+f) source
    _=_ := by abel

private theorem energy_bridge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G R : E →L[ℝ] E) (h x w q l c g : E) (a : ℝ) (split : h=x+w) (acted : q+a • l=c+g) :
    2*inner ℝ h (G g)=2*inner ℝ w (G ((ContinuousLinearMap.id ℝ E-R) q))+
      2*a*inner ℝ h (G l)+(2*inner ℝ x (G q)+2*inner ℝ w (G (R q)))-2*inner ℝ h (G c) := by
  have gRead:g=q+a • l-c := by
    rw [acted]
    abel
  rw [gRead,split]
  simp only [sub_apply,ContinuousLinearMap.id_apply,map_sub,map_add,map_smul,inner_add_left,
    inner_sub_right,inner_add_right,real_inner_smul_right]
  ring

theorem residual_work_bridge (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistorySchurResidualEnergy.residualWork seed M time=
      NativeWindowHistoryDynamicEnergy.jointWork seed M time+
        2*nu.coeff*gradient M (finiteHistory seed time M)+
        2*nu.coeff^2*‖laplacianAction nu M (finiteHistory seed time M)‖^2+
        signedTransfer seed M time-NativeWindowHistorySchurResidualEnergy.controlledWork seed M time := by
  let h:=finiteHistory seed time M
  let w:=temporalResponse seed M time
  let c:=NativeWindowHistorySchurMixedAction.controlledInput seed M time
  let g:=wAction seed M time w+forcingHistory seed M time
  have raw:=NativeWindowHistorySchurMixedAction.source_action seed M time
  have forced:=add_force (E := H) (action seed M time h) (nu.coeff • laplacianAction nu M h)
    c (wAction seed M time w) (forcingHistory seed M time) raw
  have acted:rateHistory seed M time+nu.coeff • laplacianAction nu M h=c+g :=
    (congrArg (fun v : H => v+nu.coeff • laplacianAction nu M h) (NativeWindowHistoryOseen.source_equation seed M time)).trans forced
  have bridge:=energy_bridge (E := H) (heat nu M) (correction seed M time) h (completion seed M time) w
    (rateHistory seed M time) (laplacianAction nu M h) c g nu.coeff
    (NativeWindowHistorySchurCompletion.source_split seed M time) acted
  change 2*form nu M h g=2*form nu M w (jacobian seed M time (rateHistory seed M time))+
    2*nu.coeff*form nu M h (laplacianAction nu M h)+signedTransfer seed M time-2*form nu M h c at bridge
  have heatCost:form nu M h (laplacianAction nu M h)=gradient M h+nu.coeff*‖laplacianAction nu M h‖^2 :=
    (NativeWindowHistoryJacobianSpatial.form_gradient nu M h h).symm.trans
      ((Finset.sum_congr rfl fun j _ => NativeWindowHistoryJacobianControl.form_self nu M (spatial M j h)).trans
        (energy_gradient nu M h))
  have residual:=bare_form nu M h g
  have controlled:=bare_form nu M h c
  have joint:=joint_read seed M time
  change NativeWindowHistorySchurResidualEnergy.residualWork seed M time=2*form nu M h g at residual
  change NativeWindowHistorySchurResidualEnergy.controlledWork seed M time=2*form nu M h c at controlled
  have heatScaled:=congrArg (fun x : ℝ => 2*nu.coeff*x) heatCost
  linarith only [bridge,heatScaled,residual,controlled,joint]

def retainedInput (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  xAction seed M time (temporalResponse seed M time)+wAction seed M time (temporalResponse seed M time)-
    embed (commonForce seed M time)+forcingHistory seed M time

def retainedWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  2*form nu M (temporalResponse seed M time) (jacobian seed M time (retainedInput seed M time))

private theorem add_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G D : E →L[ℝ] E) (w x r : E) :
    2*inner ℝ w (G (D (x+r)))=2*inner ℝ w (G (D x))+2*inner ℝ w (G (D r)) := by
  rw [map_add,map_add,inner_add_right,mul_add]

theorem reaction_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    reactionWork seed M time=NativeWindowHistoryDynamicResponse.reactionWork seed M time+retainedWork seed M time := by
  have split:reaction seed M time=completion seed M time+retainedInput seed M time := by
    unfold reaction retainedInput
    abel
  have source:=congrArg (fun x : H => 2*form nu M (temporalResponse seed M time) (jacobian seed M time x)) split
  apply source.trans
  simpa only [form,NativeWindowHistoryDynamicResponse.reactionWork,retainedWork] using!
    add_pair (E := H) (heat nu M) (jacobian seed M time)
      (temporalResponse seed M time) (completion seed M time) (retainedInput seed M time)

theorem source_retained_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      NativeWindowHistoryDynamicEnergy.sourceRate seed M time≤
        -nu.coeff^2*‖laplacianAction nu M (temporalResponse seed M time)‖^2+
          epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C+
            commutatorWork seed M time (temporalResponse seed M time)+retainedWork seed M time := by
  obtain ⟨first,B,B0,original⟩:=source_generator seed horizon nonnegative epsilon positive
  have responseBudget:=NativeWindowHistoryDynamicResponse.source_reaction_bound (nu := nu) seed horizon nonnegative
  obtain ⟨last,C,C0,source⟩:=responseBudget
  refine ⟨max first last,B+C,add_nonneg B0 C0,fun M above time inside => ?_⟩
  have full:=original M ((le_max_left _ _).trans above) time inside
  have bound:=(le_abs_self _).trans (source M ((le_max_right _ _).trans above) time inside)
  have split:=reaction_split seed M time
  linarith only [full,bound,split]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem commutatorWork_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    commutatorWork seed M (step.2.clockAdvance+time) (temporalResponse seed M (step.2.clockAdvance+time))=
      commutatorWork step.1 M time (temporalResponse step.1 M time) :=
  congrArg₂ (fun (D : H →L[ℝ] H) (w : H) => -2*nu.coeff*(∑j : Coordinate,
    form nu M w (((spatial M j).comp D-D.comp (spatial M j)) (spatial M j w))))
    (NativeWindowHistoryJacobianControl.jacobian_next seed M step generated time time0)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0)

private theorem cancel_part {E : Type*} [AddCommGroup E] [Module ℝ E] (q l x r : E) (a : ℝ)
    (source : q=(-a) • l+(x+r)) : r=q+a • l-x := by
  rw [source,neg_smul]
  abel

theorem retainedWork_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    retainedWork seed M (step.2.clockAdvance+time)=retainedWork step.1 M time := by
  have identity (s : GeneratedWholeRestartCurrent nu) (t : ℝ) :
      retainedInput s M t=rateHistory s M t+nu.coeff • laplacianAction nu M (temporalResponse s M t)-completion s M t := by
    have split:reaction s M t=completion s M t+retainedInput s M t := by
      unfold reaction retainedInput
      abel
    have source:=(rate_split s M t).trans (congrArg
      (fun r : H => (-nu.coeff) • laplacianAction nu M (temporalResponse s M t)+r) split)
    exact cancel_part (E := H) _ _ _ _ nu.coeff source
  have read:=congrArg₂ (fun (q : H) (w : H) => q+nu.coeff • laplacianAction nu M w)
    (NativeWindowHistoryOseen.rateHistory_next seed M step generated time time0)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0)
  have inputNext:retainedInput seed M (step.2.clockAdvance+time)=retainedInput step.1 M time :=
    (identity seed _).trans ((congrArg₂ (fun x y : H => x-y) read
      (NativeWindowHistorySchurCompletion.completion_next seed M step generated time time0)).trans (identity step.1 time).symm)
  exact congrArg₂ (fun w y : H => 2*form nu M w y)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0)
    (congrArg₂ (fun (D : H →L[ℝ] H) (x : H) => D x)
      (NativeWindowHistoryJacobianControl.jacobian_next seed M step generated time time0) inputNext)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianViscous
