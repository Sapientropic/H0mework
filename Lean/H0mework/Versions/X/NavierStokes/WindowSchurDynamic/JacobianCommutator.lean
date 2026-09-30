import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatialTransport
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianControl

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianCommutator
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowHistoryOseen (H lift)
open NativeWindowHistorySpatialWords (fiber operator)
open NativeWindowHistorySpatialTransport (finite)
open NativeWindowHistoryFrozenInverse (kernel)
open NativeWindowHistoryDynamicHistory (kernelAction kernelAction_ae)
open NativeWindowHistorySchurAdvectorFiber (family rawProfile xProfile)
open NativeWindowHistorySchurTranspose (transposeAction transpose_ae)
open NativeWindowHistorySchurCompletion (completion)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryJacobianControl (correction jacobian)
noncomputable section
variable {nu : Viscosity}

theorem fiber_original (M : ℕ) (j : Coordinate) : fiber M [j]=lift M (finite M j) := rfl

theorem fiber_included (M : ℕ) (j : Coordinate) (v : physicalSpace (modes M)) :
    fiber M [j] (includeCLM (modes M) (modes_closed M) v)=
      includeCLM (modes M) (modes_closed M) (finite M j v) :=
  NativeWindowHistoryOseen.lift_included M _ v

theorem fiber_restrict (M : ℕ) (j : Coordinate) (v : wholePhysical) :
    restrictCLM (modes M) (modes_zero M) (modes_closed M) (fiber M [j] v)=
      finite M j (restrictCLM (modes M) (modes_zero M) (modes_closed M) v) := by
  rw [fiber_original,lift,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,restrict_include]

theorem family_derivative (nu : Viscosity) (M : ℕ) (j : Coordinate) (u v : wholePhysical) :
    fiber M [j] (family nu M u v)=family nu M (fiber M [j] u) v+family nu M u (fiber M [j] v) := by
  simp only [NativeWindowHistorySchurAdvectorFiber.family_original,fiber_included,fiber_restrict,← map_add]
  exact congrArg (includeCLM (modes M) (modes_closed M))
    (NativeWindowHistorySpatialTransport.transport_derivative (modes M) (modes_zero M) (modes_closed M) nu _ _ j)

theorem kernel_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) (v : wholePhysical) :
    fiber M [j] (kernel seed M time v)-kernel seed M time (fiber M [j] v)=
      kernel seed M time (family nu M (fiber M [j] (NativeWindowHistoryOseen.velocityPath seed M time))
        (kernel seed M time v)) := by
  let includeFinite := includeCLM (modes M) (modes_closed M)
  let restrict := restrictCLM (modes M) (modes_zero M) (modes_closed M)
  have finiteRead := NativeWindowHistorySpatialTransport.kernel_derivative nu M j
    (NativeWindowTraceAdjoint.value seed M time) (restrict v)
  have included := congrArg includeFinite finiteRead
  simp only [NativeWindowHistoryDynamicKernel.kernel_source,NativeWindowHistoryDynamicKernel.transport_apply] at included
  change fiber M [j] (includeFinite (NativeWindowHistoryFrozenInverse.physical seed M time (restrict v)))-
    includeFinite (NativeWindowHistoryFrozenInverse.physical seed M time (restrict (fiber M [j] v)))=_
  rw [fiber_included,fiber_restrict]
  change _=includeFinite (NativeWindowHistoryFrozenInverse.physical seed M time (restrict
    (family nu M (fiber M [j] (includeFinite (NativeWindowTraceAdjoint.value seed M time)))
      (includeFinite (NativeWindowHistoryFrozenInverse.physical seed M time (restrict v))))))
  rw [fiber_included,NativeWindowHistorySchurAdvectorFiber.family_original]
  simp only [restrict,includeFinite,restrict_include]
  exact (map_sub includeFinite _ _).symm.trans included

theorem spatial_ae (M : ℕ) (j : Coordinate) (v : H) :
    operator M [j] v=ᵐ[averageMeasure] fun lag => fiber M [j] (v lag) :=
  (fiber M [j]).coeFn_compLpL v

def derivativeProfile (M : ℕ) (j : Coordinate) (v : Lp wholePhysical ∞ averageMeasure) :
    Lp wholePhysical ∞ averageMeasure := (fiber M [j]).compLpL ∞ averageMeasure v

def advectorDerivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) : H →L[ℝ] H :=
  (family nu M).holderL averageMeasure ∞ 2 2 (derivativeProfile M j (rawProfile seed M time))

def transposeDerivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) : H →L[ℝ] H :=
  (family nu M).flip.holderL averageMeasure ∞ 2 2 (derivativeProfile M j (xProfile seed M time))

theorem advectorDerivative_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) (v : H) :
    advectorDerivative seed M j time v=ᵐ[averageMeasure] fun lag =>
      family nu M (operator M [j] (finiteHistory seed time M) lag) (v lag) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical) (F := wholePhysical) (G := wholePhysical)
    (r := 2) (family nu M) (derivativeProfile M j (rawProfile seed M time)) v,
    (fiber M [j]).coeFn_compLpL (rawProfile seed M time),NativeWindowHistorySchurAdvectorFiber.rawProfile_ae seed M time,
    spatial_ae M j (finiteHistory seed time M)] with lag applied differentiated source actual
  change advectorDerivative seed M j time v lag=family nu M (derivativeProfile M j (rawProfile seed M time) lag) (v lag) at applied
  have profileRead : derivativeProfile M j (rawProfile seed M time) lag=fiber M [j] (rawProfile seed M time lag) := differentiated
  have sourceRead := profileRead.trans ((congrArg (fiber M [j]) source).trans actual.symm)
  exact applied.trans (congrArg (fun u : wholePhysical => family nu M u (v lag)) sourceRead)


theorem transposeDerivative_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) (v : H) :
    transposeDerivative seed M j time v=ᵐ[averageMeasure] fun lag =>
      family nu M (v lag) (operator M [j] (completion seed M time) lag) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical) (F := wholePhysical) (G := wholePhysical)
    (r := 2) (family nu M).flip (derivativeProfile M j (xProfile seed M time)) v,
    (fiber M [j]).coeFn_compLpL (xProfile seed M time),NativeWindowHistorySchurAdvectorFiber.xProfile_ae seed M time,
    spatial_ae M j (completion seed M time)] with lag applied differentiated source actual
  change transposeDerivative seed M j time v lag=family nu M (v lag) (derivativeProfile M j (xProfile seed M time) lag) at applied
  have profileRead : derivativeProfile M j (xProfile seed M time) lag=fiber M [j] (xProfile seed M time lag) := differentiated
  have sourceRead := profileRead.trans ((congrArg (fiber M [j]) source).trans actual.symm)
  exact applied.trans (congrArg (fun u : wholePhysical => family nu M (v lag) u) sourceRead)


theorem kernel_commutator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) (v : H) :
    operator M [j] (kernelAction seed M time v)-kernelAction seed M time (operator M [j] v)=
      kernelAction seed M time (advectorDerivative seed M j time (kernelAction seed M time v)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (operator M [j] (kernelAction seed M time v)) (kernelAction seed M time (operator M [j] v)),
    spatial_ae M j (kernelAction seed M time v),kernelAction_ae seed M time v,
    kernelAction_ae seed M time (operator M [j] v),spatial_ae M j v,
    kernelAction_ae seed M time (advectorDerivative seed M j time (kernelAction seed M time v)),
    advectorDerivative_ae seed M j time (kernelAction seed M time v),spatial_ae M j (finiteHistory seed time M),
    NativeWindowHistoryOseen.history_original seed M time] with lag sub first raw second dv last transported dh original
  have firstRead := first.trans (congrArg (fiber M [j]) raw)
  have secondRead := second.trans (congrArg (kernel seed M (time-lag)) dv)
  have leftRead := sub.trans (congrArg₂ (fun a b : wholePhysical => a-b) firstRead secondRead)
  have sourceRead : operator M [j] (finiteHistory seed time M) lag=
      fiber M [j] (NativeWindowHistoryOseen.velocityPath seed M (time-lag)) :=
    dh.trans (congrArg (fiber M [j]) original)
  have transportRead := transported.trans (congrArg₂ (fun a b : wholePhysical => family nu M a b) sourceRead raw)
  have rightRead := last.trans (congrArg (kernel seed M (time-lag)) transportRead)
  exact leftRead.trans ((kernel_derivative seed M j (time-lag) (v lag)).trans rightRead.symm)


theorem transpose_commutator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) (v : H) :
    operator M [j] (transposeAction seed M time v)-transposeAction seed M time (operator M [j] v)=
      transposeDerivative seed M j time v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (operator M [j] (transposeAction seed M time v)) (transposeAction seed M time (operator M [j] v)),
    spatial_ae M j (transposeAction seed M time v),transpose_ae seed M time v,
    transpose_ae seed M time (operator M [j] v),spatial_ae M j v,
    transposeDerivative_ae seed M j time v,spatial_ae M j (completion seed M time)] with lag sub first raw second dv last dx
  have leftRead := sub.trans (congrArg₂ (fun a b : wholePhysical => a-b)
    (first.trans (congrArg (fiber M [j]) raw))
    (second.trans (congrArg (fun a : wholePhysical => family nu M a (completion seed M time lag)) dv)))
  have rightRead := last.trans (congrArg (fun a : wholePhysical => family nu M (v lag) a) dx)
  apply leftRead.trans
  apply Eq.trans _ rightRead.symm
  rw [family_derivative]
  abel


private theorem product_commutator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D K T B C : E →L[ℝ] E) (first : ∀ v,D (K v)-K (D v)=K (B (K v)))
    (last : ∀ v,D (T v)-T (D v)=C v) (v : E) :
    D ((ContinuousLinearMap.id ℝ E-K.comp T) v)-(ContinuousLinearMap.id ℝ E-K.comp T) (D v)=
      -K (B ((K.comp T) v))-K (C v) := by
  have applied := congrArg K (last v)
  rw [map_sub] at applied
  simp only [sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,map_sub]
  calc
    _=-(D (K (T v))-K (D (T v)))-(K (D (T v))-K (T (D v))) := by abel
    _=_ := by rw [first,applied]


theorem jacobian_commutator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) (v : H) :
    operator M [j] (jacobian seed M time v)-jacobian seed M time (operator M [j] v)=
      -kernelAction seed M time (advectorDerivative seed M j time (correction seed M time v))-
        kernelAction seed M time (transposeDerivative seed M j time v) := by
  simpa only [jacobian,correction] using! product_commutator (E := H) (operator M [j]) (kernelAction seed M time) (transposeAction seed M time)
    (advectorDerivative seed M j time) (transposeDerivative seed M j time)
    (kernel_commutator seed M j time) (transpose_commutator seed M j time) v

theorem jacobian_operator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    (operator M [j]).comp (jacobian seed M time)-(jacobian seed M time).comp (operator M [j])=
      -(kernelAction seed M time).comp ((advectorDerivative seed M j time).comp (correction seed M time))-
        (kernelAction seed M time).comp (transposeDerivative seed M j time) := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [sub_apply,neg_apply,ContinuousLinearMap.comp_apply] using! jacobian_commutator seed M j time v

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem advectorDerivative_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    advectorDerivative seed M j (step.2.clockAdvance+time)=advectorDerivative step.1 M j time := by
  have source := congrArg (operator M [j]) (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0 M)
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [advectorDerivative_ae seed M j (step.2.clockAdvance+time) v,
    advectorDerivative_ae step.1 M j time v] with lag first last
  exact first.trans ((congrArg (fun u : wholePhysical => family nu M u (v lag))
    (congrArg (fun h : H => h lag) source)).trans last.symm)

theorem transposeDerivative_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    transposeDerivative seed M j (step.2.clockAdvance+time)=transposeDerivative step.1 M j time := by
  have source := congrArg (operator M [j]) (NativeWindowHistorySchurCompletion.completion_next seed M step generated time time0)
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [transposeDerivative_ae seed M j (step.2.clockAdvance+time) v,
    transposeDerivative_ae step.1 M j time v] with lag first last
  exact first.trans ((congrArg (fun u : wholePhysical => family nu M (v lag) u)
    (congrArg (fun h : H => h lag) source)).trans last.symm)

theorem commutator_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    (operator M [j]).comp (jacobian seed M (step.2.clockAdvance+time))-
        (jacobian seed M (step.2.clockAdvance+time)).comp (operator M [j])=
      (operator M [j]).comp (jacobian step.1 M time)-(jacobian step.1 M time).comp (operator M [j]) :=
  congrArg (fun J : H →L[ℝ] H => (operator M [j]).comp J-J.comp (operator M [j]))
    (NativeWindowHistoryJacobianControl.jacobian_next seed M step generated time time0)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianCommutator
