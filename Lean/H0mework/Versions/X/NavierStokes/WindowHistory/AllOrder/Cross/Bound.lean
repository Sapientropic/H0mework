import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.MeanStrainJoint
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.CreatedLoadBudget
import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Half

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCenteredCrossWork
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent (physicalSpace pairing coefficients)
open NativeCommonAdvectorAction (curlPair)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryDynamicKernel (transport)
open NativeWindowHistoryOseen (H)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeWindowHistorySpatialWords (history fiber operator)
open NativeWindowHistoryCreationCovariance (centered)
open NativeWindowHistoryCreationFirstJet (firstJet)
open NativeWindowHistoryAdjointSpatialHalf (moment cap energyCap)
open NativeWindowHistoryAdjointSpatialFeedback (sample read lift)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Q" => NativeWindowHistoryMeanProjection.residual
variable {nu : Viscosity}

def point (M : ℕ) (p r q : physicalSpace (modes M)) : ℝ :=
  pairing (modes M) p (transport nu M r q)+pairing (modes M) r (transport nu M p q)

private theorem point_young (M : ℕ) (p r q : physicalSpace (modes M)) (a : ℝ) :
    2*a*point (nu := nu) M p r q ≤
      2*a^2*cap^2*moment (modes M) 2 r*moment (modes M) 1 p+2*curlPair (modes M) q.1 q.1 := by
  have first:=NativeWindowHistorySchurWeakPairing.transport_young (modes M) (modes_zero M) (modes_closed M) nu r p q a
  have last:=NativeWindowHistorySchurWeakPairing.transport_young (modes M) (modes_zero M) (modes_closed M) nu p r q a
  have square:=NativeWindowHistoryCreationHalf.square_product (modes M) (modes_closed M) r p
  have flipped : (∫x : NativePhysicalFourier.Torus,NativeWindowHistoryCreationGeometry.square (modes M) p x*
      NativeWindowHistoryCreationGeometry.square (modes M) r x)=
      ∫x : NativePhysicalFourier.Torus,NativeWindowHistoryCreationGeometry.square (modes M) r x*
        NativeWindowHistoryCreationGeometry.square (modes M) p x := by
    apply integral_congr_ae
    filter_upwards with x
    exact mul_comm _ _
  rw [flipped] at last
  have paid:=mul_le_mul_of_nonneg_left square (sq_nonneg a)
  unfold point
  simp only [NativeWindowHistoryDynamicKernel.transport_apply]
  nlinarith only [first,last,paid]

set_option backward.isDefEq.respectTransparency false in
private theorem point_continuous (M : ℕ) (p : physicalSpace (modes M))
    (r q : ℝ → physicalSpace (modes M)) (rc : Continuous r) (qc : Continuous q) :
    Continuous (fun s => point (nu := nu) M p (r s) (q s)) := by
  have cc : Continuous (fun v : physicalSpace (modes M) => coefficients (modes M) v) :=
    (LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous
  have product:=((transport nu M).continuous.comp rc).clm_apply qc
  have first:=((continuous_const (y := coefficients (modes M) p)).inner (𝕜 := ℝ) (cc.comp product))
  have last:=(cc.comp rc).inner (𝕜 := ℝ) (cc.comp ((transport nu M p).continuous.comp qc))
  convert! first.add last using 1

def residualWord (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) : H :=
  Q (history seed M [j] time)

def work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) : ℝ :=
  ∫lag,point (nu := nu) M (firstJet seed M 0 j time)
    (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
    (centered seed M time (time-lag)) ∂averageMeasure

theorem work_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    Integrable (fun lag => point (nu := nu) M (firstJet seed M 0 j time)
      (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
      (centered seed M time (time-lag))) averageMeasure := by
  have qc:=NativeWindowHistoryCreationCovariance.centered_continuous seed M time
  exact (NativeWindowTraceTerminalGraph.continuous_memLp time _
    (point_continuous M (firstJet seed M 0 j time) _ _
      ((NativeWindowHistorySpatialTransport.finite M j).continuous.comp qc) qc) 1).integrable le_rfl

set_option backward.isDefEq.respectTransparency false in
private theorem word_sample (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    sample M (residualWord seed M j time)=ᵐ[averageMeasure] fun lag =>
      NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)) := by
  have same : residualWord seed M j time=operator M [j] (Q (finiteHistory seed time M)) :=
    NativeWindowHistoryMeanProjection.residual_comp (fiber M [j]) (finiteHistory seed time M)
  rw [same]
  filter_upwards [(fiber M [j]).coeFn_compLpL (Q (finiteHistory seed time M)),
    NativeWindowHistoryCreationHalf.sample_centered seed M time] with lag actual original
  change operator M [j] (Q (finiteHistory seed time M)) lag=_ at actual
  change NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
    (operator M [j] (Q (finiteHistory seed time M)) lag)=_
  rw [actual]
  change NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
    (NativePhysicalPairing.includeCLM (modes M) (modes_closed M)
      (NativeWindowHistorySpatialTransport.finite M j
        (sample M (Q (finiteHistory seed time M)) lag)))=_
  rw [NativePhysicalPairing.restrict_include,original]

private theorem q_gradient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (∫lag,curlPair (modes M) (centered seed M time (time-lag)).1 (centered seed M time (time-lag)).1 ∂averageMeasure)=
      gradient M (Q (finiteHistory seed time M)) := by
  unfold NativeWindowTraceWholeHistory.gradient
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryCreationHalf.sample_centered seed M time] with lag actual
  exact (congrArg (fun v : physicalSpace (modes M) => curlPair (modes M) v.1 v.1) actual).symm

private theorem r_moment (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    (∫lag,moment (modes M) 2 (NativeWindowHistorySpatialTransport.finite M j
      (centered seed M time (time-lag))) ∂averageMeasure)=
        ‖lift M (fun k => NativeUnheatedSexticLatticePower.radical k^2) (residualWord seed M j time)‖^2 := by
  rw [NativeWindowHistoryAdjointSpatialFeedback.lift_square]
  apply integral_congr_ae
  filter_upwards [word_sample seed M j time] with lag actual
  rw [NativeWindowHistoryAdjointSpatialFeedback.read_moment]
  exact congrArg (moment (modes M) 2) actual.symm


private theorem q_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Integrable (fun lag => curlPair (modes M) (centered seed M time (time-lag)).1
      (centered seed M time (time-lag)).1) averageMeasure := by
  apply (NativeWindowTraceWholeHistory.gradient_integrable nu M (Q (finiteHistory seed time M))).congr
  filter_upwards [NativeWindowHistoryCreationHalf.sample_centered seed M time] with lag actual
  exact congrArg (fun v : physicalSpace (modes M) => curlPair (modes M) v.1 v.1) actual

private theorem r_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    Integrable (fun lag => moment (modes M) 2 (NativeWindowHistorySpatialTransport.finite M j
      (centered seed M time (time-lag)))) averageMeasure := by
  apply (NativeWindowHistoryAdjointSpatialFeedback.read_integrable M
    (fun k => NativeUnheatedSexticLatticePower.radical k^2) (residualWord seed M j time)).congr
  filter_upwards [word_sample seed M j time] with lag actual
  rw [NativeWindowHistoryAdjointSpatialFeedback.read_moment]
  exact congrArg (moment (modes M) 2) actual

def coefficient (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  2*cap^2*NativeWindowHistoryCreationFirstJet.budget seed 0 horizon

theorem coefficient_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ coefficient seed horizon := by
  unfold coefficient
  positivity [NativeWindowHistoryCreationFirstJet.budget_nonnegative seed 0 horizon]

set_option backward.isDefEq.respectTransparency false in
theorem source_young (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (j : Coordinate) (time : ℝ) (inside : time∈Icc 0 horizon) (a : ℝ) :
    2*a*work seed M j time ≤ a^2*coefficient seed horizon*
      ‖lift M (fun k => NativeUnheatedSexticLatticePower.radical k^2) (residualWord seed M j time)‖^2+
        2*NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon := by
  have ppaid:=NativeWindowHistoryCreationFirstJet.firstJet_bound seed 0 horizon M j time inside
  have pointPaid (lag : ℝ) :
      2*a*point (nu := nu) M (firstJet seed M 0 j time)
        (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
        (centered seed M time (time-lag)) ≤
      (a^2*coefficient seed horizon)*moment (modes M) 2
        (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))+
          2*curlPair (modes M) (centered seed M time (time-lag)).1 (centered seed M time (time-lag)).1 := by
    have first:=point_young (nu := nu) M (firstJet seed M 0 j time)
      (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
      (centered seed M time (time-lag)) a
    have mom0:=NativeWindowHistoryAdjointSpatialHalf.moment_nonnegative (modes M) 2
      (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
    have paid:=mul_le_mul_of_nonneg_left ppaid (show 0 ≤ 2*a^2*cap^2*
      moment (modes M) 2 (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag))) by
        positivity)
    apply first.trans
    exact (add_le_add paid le_rfl).trans_eq (by unfold coefficient; ring)
  have integrated:=integral_mono ((work_integrable seed M j time).const_mul (2*a))
    (((r_integrable seed M j time).const_mul (a^2*coefficient seed horizon)).add
      ((q_integrable seed M time).const_mul 2)) pointPaid
  simp only [Pi.add_apply] at integrated
  rw [integral_add ((r_integrable seed M j time).const_mul (a^2*coefficient seed horizon))
    ((q_integrable seed M time).const_mul 2),integral_const_mul,integral_const_mul,integral_const_mul,
    r_moment,q_gradient] at integrated
  have qpaid := (NativeWindowHistoryMeanGradient.gradient_residual_le seed M (finiteHistory seed time M)).trans
    (NativeWindowHistorySchurTemporalControl.source_gradient seed horizon M time inside)
  exact integrated.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left qpaid (by norm_num)))

private theorem absolute_young (w P G delta : ℝ) (positive : 0 < delta)
    (paid : ∀a : ℝ,2*a*w ≤ a^2*P+G) : |2*w| ≤ delta*P+delta⁻¹*G := by
  have main (e : ℝ) (e0 : 0 < e) : |2*w| ≤ e⁻¹*P+e*G := by
    have u:=mul_le_mul_of_nonneg_left (paid e⁻¹) e0.le
    have l:=mul_le_mul_of_nonneg_left (paid (-e⁻¹)) e0.le
    have one : e*(2*e⁻¹*w)=2*w := by field_simp
    have two : e*(2*(-e⁻¹)*w)= -2*w := by field_simp
    have three : e*((e⁻¹)^2*P+G)=e⁻¹*P+e*G := by field_simp
    rw [one,three] at u
    rw [neg_sq,two,three] at l
    exact abs_le.mpr ⟨by linarith only [l],u⟩
  simpa only [inv_inv] using main delta⁻¹ (inv_pos.mpr positive)

set_option backward.isDefEq.respectTransparency false in
theorem source (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0 < epsilon) :
    ∃C : ℝ,0 ≤ C ∧ ∀M (j : Coordinate) time,time∈Icc 0 horizon →
      |2*work seed M j time| ≤ epsilon*gradient M (history seed M [j] time)+C := by
  obtain ⟨X,X0,hist⟩:=NativeWindowHistoryAllOrderCreatedLoadBudget.first_history_bound seed horizon
  let K:=coefficient seed horizon
  have K0 : 0 ≤ K:=coefficient_nonnegative seed horizon
  have A0 := (NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu).le
  let delta:=epsilon/(K*energyCap nu*nu.coeff+1)
  have d0 : 0 < delta := by positivity [nu.coeff_pos]
  let G:=NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon
  have G0 : 0 ≤ G:=le_max_left _ _
  refine ⟨delta*K*energyCap nu*X+delta⁻¹*(2*G),by positivity,fun M j time inside => ?_⟩
  let r:=residualWord seed M j time
  have first:=absolute_young (work seed M j time)
    (K*‖lift M (fun k => NativeUnheatedSexticLatticePower.radical k^2) r‖^2) (2*G) delta d0
    (fun a => by simpa only [mul_assoc,K,r,G] using source_young seed horizon M j time inside a)
  have mass : ‖r‖^2 ≤ X :=
    (NativeWindowHistorySchurCenteredGraph.residual_norm_square (history seed M [j] time)).trans (hist M j time inside)
  have grad := NativeWindowHistoryMeanGradient.gradient_residual_le seed M (history seed M [j] time)
  have energy:=NativeWindowHistoryAdjointSpatialFeedback.whole_moment_energy (nu := nu) M r
  have control : ‖lift M (fun k => NativeUnheatedSexticLatticePower.radical k^2) r‖^2 ≤
      energyCap nu*(X+nu.coeff*gradient M (history seed M [j] time)) :=
    energy.trans (mul_le_mul_of_nonneg_left (add_le_add mass (mul_le_mul_of_nonneg_left grad nu.coeff_pos.le)) A0)
  have scaled:=mul_le_mul_of_nonneg_left control (mul_nonneg d0.le K0)
  have denominator : 0 < K*energyCap nu*nu.coeff+1 := by positivity [nu.coeff_pos]
  have cancel : delta*(K*energyCap nu*nu.coeff+1)=epsilon:=div_mul_cancel₀ _ denominator.ne'
  have small : delta*K*energyCap nu*nu.coeff ≤ epsilon := by nlinarith only [cancel,d0]
  have final:=mul_le_mul_of_nonneg_right small
    (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M (history seed M [j] time))
  nlinarith only [first,scaled,final]
end
end SaturationMonoid.NavierStokes.NativeCenteredCrossWork
