import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineMeanDiagonalPaid
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorEnergy

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
noncomputable section
variable {nu : Viscosity}

theorem source_first_word_x_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon)
    (eta : ℝ) (positive : 0<eta) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀time∈Icc 0 horizon,∀j : Coordinate,
      let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
      ‖NativeWindowHistoryMeanProjection.residual
        (NativeWindowHistorySchurAdvectorAction.xAction seed M time q)‖^2≤
        eta*‖laplacianAction nu M q‖^2+C := by
  let delta:=eta/2
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  obtain ⟨low,B,B0,paid⟩:=NativeWindowHistorySchurAdvectorAction.source_graph_bound
    seed horizon nonnegative delta delta0
  let GQ:=NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon
  have GQ0 : 0≤GQ:=le_max_left _ _
  let C:=B^2*GQ/(4*delta)
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨low,C,C0,fun M above time inside j => ?_⟩
  let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
  let L:=laplacianAction nu M q
  have source:=paid M above time inside q
  have gradient:=NativeWindowMetricGraphHistory.gradient_bound nu M q
  have scaled:=mul_le_mul_of_nonneg_left gradient B0
  have bound : ‖NativeWindowHistorySchurAdvectorAction.xAction seed M time q‖^2≤
      delta*‖L‖^2+B*‖q‖*‖L‖ := by
    nlinarith only [source,scaled]
  have residual:=NativeWindowHistorySchurCenteredGraph.residual_norm_square
    (NativeWindowHistorySchurAdvectorAction.xAction seed M time q)
  have mass:=NativeCenteredBathPaid.source_first_word_q_mass seed horizon M time inside j
  have massScaled:=mul_le_mul_of_nonneg_left mass (by positivity : 0≤B^2/(4*delta))
  have young:=scalar_young (B*‖q‖) ‖L‖ delta delta0
  have normalized : (B*‖q‖)^2/(4*delta)=(B^2/(4*delta))*‖q‖^2 := by ring
  rw [normalized] at young
  have cost : (B^2/(4*delta))*GQ=C := by dsimp only [C]; ring
  have weight : delta+delta=eta := by dsimp only [delta]; ring
  change ‖NativeWindowHistoryMeanProjection.residual
      (NativeWindowHistorySchurAdvectorAction.xAction seed M time q)‖^2≤
    eta*‖L‖^2+C
  nlinarith only [bound,residual,young,massScaled,cost,weight]

private theorem residual_triple
    (Q : NativeWindowTraceWholeHistory.H →L[ℝ] NativeWindowTraceWholeHistory.H)
    (l x w : NativeWindowTraceWholeHistory.H) (a : ℝ) (fixed : Q l=l) :
    Q (a • l+x+w)=a • l+Q x+Q w := by
  calc
    Q (a • l+x+w)=Q (a • l+x)+Q w := Q.map_add _ _
    _=(Q (a • l)+Q x)+Q w := congrArg (fun z => z+Q w) (Q.map_add _ _)
    _=(a • Q l+Q x)+Q w := congrArg (fun z => (z+Q x)+Q w) (Q.map_smul a l)
    _=_ := by rw [fixed]

theorem bath_residual_split (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (q : NativeWindowTraceWholeHistory.H)
    (centered : NativeWindowHistoryMeanProjection.residual q=q) :
    NativeWindowHistoryMeanBlocks.bath seed M time q=
      (-nu.coeff) • laplacianAction nu M q+
        NativeWindowHistoryMeanProjection.residual
          (NativeWindowHistorySchurAdvectorAction.xAction seed M time q)+
        NativeWindowHistoryMeanProjection.residual
          (NativeWindowHistorySchurAdvectorAction.wAction seed M time q) := by
  let Q:=NativeWindowHistoryMeanProjection.residual
  let X:=NativeWindowHistorySchurAdvectorAction.xAction seed M time q
  let W:=NativeWindowHistorySchurAdvectorAction.wAction seed M time q
  let L:=laplacianAction nu M q
  have read:=NativeWindowHistorySchurAdvectorEnergy.source_action_read seed M time q
  have commute:=NativeWindowHistoryMeanProjection.residual_comp
    (NativeWindowHistoryAnnihilationControl.laplacianFiber nu M) q
  change Q L=laplacianAction nu M (Q q) at commute
  have lap : Q L=L := commute.trans
        (congrArg (laplacianAction nu M) centered)
  change Q (NativeWindowHistoryOseen.action seed M time (Q q))=
    (-nu.coeff) • L+Q X+Q W
  calc
    Q (NativeWindowHistoryOseen.action seed M time (Q q))=
        Q (NativeWindowHistoryOseen.action seed M time q) :=
      congrArg (fun z : NativeWindowTraceWholeHistory.H =>
        Q (NativeWindowHistoryOseen.action seed M time z)) centered
    _=Q ((-nu.coeff) • L+X+W) := congrArg Q read
    _=(-nu.coeff) • L+Q X+Q W := residual_triple Q L X W (-nu.coeff) lap

theorem bath_word_split (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) :
    let q:=NativeWindowHistoryMeanProjection.residual
      (NativeWindowHistorySpatialWords.history seed M word time)
    let L:=laplacianAction nu M q
    let X:=NativeWindowHistoryMeanProjection.residual
      (NativeWindowHistorySchurAdvectorAction.xAction seed M time q)
    let W:=NativeWindowHistoryMeanProjection.residual
      (NativeWindowHistorySchurAdvectorAction.wAction seed M time q)
    let B:=fullMetricAction seed time M F radius
    let T:=transposeMetricAction seed time M F radius
    twoLeg B q (NativeWindowHistoryMeanBlocks.bath seed M time q)=
      inner ℝ ((-nu.coeff) • L+X+W) (B q+T q) := by
  intro q L X W B T
  have centered : NativeWindowHistoryMeanProjection.residual q=q :=
    NativeWindowHistoryBathResolvent.residual_square _
  have source:=bath_residual_split seed M time q centered
  have paired:=twoLeg_adjoint seed M time F radius q
    (NativeWindowHistoryMeanBlocks.bath seed M time q)
  change twoLeg B q _=inner ℝ _ (B q+T q)
  rw [paired,source]
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
