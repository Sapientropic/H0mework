import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineCouplingPaid
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Mean

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
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
noncomputable section
variable {nu : Viscosity}

theorem mean_operator_split (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (u : NativeWholeResolvent.wholePhysical) :
    NativeWindowHistoryMeanAction.meanOperator seed M time u=
      (-nu.coeff) • laplacianFiber nu M u+
        NativeWindowHistoryMeanDrift.drift seed M time u := by
  have diffusion:=NativeWindowMetricGraphMean.diffusion_laplacian nu M u
  have source : NativeWindowHistoryMeanDrift.drift seed M time u=
      NativeWindowHistoryMeanAction.meanOperator seed M time u-
        NativeWindowHistoryMeanBlocks.diffusion nu M u := by
    rfl
  rw [diffusion] at source
  rw [source]
  abel

theorem source_first_word_drift_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon eta : ℝ) (positive : 0<eta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →∀j : Coordinate,
      let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
      ‖NativeWindowHistoryMeanDrift.drift seed M time u‖^2≤
        eta*‖laplacianFiber nu M u‖^2+C := by
  let delta:=eta/2
  have delta0 : 0<delta := by dsimp only [delta]; positivity
  let B:=NativeWindowHistoryCreationSource.budget seed horizon delta
  have B0 : 0≤B:=NativeWindowHistoryCreationSource.budget_nonnegative seed horizon delta delta0
  let GU:=max 0 (NativeWindowAugmentedPayment.graphBudget seed 0 horizon)
  have GU0 : 0≤GU:=le_max_left _ _
  let C:=B^2*GU/(4*delta)
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨C,C0,fun M time inside j => ?_⟩
  let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
  let L:=laplacianFiber nu M u
  have drift:=NativeWindowMetricGraphMean.drift_bound seed horizon delta delta0 M time inside u
  have mass:=NativeCenteredMeanPrincipal.source_first_word_u_mass seed horizon M time inside j
  have young:=scalar_young (B*‖u‖) ‖L‖ delta delta0
  have massScaled:=mul_le_mul_of_nonneg_left mass (by positivity : 0≤B^2/(4*delta))
  have normalized : (B*‖u‖)^2/(4*delta)=
      (B^2/(4*delta))*‖u‖^2 := by ring
  rw [normalized] at young
  have cost : (B^2/(4*delta))*GU=C := by dsimp only [C]; ring
  have weight : delta+delta=eta := by dsimp only [delta]; ring
  change ‖NativeWindowHistoryMeanDrift.drift seed M time u‖^2≤eta*‖L‖^2+C
  nlinarith only [drift,young,massScaled,cost,weight]

theorem mean_word_diagonal_split (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) :
    let u:=NativeWindowHistoryAllOrderWord.value seed M word time
    let x:=NativeWindowHistoryMeanProjection.embed u
    let L:=laplacianAction nu M x
    let d:=NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanDrift.drift seed M time u)
    let B:=fullMetricAction seed time M F radius
    let T:=transposeMetricAction seed time M F radius
    twoLeg B x (NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanAction.meanOperator seed M time u))=
      inner ℝ ((-nu.coeff) • L+d) (B x+T x) := by
  intro u x L d B T
  have source:=mean_operator_split seed M time u
  have lifted:=congrArg NativeWindowHistoryMeanProjection.embed source
  simp only [map_add,map_smul] at lifted
  have lap : L=NativeWindowHistoryMeanProjection.embed (laplacianFiber nu M u) := by
    dsimp only [L,x,laplacianAction]
    exact NativeWindowHistoryMeanProjection.comp_embed (laplacianFiber nu M) u
  rw [← lap] at lifted
  have paired:=twoLeg_adjoint seed M time F radius x
    (NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanAction.meanOperator seed M time u))
  change twoLeg B x _=inner ℝ _ (B x+T x)
  rw [paired,lifted]

theorem drift_scalar (epsilon K GU Cd d m a bx tx : ℝ)
    (epsilon0 : 0<epsilon) (K0 : 0≤K)
    (graphBx : bx^2≤K*(d^2+m^2))
    (graphTx : tx^2≤K*(d^2+m^2))
    (mass : m^2≤GU)
    (drift : a^2≤(epsilon*(epsilon/(8*(K+1)))/2)*d^2+Cd) :
    a*(bx+tx)≤epsilon*d^2+
      (2*K*(epsilon/(8*(K+1))))*GU+
        Cd/(2*(epsilon/(8*(K+1)))) := by
  let delta:=epsilon/(8*(K+1))
  let eta:=epsilon*delta/2
  have delta0 : 0<delta := by dsimp only [delta]; positivity
  have first:=scalar_young a bx delta delta0
  have last:=scalar_young a tx delta delta0
  have young : a*(bx+tx)≤delta*(bx^2+tx^2)+a^2/(2*delta) := by
    have den : delta ≠0:=delta0.ne'
    field_simp at first last ⊢
    nlinarith only [first,last]
  have graph : bx^2+tx^2≤2*K*(d^2+m^2) := by
    nlinarith only [graphBx,graphTx]
  have graphScaled:=mul_le_mul_of_nonneg_left graph delta0.le
  have driftScaled:=div_le_div_of_nonneg_right drift (by positivity : 0≤2*delta)
  have driftRead : (eta*d^2+Cd)/(2*delta)=
      (eta/(2*delta))*d^2+Cd/(2*delta) := by ring
  dsimp only [eta,delta] at driftRead
  rw [driftRead] at driftScaled
  have frac : 2*K*delta≤epsilon/4 := by
    have den : 0<8*(K+1) := by positivity
    have same : delta*(8*(K+1))=epsilon := by
      dsimp only [delta]
      exact div_mul_cancel₀ _ den.ne'
    nlinarith only [same,delta0,K0]
  have etaRead : eta/(2*delta)=epsilon/4 := by
    dsimp only [eta]
    field_simp [delta0.ne']
    ring
  have coefficient : 2*K*delta+eta/(2*delta)≤epsilon := by
    rw [etaRead]
    linarith only [frac,epsilon0]
  have costScaled:=mul_le_mul_of_nonneg_right coefficient (sq_nonneg d)
  have massScaled:=mul_le_mul_of_nonneg_left mass
    (mul_nonneg (mul_nonneg (by norm_num : 0≤(2:ℝ)) K0) delta0.le)
  change a*(bx+tx)≤epsilon*d^2+2*K*delta*GU+Cd/(2*delta)
  nlinarith only [young,graphScaled,driftScaled,costScaled,massScaled]

end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
