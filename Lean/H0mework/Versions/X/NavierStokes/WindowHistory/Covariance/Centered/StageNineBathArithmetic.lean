import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineBathSource
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineMeanDiagonalSource

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

theorem signed_bath_arithmetic
    (nu K G Cx : ℝ) (nu0 : 0<nu) (K0 : 0≤K)
    (q L X W Bq Tq : NativeWindowTraceWholeHistory.H)
    (mass : ‖q‖^2≤G)
    (firstGraph : ‖Bq‖^2≤K*(‖L‖^2+‖q‖^2))
    (lastGraph : ‖Tq‖^2≤K*(‖L‖^2+‖q‖^2))
    (firstHeat : -2*nu*inner ℝ Bq L≤-nu^2*‖L‖^2+K*‖q‖^2)
    (lastHeat : -2*nu*inner ℝ Tq L≤-nu^2*‖L‖^2+K*‖q‖^2)
    (xSmall : ‖X‖^2≤
      ((nu^2/4)*((nu^2/4)/(8*(K+1)))/2)*‖L‖^2+Cx) :
    inner ℝ ((-nu) • L+X+W) (Bq+Tq)≤
      -(nu^2/2)*‖L‖^2+inner ℝ W (Bq+Tq)+
        (K+2*K*((nu^2/4)/(8*(K+1))))*G+
        Cx/(2*((nu^2/4)/(8*(K+1)))) := by
  let epsilon:=nu^2/4
  have epsilon0 : 0<epsilon:=by dsimp only [epsilon]; positivity
  let delta:=epsilon/(8*(K+1))
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  have viscous : -nu*(inner ℝ L Bq+inner ℝ L Tq)≤
      -nu^2*‖L‖^2+K*‖q‖^2 := by
    have s1:=real_inner_comm Bq L
    have s2:=real_inner_comm Tq L
    rw [s1,s2]
    nlinarith only [firstHeat,lastHeat]
  have xCost:=drift_scalar epsilon K G Cx ‖L‖ ‖q‖ ‖X‖ ‖Bq‖ ‖Tq‖
    epsilon0 K0 firstGraph lastGraph mass
    (by simpa only [epsilon,delta] using xSmall)
  have xPair : inner ℝ X (Bq+Tq)≤
      epsilon*‖L‖^2+2*K*delta*G+Cx/(2*delta) := by
    have pair:=real_inner_le_norm X (Bq+Tq)
    have norm:=norm_add_le Bq Tq
    have scaled:=mul_le_mul_of_nonneg_left norm (norm_nonneg X)
    exact (pair.trans scaled).trans xCost
  have algebra : inner ℝ ((-nu) • L+X+W) (Bq+Tq)=
      -nu*(inner ℝ L Bq+inner ℝ L Tq)+
        inner ℝ X (Bq+Tq)+inner ℝ W (Bq+Tq) := by
    have a1:=inner_add_left (𝕜 := ℝ) (E := NativeWindowTraceWholeHistory.H)
      ((-nu) • L+X) W (Bq+Tq)
    have a2:=inner_add_left (𝕜 := ℝ) (E := NativeWindowTraceWholeHistory.H)
      ((-nu) • L) X (Bq+Tq)
    have a3:=real_inner_smul_left (F := NativeWindowTraceWholeHistory.H) L (Bq+Tq) (-nu)
    have a4:=inner_add_right (𝕜 := ℝ) (E := NativeWindowTraceWholeHistory.H) L Bq Tq
    calc
      _=inner ℝ ((-nu) • L+X) (Bq+Tq)+inner ℝ W (Bq+Tq) := a1
      _=(inner ℝ ((-nu) • L) (Bq+Tq)+inner ℝ X (Bq+Tq))+
          inner ℝ W (Bq+Tq) := congrArg (fun z => z+inner ℝ W (Bq+Tq)) a2
      _=((-nu)*inner ℝ L (Bq+Tq)+inner ℝ X (Bq+Tq))+
          inner ℝ W (Bq+Tq) :=
        congrArg (fun z => (z+inner ℝ X (Bq+Tq))+inner ℝ W (Bq+Tq)) a3
      _=((-nu)*(inner ℝ L Bq+inner ℝ L Tq)+inner ℝ X (Bq+Tq))+
          inner ℝ W (Bq+Tq) :=
        congrArg (fun z => ((-nu)*z+inner ℝ X (Bq+Tq))+inner ℝ W (Bq+Tq)) a4
      _=_ := by ring
  rw [algebra]
  have massScaled:=mul_le_mul_of_nonneg_left mass K0
  have combined : -nu*(inner ℝ L Bq+inner ℝ L Tq)+inner ℝ X (Bq+Tq)≤
      (-nu^2+epsilon)*‖L‖^2+
        (K+2*K*delta)*G+Cx/(2*delta) := by
    nlinarith only [viscous,xPair,massScaled]
  have coefficient : -nu^2+epsilon≤-(nu^2/2) := by
    dsimp only [epsilon]
    nlinarith only [sq_nonneg nu]
  have scaled:=mul_le_mul_of_nonneg_right coefficient (sq_nonneg ‖L‖)
  dsimp only [epsilon,delta] at *
  linarith only [combined,scaled]

end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
