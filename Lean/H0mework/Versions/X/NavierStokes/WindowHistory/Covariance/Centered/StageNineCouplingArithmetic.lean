import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineTransposeCoupling
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.CouplingPaid

set_option autoImplicit false
set_option maxHeartbeats 800000
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

theorem scalar_young (a b delta : ℝ) (positive : 0<delta) :
    a*b≤delta*b^2+a^2/(4*delta) := by
  have identity : delta*b^2+a^2/(4*delta)-a*b=(2*delta*b-a)^2/(4*delta) := by
    field_simp [positive.ne']
    ring
  have square : 0≤(2*delta*b-a)^2/(4*delta) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith only [identity,square]

theorem coupling_scalar (epsilon K GU GQ Ca Cc du dq mu mq a c bx tx bq tq : ℝ)
    (epsilon0 : 0<epsilon) (K0 : 0≤K)
    (graphBx : bx^2≤K*(du^2+mu^2))
    (graphTx : tx^2≤K*(du^2+mu^2))
    (graphBq : bq^2≤K*(dq^2+mq^2))
    (graphTq : tq^2≤K*(dq^2+mq^2))
    (massU : mu^2≤GU) (massQ : mq^2≤GQ)
    (ann : a^2≤(epsilon*(epsilon/(8*(K+1)))/2)*dq^2+Ca)
    (cre : c^2≤(epsilon*(epsilon/(8*(K+1)))/2)*du^2+Cc) :
    a*(bx+tx)+c*(bq+tq)≤
      epsilon*(du^2+dq^2)+
        (2*K*(epsilon/(8*(K+1))))*(GU+GQ)+
          (Ca+Cc)/(2*(epsilon/(8*(K+1)))) := by
  let delta:=epsilon/(8*(K+1))
  let eta:=epsilon*delta/2
  have delta0 : 0<delta := by dsimp only [delta]; positivity
  have y1:=scalar_young a bx delta delta0
  have y2:=scalar_young a tx delta delta0
  have y3:=scalar_young c bq delta delta0
  have y4:=scalar_young c tq delta delta0
  have young : a*(bx+tx)+c*(bq+tq)≤
      delta*(bx^2+tx^2+bq^2+tq^2)+(a^2+c^2)/(2*delta) := by
    have denom : delta ≠0:=delta0.ne'
    field_simp at y1 y2 y3 y4 ⊢
    nlinarith only [y1,y2,y3,y4]
  have graph : bx^2+tx^2+bq^2+tq^2≤
      2*K*(du^2+dq^2+mu^2+mq^2) := by
    nlinarith only [graphBx,graphTx,graphBq,graphTq]
  have graphScaled:=mul_le_mul_of_nonneg_left graph delta0.le
  have annCre : a^2+c^2≤eta*(du^2+dq^2)+Ca+Cc := by
    dsimp only [eta,delta] at *
    linarith only [ann,cre]
  have annScaled:=div_le_div_of_nonneg_right annCre (by positivity : 0≤2*delta)
  have annRead : (eta*(du^2+dq^2)+Ca+Cc)/(2*delta)=
      (eta/(2*delta))*(du^2+dq^2)+(Ca+Cc)/(2*delta) := by ring
  rw [annRead] at annScaled
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
  have costScaled:=mul_le_mul_of_nonneg_right coefficient
    (add_nonneg (sq_nonneg du) (sq_nonneg dq))
  have massScaled:=mul_le_mul_of_nonneg_left (add_le_add massU massQ)
    (mul_nonneg (mul_nonneg (by norm_num : 0≤(2:ℝ)) K0) delta0.le)
  change a*(bx+tx)+c*(bq+tq)≤
    epsilon*(du^2+dq^2)+2*K*delta*(GU+GQ)+(Ca+Cc)/(2*delta)
  nlinarith only [young,graphScaled,annScaled,costScaled,massScaled]

end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
