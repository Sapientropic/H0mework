import H0mework.Physics.LowEnergy.PacketDynamics.AdjointFlow

/-! Finite products and sums retain the actual whole-space Fourier multiplier before graph equations are consumed. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace
noncomputable section

def HasSymbol (action : FullMatterL2 →L[ℂ] FullMatterL2) (matrix : Position → FiberOperators) : Prop :=
  ∀ field, fourier (action field) =ᵐ[volume] fun frequency => matrix frequency (fourier field frequency)

theorem HasSymbol.comp {first second : FullMatterL2 →L[ℂ] FullMatterL2}
    {firstMatrix secondMatrix : Position → FiberOperators}
    (left : HasSymbol first firstMatrix) (right : HasSymbol second secondMatrix) :
    HasSymbol (first.comp second) (fun frequency => firstMatrix frequency*secondMatrix frequency) := by
  intro field
  filter_upwards [left (second field),right field] with frequency outer inner
  exact outer.trans (congrArg (firstMatrix frequency) inner)

theorem HasSymbol.sub {first second : FullMatterL2 →L[ℂ] FullMatterL2}
    {firstMatrix secondMatrix : Position → FiberOperators}
    (left : HasSymbol first firstMatrix) (right : HasSymbol second secondMatrix) :
    HasSymbol (first-second) (fun frequency => firstMatrix frequency-secondMatrix frequency) := by
  intro field
  change fourier (first field-second field) =ᵐ[volume] _
  rw [map_sub]
  filter_upwards [left field,right field,Lp.coeFn_sub (fourier (first field)) (fourier (second field))]
    with frequency firstAt secondAt difference
  rw [difference]
  simp only [Pi.sub_apply,firstAt,secondAt]
  rfl

theorem HasSymbol.smul {action : FullMatterL2 →L[ℂ] FullMatterL2} {matrix : Position → FiberOperators}
    (original : HasSymbol action matrix) (scalar : ℂ) :
    HasSymbol (scalar • action) (fun frequency => scalar • matrix frequency) := by
  intro field
  change fourier (scalar • action field) =ᵐ[volume] _
  rw [map_smul]
  filter_upwards [original field,Lp.coeFn_smul scalar (fourier (action field))] with frequency actionAt scaled
  rw [scaled]
  simp only [Pi.smul_apply,actionAt]
  rfl

theorem constant_symbol (matrix : FiberOperators) :
    HasSymbol (matrix.compLpL 2 volume) (fun _ => matrix) := by
  intro field
  rw [GaugeGreen.constant_fourier]
  exact matrix.coeFn_compLpL (fourier field)

theorem adjointFlow_symbol (time : ℝ) : HasSymbol (adjointFlow time) (adjointMatrices time) := by
  intro field
  rw [adjointFlow_fourier]
  exact adjointMomentumFlow_ae time (fourier field)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
