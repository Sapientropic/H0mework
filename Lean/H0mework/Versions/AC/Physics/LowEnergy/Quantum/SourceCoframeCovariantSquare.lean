import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCoframeCovariantAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceCoframeCovariantSquare
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoframeCore GaussCoframeKinetic GaussCoframeForm SourceCoframeSpinConnection SourceCoframeCovariantAction
open scoped ContDiff Matrix InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem spin_real (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussCoframeSpin.current a) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)).map_smul (c z : ℂ) (f z)

private theorem mixed_row (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    mixed i a c hc=(1/2 : ℂ) •
      ((multiply c hc*GaussCoframeSpin.current a)*momentum i+adjoint i*(multiply c hc*GaussCoframeSpin.current a)) := by
  change (1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply c hc*momentum i)+
    adjoint i*(multiply c hc*GaussCoframeSpin.current a))=_
  rw [←mul_assoc,(spin_real a c hc).eq]

private theorem connection_metric (i j : Fin 6) :
    connectionAction i*metricAction i j=metricAction j i*connectionAction i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change connectionFiber i z ((coefficient i j z : ℂ) • f z)=
    (coefficient j i z : ℂ) • connectionFiber i z (f z)
  rw [map_smul,coefficient_symmetric]

private theorem cross_left :
    (∑ i : Fin 6,∑ j : Fin 6,adjoint i*metricAction i j*connectionAction j)=
      (1/2 : ℂ) • (∑ i : Fin 6,adjoint i*currentRow i) := by
  simp only [mul_assoc,←Finset.mul_sum,original_connection_row,mul_smul_comm,Finset.smul_sum]
private theorem cross_right :
    (∑ i : Fin 6,∑ j : Fin 6,connectionAction i*metricAction i j*momentum j)=
      (1/2 : ℂ) • (∑ i : Fin 6,currentRow i*momentum i) := by
  simp_rw [connection_metric]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_mul,original_connection_row,smul_mul_assoc,Finset.smul_sum]

private theorem original_cross :
    (1/2 : ℂ) • (∑ i : Fin 6,adjoint i*currentRow i)+
    (1/2 : ℂ) • (∑ i : Fin 6,currentRow i*momentum i)=currentAction := by
  simp [currentAction,mixed_row,currentRow,Fin.sum_univ_succ,mul_assoc,Fin.succ,smul_add,mul_add,add_mul]
  all_goals module

/-- The original adjoint, variable metric, four mixed terms and ordered connection square are one differential operator. -/
theorem original_covariant_kinetic : covariantKinetic=kinetic+currentAction+connectionSquare := by
  have hk : (∑ i : Fin 6,∑ j : Fin 6,adjoint i*metricAction i j*momentum j)=kinetic := by
    rfl
  have he : covariantKinetic=(∑ i : Fin 6,∑ j : Fin 6,adjoint i*metricAction i j*momentum j)+
      (∑ i : Fin 6,∑ j : Fin 6,adjoint i*metricAction i j*connectionAction j)+
      (∑ i : Fin 6,∑ j : Fin 6,connectionAction i*metricAction i j*momentum j)+connectionSquare := by
    simp only [covariantKinetic,covariantAdjoint,SourceCoframeCovariantAction.covariantMomentum,
      connectionSquare,add_mul,mul_add,Finset.sum_add_distrib]
    abel
  rw [he,hk,cross_left,cross_right]
  rw [show kinetic+(1/2 : ℂ) • (∑ i : Fin 6,adjoint i*currentRow i)+
      (1/2 : ℂ) • (∑ i : Fin 6,currentRow i*momentum i)=kinetic+currentAction from by
    rw [add_assoc,original_cross]]

def residualWeight : Fin 7 → ℝ := ![-3/4,-3/4,-3/4,-3/4,-3/4,-3/4,3/4]
def spinRemainder : End := ∑ a : Fin 7,(residualWeight a : ℂ) •
  (GaussCoframeSpin.current a*multiply inverseVolume inverseVolume_smooth*GaussCoframeSpin.current a)

private theorem spin_split : (∑ a : Fin 7,spinSquare a)=spinRemainder+(-1/4 : ℂ) • rotationSquare := by
  change (∑ a : Fin 7,(spinWeight a : ℂ) •
    (GaussCoframeSpin.current a*multiply inverseVolume inverseVolume_smooth*GaussCoframeSpin.current a))=_
  norm_num [spinRemainder,rotationSquare,rotationAction,residualWeight,spinWeight,
    Fin.sum_univ_succ,Fin.succ,mul_assoc,smul_add]
  all_goals module

/-- Complete original coframe action in the same core and Number-weighted adjoint; the local signed spin residual is explicit. -/
theorem original_coframe_covariant :
    coframeAction=covariantKinetic+spinRemainder+numberShift+multiply volumePotential volumePotential_smooth := by
  rw [original_covariant_kinetic,original_connection_square]
  rw [coframeAction,spin_split]
  abel

end LowEnergy.SourceCoframeCovariantSquare
