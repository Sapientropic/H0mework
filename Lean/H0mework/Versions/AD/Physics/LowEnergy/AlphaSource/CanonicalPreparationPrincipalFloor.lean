import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarInverse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhaseBounds
open PreparationActualFactor PreparationScalarCoordinates PreparationPhaseScalar
open PreparationPhaseGuard PreparationCoordinates PreparationChartGuard
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussNativeEnergy GaussHistoryHilbert
open scoped BigOperators

theorem actual_diagonal_product_bounds (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius)
    (i : Fin 6) (diagonal : diagonalIndex i) :
    21/50 ≤ (fullCoordinates.symm z).1 i*u (coframeSlot i) ∧
      (fullCoordinates.symm z).1 i*u (coframeSlot i) ≤ 23/50 := by
  have q:=abs_le.mp (coframe_box z zbox i)
  have qi : qCenter i=1 := by unfold qCenter; exact if_pos diagonal
  rw [qi] at q
  have p:=abs_le.mp (ubox (coframeSlot i))
  have p0:=source_coframe_momentum_bounds i diagonal
  have small:=radius_small.2
  have qlower : (99/100 : ℝ)≤(fullCoordinates.symm z).1 i := by linarith
  have qupper : (fullCoordinates.symm z).1 i≤(101/100 : ℝ) := by linarith
  have plower : (17/40 : ℝ)≤u (coframeSlot i) := by linarith
  have pupper : u (coframeSlot i)≤(91/200 : ℝ) := by linarith
  constructor
  · have product:=mul_le_mul qlower plower (by norm_num)
      (by linarith : 0≤(fullCoordinates.symm z).1 i)
    norm_num at product
    linarith
  · have product:=mul_le_mul qupper pupper (by linarith : 0≤u (coframeSlot i))
      (by norm_num)
    norm_num at product
    linarith

theorem actual_coframe_polynomial_floor (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) :
    41/100 < polynomialPrincipal (fullCoordinates.symm z).1 (fun i => u (coframeSlot i)) := by
  have p0:=actual_diagonal_product_bounds z u zbox ubox 0 (by decide)
  have p2:=actual_diagonal_product_bounds z u zbox ubox 2 (by decide)
  have p5:=actual_diagonal_product_bounds z u zbox ubox 5 (by decide)
  have tail:=abs_le.mp (coframe_tail_bound z u zbox ubox unit)
  have small:=phase_radius
  have product02:=mul_le_mul p0.1 p2.1 (by norm_num)
    (by linarith : 0≤(fullCoordinates.symm z).1 0*u (coframeSlot 0))
  have product05:=mul_le_mul p0.1 p5.1 (by norm_num)
    (by linarith : 0≤(fullCoordinates.symm z).1 0*u (coframeSlot 0))
  have product25:=mul_le_mul p2.1 p5.1 (by norm_num)
    (by linarith : 0≤(fullCoordinates.symm z).1 2*u (coframeSlot 2))
  have square0:=mul_self_le_mul_self
    (by linarith : 0≤(fullCoordinates.symm z).1 0*u (coframeSlot 0)) p0.2
  have square2:=mul_self_le_mul_self
    (by linarith : 0≤(fullCoordinates.symm z).1 2*u (coframeSlot 2)) p2.2
  have square5:=mul_self_le_mul_self
    (by linarith : 0≤(fullCoordinates.symm z).1 5*u (coframeSlot 5)) p5.2
  rw [polynomial_principal_split]
  nlinarith

theorem actual_diagonal_coframe_bounds (z : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius) (i : Fin 6)
    (diagonal : diagonalIndex i) :
    99/100≤(fullCoordinates.symm z).1 i ∧ (fullCoordinates.symm z).1 i≤101/100 := by
  have q:=abs_le.mp (coframe_box z zbox i)
  have qi : qCenter i=1 := by unfold qCenter; exact if_pos diagonal
  rw [qi] at q
  constructor <;> linarith [radius_small.2]

theorem actual_volume_product_bounds (z : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius) :
    (99/100 : ℝ)^3≤volume (fullCoordinates.symm z) ∧
      volume (fullCoordinates.symm z)≤(101/100 : ℝ)^3 := by
  have q0:=actual_diagonal_coframe_bounds z zbox 0 (by decide)
  have q2:=actual_diagonal_coframe_bounds z zbox 2 (by decide)
  have q5:=actual_diagonal_coframe_bounds z zbox 5 (by decide)
  have lower02:=mul_le_mul q0.1 q2.1 (by norm_num)
    (by linarith : 0≤(fullCoordinates.symm z).1 0)
  have lower025:=mul_le_mul lower02 q5.1 (by norm_num)
    (by positivity : 0≤(fullCoordinates.symm z).1 0*(fullCoordinates.symm z).1 2)
  have upper02:=mul_le_mul q0.2 q2.2
    (by linarith : 0≤(fullCoordinates.symm z).1 2) (by norm_num)
  have upper025:=mul_le_mul upper02 q5.2
    (by linarith : 0≤(fullCoordinates.symm z).1 5) (by norm_num)
  constructor
  · change _≤(fullCoordinates.symm z).1 0*(fullCoordinates.symm z).1 2*(fullCoordinates.symm z).1 5
    nlinarith
  · change (fullCoordinates.symm z).1 0*(fullCoordinates.symm z).1 2*(fullCoordinates.symm z).1 5≤_
    nlinarith

theorem actual_volume_bounds (z : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius) :
    9/10≤volume (fullCoordinates.symm z) ∧ volume (fullCoordinates.symm z)≤21/20 := by
  have original:=actual_volume_product_bounds z zbox
  norm_num at original
  constructor <;> linarith

theorem actual_closed_phase_A_floor (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) :
    1/15 < A (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) := by
  have coframe:=actual_coframe_polynomial_floor z u zbox ubox unit
  have scalar:=actual_closed_phase_scalarNorm z u zbox ubox
  have v:=actual_volume_bounds z zbox
  have original:=A_original_numerator (phaseChart z zbox) u
  change A (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))=
    (polynomialPrincipal (fullCoordinates.symm z).1 (fun i => u (coframeSlot i))-
      2*scalarNormSquare (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)))/
      (4*volume (fullCoordinates.symm z)) at original
  rw [original]
  apply (lt_div_iff₀ (by nlinarith [v.1] : 0<4*volume (fullCoordinates.symm z))).mpr
  nlinarith [v.2]

end LowEnergy.PreparationPhaseBounds
