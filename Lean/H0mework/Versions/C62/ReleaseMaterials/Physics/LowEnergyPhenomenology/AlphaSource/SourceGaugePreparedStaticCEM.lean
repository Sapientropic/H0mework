import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaugeSpatialChannelExpansion

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalGaugePreparedStaticCEM
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalGaugeSpatialChannelExpansion
open PreparationPhysicalCommonObservableUnits
open PreparationPhysicalCommonCurrentStaticRead
open PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalActualLegNormalization
open CanonicalGradedSpatialSource
open PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalFeedback
open PreparationVacuumElectromagneticIdentity
open PreparationVacuumSoftPoleSelection
open Stage10
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

/-! This file makes the actual Coulomb coefficient explicit.  It consumes the
same actual charged source field and detector as the directional channel
producer.  The prepared-leg/static-residue and full-light/contact bridges stay
separate until their source-native equations are proved. -/

/-- The raw coefficient multiplying the normalized static Coulomb read by the
source action/clock product.  It is a source object, not an experimental input. -/
def sourceGaugeStaticCEM (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum) : ℂ :=
  ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ) *
    sourceGaugeStaticCouplingTensor branch qd q dSL dEL dSR dER sL eL sR eR T n

/-- The corresponding dimensionless source read, with the same denominator
appearing exactly once. -/
def sourceGaugeStaticAlpha (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum) : ℂ :=
  (((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)⁻¹) *
    sourceGaugeStaticCEM branch qd q dSL dEL dSR dER sL eL sR eR T n

/-- Direct source generation of the complete detector coefficient, including
all actual pair weights and the independent full-field leg correction. -/
theorem sourceGaugeStaticCEM_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (left : qd.z.im≠0) (right : qd.w.im≠0) :
    sourceGaugeStaticCEM branch qd q dSL dEL dSR dER sL eL sR eR T n =
      ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ) *
        (sourceActualLegNormalization qd dSL dEL dSR dER *
          ((∑a : RestStateIndex, ∑b : RestStateIndex,
            sourceActualPreparedWeight 0 0 sL eL sR eR a b *
              sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
                (sourceCommonCoulombTensor q n a b)) -
            sourceActualLegCorrection qd dSL dEL dSR dER
              (sourceActualPreparedKernel qd 0 0 0 T
                (sourceGaugeActualCoulombField q sL eL sR eR n))) /
          ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)) := by
  unfold sourceGaugeStaticCEM
  rw [sourceGaugeStaticCoupling_return branch qd q dSL dEL dSR dER sL eL sR eR T n left right]

/-- The same raw coefficient after the strict three-channel expansion.  All 64
prepared pair weights, the three signed channels, and the complete correction
remain visible in the consumer expression. -/
theorem sourceGaugeStaticCEM_channels (branch : Fin 2)
    (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (left : qd.z.im≠0) (right : qd.w.im≠0) :
    sourceGaugeStaticCEM branch qd q dSL dEL dSR dER sL eL sR eR T n =
      ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ) *
        (sourceActualLegNormalization qd dSL dEL dSR dER *
          ((∑a : RestStateIndex, ∑b : RestStateIndex,
            sourceActualPreparedWeight 0 0 sL eL sR eR a b *
              (sourceObservableChannel q n a b 0 *
                  sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
                    (sourceCommonOriginColumn 0) +
               sourceObservableChannel q n a b 1 *
                  sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
                    (nativeBranchVector 0) +
               sourceObservableChannel q n a b 2 *
                  sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
                    (nativeBranchVector 1))) -
            sourceActualLegCorrection qd dSL dEL dSR dER
              (sourceActualPreparedKernel qd 0 0 0 T
                (sourceGaugeActualCoulombField q sL eL sR eR n))) /
          ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)) := by
  unfold sourceGaugeStaticCEM
  rw [sourceGaugeStaticCouplingTensor_channels branch qd q dSL dEL dSR dER sL eL sR eR T n
    left right]

theorem sourceGaugeStaticAlpha_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum) :
    sourceGaugeStaticAlpha branch qd q dSL dEL dSR dER sL eL sR eR T n =
      sourceGaugeStaticCouplingTensor branch qd q dSL dEL dSR dER sL eL sR eR T n := by
  unfold sourceGaugeStaticAlpha sourceGaugeStaticCEM
  have h : ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (mul_pos ActionNormalization.phaseMomentum_positive (sourceSpeed_positive branch)).ne'
  field_simp [h]

/-- The coefficient is independent of positive radial rescaling of the physical
direction.  This is the momentum-space Coulomb read; it does not yet assert the
prepared Thomson/static-residue identity. -/
theorem sourceGaugeStaticCEM_radial (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (r : ℝ) (positive : 0<r) :
    sourceGaugeStaticCEM branch qd q dSL dEL dSR dER sL eL sR eR T (r • n) =
      sourceGaugeStaticCEM branch qd q dSL dEL dSR dER sL eL sR eR T n := by
  unfold sourceGaugeStaticCEM
  rw [sourceGaugeStaticCoupling_radial branch qd q dSL dEL dSR dER sL eL sR eR T n r positive]

theorem sourceGaugeStaticAlpha_radial (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (r : ℝ) (positive : 0<r) :
    sourceGaugeStaticAlpha branch qd q dSL dEL dSR dER sL eL sR eR T (r • n) =
      sourceGaugeStaticAlpha branch qd q dSL dEL dSR dER sL eL sR eR T n := by
  unfold sourceGaugeStaticAlpha
  rw [sourceGaugeStaticCEM_radial branch qd q dSL dEL dSR dER sL eL sR eR T n r positive]

end LowEnergy.PreparationPhysicalGaugePreparedStaticCEM
