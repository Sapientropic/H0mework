import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarCompressionJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedResolventWard
import Lean.Elab.Term

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualMixedCompressionShape
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussUnitaryHistory SourceScalarPairedTransport SourceClockPhiSecondBulk
open SourceScalarVirialBulk SourceScalarGaugeScale SourceJointScaleBudget
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open scoped InnerProductSpace BigOperators
open Lean Meta Elab Term
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
local instance labelFintype : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _
attribute [local irreducible] compressionCore defectAction diagonalAction

elab "paid_source_compression_apply%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeCompressionCovariance 0) "LowEnergy")
    "SourceCoframeCompressionCovariance") "sourceCompression_apply")

elab "original_shape_span_core%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeCompressionCovariance 0) "LowEnergy")
    "SourceCoframeCompressionCovariance") "spanCore")

/-- The original ungraded finite-span projection, lifted to the actual smooth core. -/
def projectionCore (F : Index) : End where
  toFun f := coreEquiv.symm ⟨(FiniteCoreEvolution.coreSpan diagonal F).starProjection (embed f),
    FiniteCoreEvolution.coreSpan_le diagonal F
      ((FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto (embed f)).property⟩
  map_add' f g := by apply coreEquiv.injective; apply Subtype.ext; simp [map_add]
  map_smul' c f := by apply coreEquiv.injective; apply Subtype.ext; simp [map_smul]

theorem actual_projection_core_embed (F : Index) (f : QuantumTest) :
    embed (projectionCore F f) =
      (FiniteCoreEvolution.coreSpan diagonal F).starProjection (embed f) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- Pinching is part of the source compression and is retained before differentiation. -/
def coreCompression (F : Index) (A : End) : End :=
  ∑ g : NativeHistoryGrade.Label,
    GaussCoreLabel.project g*projectionCore F*A*projectionCore F*GaussCoreLabel.project g

theorem actual_core_compression_embed (F : Index) (A : End) (f : QuantumTest) :
    embed (coreCompression F A f)=sourceCompression F A (embed f) := by
  classical
  simp only [coreCompression,LinearMap.sum_apply,map_sum,Module.End.mul_apply,
    GaussCoreLabel.embed_project,actual_projection_core_embed]
  change (∑ g : NativeHistoryGrade.Label, NativeHistoryGrade.projection g
    ((FiniteCoreEvolution.coreSpan diagonal F).starProjection
      (embed (A (projectionCore F (GaussCoreLabel.project g f)))))) = _
  rw [(paid_source_compression_apply%) F A (embed f)]
  apply Finset.sum_congr rfl
  intro g _
  apply congrArg (fun q : QuantumTest => NativeHistoryGrade.projection g
    ((FiniteCoreEvolution.coreSpan diagonal F).starProjection (embed (A q))))
  apply embed_injective
  rw [actual_projection_core_embed,GaussCoreLabel.embed_project]
  exact (congrArg Subtype.val (coreEquiv.apply_symm_apply
    ((original_shape_span_core%) F (NativeHistoryGrade.projection g (embed f))))).symm

/-- The actual CF is the graded sum of original ungraded PHP blocks. -/
theorem actual_compression_core_identity (F : Index) :
    compressionCore F=coreCompression F diagonalAction := by
  apply LinearMap.ext
  intro f
  apply embed_injective
  rw [actual_core_compression_embed]
  have hc : embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [hc]
  exact congrArg (fun A : H →L[ℂ] H => A (embed f))
    (by simpa only [scaledCompression,source_scale_one] using (actual_compression_return F).symm)

private theorem phi_grade_zero (g : NativeHistoryGrade.Label) :
    deltaPhi (GaussCoreLabel.project g)=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change SourceScalarVirialBulk.phiEulerAction (GaussCoreLabel.project g f) z-
    GaussCoreLabel.project g (SourceScalarVirialBulk.phiEulerAction f) z=0
  rw [SourceScalarVirialBulk.phi_euler_apply,GaussCoreLabel.project_apply,
    SourceScalarVirialBulk.phi_euler_apply,GaussCoreLabel.derivative_project,sub_self]

private theorem gauge_grade_zero (g : NativeHistoryGrade.Label) :
    deltaGauge (GaussCoreLabel.project g)=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change SourceGaugeRadialPair.gaugeEulerAction (GaussCoreLabel.project g f) z-
    GaussCoreLabel.project g (SourceGaugeRadialPair.gaugeEulerAction f) z=0
  rw [SourceGaugeRadialPair.gauge_euler_apply,GaussCoreLabel.project_apply,
    SourceGaugeRadialPair.gauge_euler_apply,GaussCoreLabel.derivative_project,sub_self]

private theorem phi_product (A B : End) : deltaPhi (A*B)=deltaPhi A*B+A*deltaPhi B := by
  change SourceScalarVirialBulk.phiEulerAction*(A*B)-(A*B)*SourceScalarVirialBulk.phiEulerAction=_
  change SourceScalarVirialBulk.phiEulerAction*(A*B)-(A*B)*SourceScalarVirialBulk.phiEulerAction=
    (SourceScalarVirialBulk.phiEulerAction*A-A*SourceScalarVirialBulk.phiEulerAction)*B+
      A*(SourceScalarVirialBulk.phiEulerAction*B-B*SourceScalarVirialBulk.phiEulerAction)
  noncomm_ring
private theorem gauge_product (A B : End) : deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B := by
  change SourceGaugeRadialPair.gaugeEulerAction*(A*B)-(A*B)*SourceGaugeRadialPair.gaugeEulerAction=_
  change SourceGaugeRadialPair.gaugeEulerAction*(A*B)-(A*B)*SourceGaugeRadialPair.gaugeEulerAction=
    (SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)*B+
      A*(SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)
  noncomm_ring

/-- Difference of the same two original source derivations. -/
def differenceJet : End →ₗ[ℂ] End := deltaPhi-deltaGauge

private theorem difference_product (A B : End) :
    differenceJet (A*B)=differenceJet A*B+A*differenceJet B := by
  simp only [differenceJet,LinearMap.sub_apply,phi_product,gauge_product]
  noncomm_ring

/-- The six terms keep their original operator order. -/
def crossShape (A B C : End) : End :=
  differenceJet A*deltaGauge B*C+differenceJet A*B*deltaGauge C+
  deltaGauge A*differenceJet B*C+A*differenceJet B*deltaGauge C+
  deltaGauge A*B*differenceJet C+A*deltaGauge B*differenceJet C

private theorem second_triple (A B C : End) :
    secondJet (A*B*C)=secondJet A*B*C+A*secondJet B*C+A*B*secondJet C-crossShape A B C := by
  change differenceJet (A*B*C)-deltaGauge (differenceJet (A*B*C))=_
  have he (a : End) : secondJet a=differenceJet a-deltaGauge (differenceJet a) := rfl
  simp only [difference_product,map_add,gauge_product,he,crossShape]
  noncomm_ring

private theorem second_grade (g : NativeHistoryGrade.Label) (A : End) :
    secondJet (GaussCoreLabel.project g*A*GaussCoreLabel.project g)=
      GaussCoreLabel.project g*secondJet A*GaussCoreLabel.project g := by
  rw [second_triple]
  have hd : differenceJet (GaussCoreLabel.project g)=0 := by
    simp only [differenceJet,LinearMap.sub_apply,phi_grade_zero,gauge_grade_zero,sub_self]
  have hs : secondJet (GaussCoreLabel.project g)=0 := by
    change differenceJet (GaussCoreLabel.project g)-deltaGauge (differenceJet (GaussCoreLabel.project g))=0
    rw [hd]
    change (0 : End)-(SourceGaugeRadialPair.gaugeEulerAction*0-0*SourceGaugeRadialPair.gaugeEulerAction)=0
    simp only [mul_zero,zero_mul,sub_self]
  simp only [hs,hd,crossShape,gauge_grade_zero,zero_mul,mul_zero,zero_add,add_zero,sub_zero]

/-- All projection-side terms, including both second jets and six ordered crosses. -/
def wholeShape (F : Index) : End :=
  ∑ g : NativeHistoryGrade.Label, GaussCoreLabel.project g*
    (secondJet (projectionCore F)*diagonalAction*projectionCore F+
      projectionCore F*diagonalAction*secondJet (projectionCore F)-
      crossShape (projectionCore F) diagonalAction (projectionCore F))*GaussCoreLabel.project g

/-- Actual graded CF, with no projection-factorization or shape premise. -/
theorem actual_second_compression_shape (F : Index) :
    secondJet (compressionCore F)=coreCompression F (secondJet diagonalAction)+wholeShape F := by
  classical
  rw [actual_compression_core_identity]
  simp only [coreCompression,map_sum]
  simp_rw [show ∀ g : NativeHistoryGrade.Label,
      secondJet (GaussCoreLabel.project g*projectionCore F*diagonalAction*projectionCore F*
        GaussCoreLabel.project g)=GaussCoreLabel.project g*
          secondJet (projectionCore F*diagonalAction*projectionCore F)*GaussCoreLabel.project g
    from fun g => by simpa only [mul_assoc] using second_grade g (projectionCore F*diagonalAction*projectionCore F)]
  simp only [wholeShape,second_triple,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  noncomm_ring

/-- The actual OwnDefect retains its uncompressed gap and the complete graded shape. -/
theorem actual_second_defect_shape (F : Index) :
    secondJet (defectAction F)=secondJet diagonalAction-
      coreCompression F (secondJet diagonalAction)-wholeShape F := by
  rw [defectAction,map_sub,actual_second_compression_shape]
  abel

end LowEnergy.ActualMixedCompressionShape
