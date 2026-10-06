import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedGamma
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialJoinedCross
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialCoefficient
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaCubicCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialMixedCore
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceClockYukawaTail SourceCutoffDilationWard
open SourceClockYukawaHamiltonianCurrent SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent
open SourceClockYukawaCubicCurrent SourceClockYukawaRadialJoinedCross
open SourceRelativePowerTail SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] inverseRadius fullAction state compressionCore defectAction
  finiteResolvent GaussGradedCompression.compression actualIncrement resolventCore
  GaussMatterCore.matterAction diagonalAction

/-- The scalar70 current is already joined before it meets either moving radial response. -/
def nativeCutoffCurrent (sharp : Bool) (m ell : ℕ) : End := (-Complex.I/2:ℂ) • ∑ a : ScalarIndex,
  (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
      PositiveScalarWeakBudget.coefficient sharp a m ell+
    PositiveScalarWeakBudget.coefficient sharp a m ell*multiply scalarWeight scalarWeight_smooth*
      covariantMomentum (scalarDirection a))

def sourceCutoffCurrent (sharp : Bool) (m ell : ℕ) : End :=
  (bracket GaussMatterCore.matterAction (fullAction sharp)+reducedSpinCurrent sharp)*thetaAction m ell+
    nativeCutoffCurrent sharp m ell

def correctedCutoffCore (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  sourceCutoffCurrent sharp m ell-bracket (defectAction F) (literalIncrementAction sharp m ell)

def correctedJoinedCore (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  joinedCore sharp m ell-
    bracket (bracket (defectAction F) inverseAction) (literalIncrementAction sharp m ell)

def sourceMixedResponse (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  let R := resolventCore F z hz
  let K := SourceRadiusResponseDecay.radialCurrent F
  let J := correctedCutoffCore sharp m ell F
  R*J*R*K*R+R*K*R*J*R-R*correctedJoinedCore sharp m ell F*R

private theorem bracket_product {A : Type*} [Ring A] (X Y Z : A) :
    bracket X (Y*Z)=bracket X Y*Z+Y*bracket X Z := by unfold bracket;noncomm_ring

private theorem source_cutoff_current (sharp : Bool) (m ell : ℕ) :
    bracket diagonalAction (literalIncrementAction sharp m ell)=sourceCutoffCurrent sharp m ell := by
  have hθ : bracket diagonalAction (thetaAction m ell)=SourceInverseNeutralScalarCurrent.radialCurrent m ell :=
    SourceScalarRadialContact.original_hamiltonian_radial_contact m ell
  rw [literal_full_return,bracket_product,original_hamiltonian_yukawa_current,hθ]
  have h := PositiveScalarWeakBudget.original_scalar_two_leg_join sharp m ell
  change scalarCurrent sharp*thetaAction m ell+fullAction sharp*SourceInverseNeutralScalarCurrent.radialCurrent m ell=
    nativeCutoffCurrent sharp m ell at h
  unfold sourceCutoffCurrent originalCurrent
  simp only [add_mul]
  linear_combination (norm := module) h

private theorem corrected_cutoff_current (sharp : Bool) (m ell : ℕ) (F : Index) :
    bracket (compressionCore F) (literalIncrementAction sharp m ell)=correctedCutoffCore sharp m ell F := by
  have h := source_cutoff_current sharp m ell
  unfold correctedCutoffCore defectAction bracket at *
  linear_combination (norm := noncomm_ring) h

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem radial_current_embed (F : Index) (f : QuantumTest) :
    SourceClockYukawaRadialMixedGamma.radialCurrent F (embed f)=
      embed (SourceRadiusResponseDecay.radialCurrent F f) := by
  rw [SourceRadiusResponseDecay.original_radial_current]
  simp only [SourceClockYukawaRadialMixedGamma.radialCurrent,sub_apply,mul_apply_eq_comp,
    LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←inverse_core]

/-- The actual full cutoff current consumes joined native Z, all signed spin and matter,
then the complete compression defect at the same original F. -/
theorem actual_cutoff_current_source (sharp : Bool) (m ell : ℕ) (F : Index) (f : QuantumTest) :
    SourceClockYukawaRadialMixedGamma.cutoffCurrent sharp m ell F (embed f)=
      embed (correctedCutoffCore sharp m ell F f) := by
  rw [←corrected_cutoff_current]
  simp only [SourceClockYukawaRadialMixedGamma.cutoffCurrent,sub_apply,mul_apply_eq_comp,
    bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←literal_increment_core]

/-- The complete mixed compression curvature is the source radial contraction of Z
and its full same-F double defect. -/
theorem actual_mixed_curvature_source (sharp : Bool) (m ell : ℕ) (F : Index) (f : QuantumTest) :
    SourceClockYukawaRadialMixedGamma.mixedCurvature sharp m ell F (embed f)=
      embed (correctedJoinedCore sharp m ell F f) := by
  have h := actual_corrected_radial_joined_yukawa_cross sharp m ell F
  rw [←literal_full_return] at h
  change bracket (SourceRadiusResponseDecay.radialCurrent F) (literalIncrementAction sharp m ell)=
    correctedJoinedCore sharp m ell F at h
  rw [←h]
  simp only [SourceClockYukawaRadialMixedGamma.mixedCurvature,sub_apply,mul_apply_eq_comp,
    bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub,←literal_increment_core,←radial_current_embed]

/-- This is the actual mixed word consumed by the original Gamma operator identity;
each native coefficient and each full defect remains inside its original current. -/
theorem actual_mixed_response_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (f : QuantumTest) :
    SourceClockYukawaRadialMixedGamma.mixedResponse sharp m ell F z (embed f)=
      embed (sourceMixedResponse sharp m ell F z hz f) := by
  simp only [SourceClockYukawaRadialMixedGamma.mixedResponse,sourceMixedResponse,add_apply,sub_apply,mul_apply_eq_comp,
    LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,map_add,map_sub,resolvent_embed,
    ←actual_cutoff_current_source,←actual_mixed_curvature_source,←radial_current_embed]

end LowEnergy.SourceClockYukawaRadialMixedCore
