import H0mework.Versions.Rdf421ff6.Physics.LowEnergy.Quantum.SourceJointScaleBudget
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeVolumeCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceMixedNativeReturn
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolumeCurrent SourceJointScaleBudget SourceEscapeCurrent FullYSourceResolventGraphSplice
def coreRead (F : Index) (g : diagonal.domain) (A : CoreEnd) : H →L[ℂ] H :=
  ((embed.comp (A.comp (coreEquiv.symm.toLinearMap.comp
    (Submodule.inclusion (input_span_core F g))))).toContinuousLinearMap).comp
      (inputSpan F g).orthogonalProjectionOnto

private theorem core_read_add (F : Index) (g : diagonal.domain) (A B : CoreEnd) :
    coreRead F g (A+B)=coreRead F g A+coreRead F g B := by
  apply ContinuousLinearMap.ext
  intro x
  change embed ((A+B) _)=embed (A _)+embed (B _)
  exact map_add embed _ _

private theorem core_read_smul (F : Index) (g : diagonal.domain) (c : ℂ) (A : CoreEnd) :
    coreRead F g (c • A)=c • coreRead F g A := by
  apply ContinuousLinearMap.ext
  intro x
  exact map_smul embed c _

def sourceRead (F : Index) (g : diagonal.domain) : CoreEnd →ₗ[ℂ] H →L[ℂ] H where
  toFun := coreRead F g
  map_add' := core_read_add F g
  map_smul' := core_read_smul F g

theorem source_read_resolvent (F : Index) (g : diagonal.domain) (A : CoreEnd)
    (z : ℂ) (hz : z.im≠0) :
    sourceRead F g A (finiteResolvent F z (g : H))=
      embed (A (coreEquiv.symm (sourceCore F z hz g))) := by
  have hp := (inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨finiteResolvent F z (g : H),resolvent_input_span F z hz g⟩
  change embed (A (coreEquiv.symm
    (Submodule.inclusion (input_span_core F g)
      ((inputSpan F g).orthogonalProjectionOnto (finiteResolvent F z (g : H))))))=_
  rw [hp]
  rfl

end LowEnergy.SourceMixedNativeReturn
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
namespace LowEnergy.SourceScalarPositiveBulkWard
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceEscapeCurrent FullYSourceResolventGraphSplice
def state (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  coreEquiv.symm (sourceCore F z hz g)

end LowEnergy.SourceScalarPositiveBulkWard
