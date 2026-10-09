import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeBulk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section
namespace LowEnergy.SourceScalarInverseRetardedBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare
open SourceHamiltonianVolume SourceScalarInverseBulk SourceScalarPairedTransport
open SourceMixedNativeReturn SourceJointScaleBudget FullYSourceResolventGraphSplice
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H

private theorem volume_right : volumeAction*inverseVolumeAction=(1 : End) :=
  LinearMap.ext volume_inverse
private theorem volume_left : inverseVolumeAction*volumeAction=(1 : End) :=
  (real_volume _ _).eq.trans volume_right

/-- The original coframe current changes sign and keeps both inverse-volume factors. -/
theorem original_inverse_current :
    diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction=
      (3*Complex.I*(sourceTime 0 : ℂ)/4) •
        (inverseVolumeAction*dilation*inverseVolumeAction) := by
  rw [InverseVolumeWardAlgebra.inverse_commutator diagonalAction volumeAction inverseVolumeAction
    volume_right volume_left,full_source_volume_current]
  simp only [mul_smul_comm,smul_mul_assoc]
  module

abbrev theta (m ell : ℕ) : End := SourceNativeCutoffContact.thetaAction m ell
def square (m ell : ℕ) : End := theta m ell*theta m ell
def inverseCutoff (m ell : ℕ) : End := inverseVolumeAction*square m ell
def symmetricCutoff (m ell : ℕ) : End :=
  (1/2 : ℂ) • (inverseSymmetricScale*square m ell+square m ell*inverseSymmetricScale)

private theorem theta_inverse (m ell : ℕ) : Commute (theta m ell) inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (SourceNativeCutoffContact.theta m ell z : ℂ) (reciprocalVolume z : ℂ) (f z)

private theorem dilation_radial : Commute dilation GaussRadialDomain.inverseAction := by
  unfold dilation
  apply Commute.smul_left
  apply Commute.sum_left
  intro i _
  have hC : Commute (coordinateAction i) GaussRadialDomain.inverseAction :=
    GaussRadialHamiltonian.real_commutes _ _
  exact ((GaussRadialHamiltonian.coframe_adjoint i).mul_left hC).add_left
    (hC.mul_left (GaussRadialHamiltonian.coframe_momentum i))

private theorem dilation_theta (m ell : ℕ) : Commute dilation (theta m ell) := by
  rw [show theta m ell=(1-GaussRadialDomain.inverseAction)^(m+1)-
      (1-GaussRadialDomain.inverseAction)^(ell+1) from
    SourceNativeCutoffContact.theta_action_polynomial m ell]
  exact (((Commute.one_right dilation).sub_right dilation_radial).pow_right (m+1)).sub_right
    (((Commute.one_right dilation).sub_right dilation_radial).pow_right (ell+1))

private theorem square_inverse (m ell : ℕ) : Commute (square m ell) inverseVolumeAction :=
  (theta_inverse m ell).mul_left (theta_inverse m ell)

private theorem inverse_current_square (m ell : ℕ) :
    Commute (diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction) (square m ell) := by
  rw [original_inverse_current]
  have hV := (square_inverse m ell).symm
  have hD := (dilation_theta m ell).mul_right (dilation_theta m ell)
  exact ((hV.mul_left hD).mul_left hV).smul_left _

/-- The complete two one-sided inverse actions have one common anticommutator carrier. -/
theorem original_inverse_cutoff_average (m ell : ℕ) :
    symmetricCutoff m ell=(1/2 : ℂ) •
      (diagonalAction*inverseCutoff m ell+inverseCutoff m ell*diagonalAction) := by
  have hV := (square_inverse m ell).eq
  have hK := (inverse_current_square m ell).eq
  have hVH := congrArg (fun A : End => A*diagonalAction) hV
  simp only [sub_mul,mul_sub,mul_assoc] at hK hVH
  have hS : square m ell*(diagonalAction*inverseVolumeAction)=
      diagonalAction*(inverseVolumeAction*square m ell)-
        inverseVolumeAction*(diagonalAction*square m ell)+
        square m ell*(inverseVolumeAction*diagonalAction) := by
    linear_combination (norm := module) -hK
  dsimp [symmetricCutoff,inverseSymmetricScale,inverseCutoff]
  simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add,mul_assoc]
  rw [hS,hVH]
  module

private def inputTest (F : Index) (g : diagonal.domain) (x : H) : QuantumTest :=
  coreEquiv.symm (Submodule.inclusion (input_span_core F g) ((inputSpan F g).orthogonalProjectionOnto x))
private theorem input_embed (F : Index) (g : diagonal.domain) (x : H) :
    embed (inputTest F g x)=((inputSpan F g).orthogonalProjectionOnto x : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_input (F : Index) (g : diagonal.domain) (x : H) :
    GaussGradedCompression.compression F ((inputSpan F g).orthogonalProjectionOnto x : H)=
      GaussGradedCompression.compression F x := by
  apply ext_inner_left ℂ
  intro y
  have hy : GaussGradedCompression.compression F y∈inputSpan F g :=
    Submodule.mem_sup_left (SourceRetardedIncrement.compression_mem_support F y)
  exact (GaussGradedCompression.compression_pair F y _).symm.trans
    ((Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨GaussGradedCompression.compression F y,hy⟩ x).trans (GaussGradedCompression.compression_pair F y x))
private theorem input_compression (F : Index) (g : diagonal.domain) (x : H) :
    embed (inputTest F g (GaussGradedCompression.compression F x))=GaussGradedCompression.compression F x := by
  rw [input_embed]
  exact congrArg Subtype.val ((inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨GaussGradedCompression.compression F x,Submodule.mem_sup_left (SourceRetardedIncrement.compression_mem_support F x)⟩)
private theorem compression_core (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem read_compression_left (F : Index) (g : diagonal.domain) (A : End) :
    sourceRead F g (compressionCore F*A)=GaussGradedCompression.compression F*sourceRead F g A := by
  apply ContinuousLinearMap.ext
  intro x
  exact compression_core F (A (inputTest F g x))
private theorem read_compression_right (F : Index) (g : diagonal.domain) (A : End) :
    sourceRead F g (A*compressionCore F)=sourceRead F g A*GaussGradedCompression.compression F := by
  apply ContinuousLinearMap.ext
  intro x
  have he : compressionCore F (inputTest F g x)=inputTest F g (GaussGradedCompression.compression F x) := by
    apply embed_injective
    exact (compression_core F _).trans ((congrArg (GaussGradedCompression.compression F) (input_embed F g x)).trans
      ((compression_input F g x).trans (input_compression F g x).symm))
  exact congrArg (fun f : QuantumTest => embed (A f)) he

/-- Both original projection defects act on the same inverse-weighted cutoff. -/
def projectionFlux (m ell : ℕ) (F : Index) (g : diagonal.domain) : Op :=
  (1/2 : ℂ) • sourceRead F g
    (defectAction F*inverseCutoff m ell+inverseCutoff m ell*defectAction F)

theorem actual_inverse_cutoff_compression (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    sourceRead F g (symmetricCutoff m ell)=
      (1/2 : ℂ) • (GaussGradedCompression.compression F*sourceRead F g (inverseCutoff m ell)+
        sourceRead F g (inverseCutoff m ell)*GaussGradedCompression.compression F)+
      projectionFlux m ell F g := by
  have hs : symmetricCutoff m ell=
      (1/2 : ℂ) • (compressionCore F*inverseCutoff m ell+inverseCutoff m ell*compressionCore F)+
      (1/2 : ℂ) • (defectAction F*inverseCutoff m ell+inverseCutoff m ell*defectAction F) := by
    rw [original_inverse_cutoff_average,defectAction]
    simp only [sub_mul,mul_sub]
    module
  have h := congrArg (sourceRead F g) hs
  simpa only [map_add,map_smul,read_compression_left,read_compression_right,projectionFlux] using! h

private theorem anticommutator_retarded {R : Type*} [Ring R] [Algebra ℂ R]
    (C A r Q P : R) (z : ℂ) (hl : r*(C-z • 1)=1) (hr : (C-z • 1)*r=1)
    (hq : Q=(1/2 : ℂ) • (C*A+A*C)+P) :
    r*Q*r=(1/2 : ℂ) • (A*r+r*A)+z • (r*A*r)+r*P*r := by
  have hL : r*C=1+z • r := by
    rw [mul_sub,mul_smul_comm,mul_one] at hl
    exact sub_eq_iff_eq_add.mp hl
  have hR : C*r=1+z • r := by
    rw [sub_mul,smul_mul_assoc,one_mul] at hr
    exact sub_eq_iff_eq_add.mp hr
  rw [hq,mul_add,add_mul]
  have he : r*((1/2 : ℂ) • (C*A+A*C))*r=
      (1/2 : ℂ) • ((r*C)*A*r+r*A*(C*r)) := by
    simp only [mul_smul_comm,smul_mul_assoc,mul_add,add_mul,mul_assoc]
  rw [he,hL,hR]
  simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm]
  module

/-- The actual symmetric one-sided average retains the full complex frequency and both d_F legs. -/
theorem actual_inverse_cutoff_retarded (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z*sourceRead F g (symmetricCutoff m ell)*finiteResolvent F z=
      (1/2 : ℂ) • (sourceRead F g (inverseCutoff m ell)*finiteResolvent F z+
        finiteResolvent F z*sourceRead F g (inverseCutoff m ell))+
      z • (finiteResolvent F z*sourceRead F g (inverseCutoff m ell)*finiteResolvent F z)+
      finiteResolvent F z*projectionFlux m ell F g*finiteResolvent F z :=
  anticommutator_retarded (GaussGradedCompression.compression F)
    (sourceRead F g (inverseCutoff m ell)) (finiteResolvent F z)
    (sourceRead F g (symmetricCutoff m ell)) (projectionFlux m ell F g) z
    (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
    (actual_inverse_cutoff_compression m ell F g)

end LowEnergy.SourceScalarInverseRetardedBudget
