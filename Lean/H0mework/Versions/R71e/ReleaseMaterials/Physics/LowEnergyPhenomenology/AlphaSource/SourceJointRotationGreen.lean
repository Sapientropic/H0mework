import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRotationAction

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalJointRotationCharge
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair Stage10
open DiracExteriorMatterAction YangMills.FullPairing FullQuantum FullSpace FullQuantum.Triangular
open PreparationPhysicalFilteredLockedChargeReturn PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationVacuumElectromagneticIdentity
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators Matrix Matrix.Norms.L2Operator SchwartzMap FourierTransform

private theorem embedded_injective : Function.Injective (fun v : Source.Index→ℂ=>naturalCoordinates (embed v)) := by
  intro a b same
  have original:=naturalCoordinates.injective same
  have read:=congrArg coordinates original
  simpa only [coordinates_embed] using read

private theorem dirac_embed (p : Fin 3→ℝ) (v : Source.Index→ℂ) :
    sourceLockedDiracMatrix p (naturalCoordinates (embed v))=
      naturalCoordinates (embed (sourceDiracMatrix p (Retarded.spectralParameter 0 1)*ᵥv)) := by
  rw [sourceLockedDiracMatrix,operator_coordinates,sourceDiracMatrix_original]

private theorem dirac_injective (p : Fin 3→ℝ) : Function.Injective (sourceLockedDiracMatrix p) := by
  apply Function.LeftInverse.injective (g:=Retarded.diracValue 0 p 0 1)
  intro v
  have inverse:=DFunLike.congr_fun (Retarded.diracValue_two_sided 0 p 0 1 (by norm_num)).2 v
  simpa only [mul_apply_eq_comp,one_apply_eq_self,sourceLockedDiracMatrix] using inverse

private theorem source_dirac_surjective (p : Fin 3→ℝ) :
    Function.Surjective (Matrix.mulVecLin (sourceDiracMatrix p (Retarded.spectralParameter 0 1))) := by
  apply LinearMap.surjective_of_injective
  intro a b same
  apply embedded_injective
  apply dirac_injective p
  rw [dirac_embed,dirac_embed]
  exact congrArg (fun v=>naturalCoordinates (embed v)) same

/-- Coordinates are read from the actual full Dirac Green, not from a replacement inverse. -/
def sourceGreenCoordinates (p : Fin 3→ℝ) (v : Source.Index→ℂ) : Source.Index→ℂ :=
  coordinates (naturalCoordinates.symm (Retarded.diracValue 0 p 0 1 (naturalCoordinates (embed v))))

/-- Finite source invariance follows from full Dirac invertibility and its actual invariant carrier. -/
theorem sourceGreenCoordinates_original (p : Fin 3→ℝ) (v : Source.Index→ℂ) :
    Retarded.diracValue 0 p 0 1 (naturalCoordinates (embed v))=
      naturalCoordinates (embed (sourceGreenCoordinates p v)) := by
  obtain ⟨u,solved⟩:=source_dirac_surjective p v
  change sourceDiracMatrix p (Retarded.spectralParameter 0 1)*ᵥu=v at solved
  have returned : Retarded.diracValue 0 p 0 1 (naturalCoordinates (embed v))=naturalCoordinates (embed u) := by
    rw [←solved,←dirac_embed]
    have inverse:=DFunLike.congr_fun (Retarded.diracValue_two_sided 0 p 0 1 (by norm_num)).2
      (naturalCoordinates (embed u))
    simpa only [mul_apply_eq_comp,one_apply_eq_self,sourceLockedDiracMatrix] using inverse
  have read : sourceGreenCoordinates p v=u := by
    rw [sourceGreenCoordinates,returned,naturalCoordinates.symm_apply_apply,coordinates_embed]
  rw [read,returned]

theorem sourceGreenCoordinates_equation (p : Fin 3→ℝ) (v : Source.Index→ℂ) :
    sourceDiracMatrix p (Retarded.spectralParameter 0 1)*ᵥsourceGreenCoordinates p v=v := by
  apply embedded_injective
  dsimp only
  rw [←dirac_embed,←sourceGreenCoordinates_original]
  have inverse:=DFunLike.congr_fun (Retarded.diracValue_two_sided 0 p 0 1 (by norm_num)).1
    (naturalCoordinates (embed v))
  simpa only [mul_apply_eq_comp,one_apply_eq_self,sourceLockedDiracMatrix] using inverse

/-- The actual full Green transports the same finite joint rotation and spatial momentum together. -/
theorem sourceJointGreen_covariance (theta : ℝ) (p : Fin 3→ℝ) (v : Source.Index→ℂ) :
    Retarded.diracValue 0 (sourceRotatedMomentum theta p) 0 1
      (naturalCoordinates (embed (sourceInternalRotation theta*ᵥv)))=
      naturalCoordinates (embed (sourceInternalRotation theta*ᵥsourceGreenCoordinates p v)) := by
  apply dirac_injective (sourceRotatedMomentum theta p)
  have inverse:=DFunLike.congr_fun
    (Retarded.diracValue_two_sided 0 (sourceRotatedMomentum theta p) 0 1 (by norm_num)).1
      (naturalCoordinates (embed (sourceInternalRotation theta*ᵥv)))
  change sourceLockedDiracMatrix (sourceRotatedMomentum theta p)
      (Retarded.diracValue 0 (sourceRotatedMomentum theta p) 0 1
        (naturalCoordinates (embed (sourceInternalRotation theta*ᵥv))))=_
  rw [show sourceLockedDiracMatrix (sourceRotatedMomentum theta p)
      (Retarded.diracValue 0 (sourceRotatedMomentum theta p) 0 1
        (naturalCoordinates (embed (sourceInternalRotation theta*ᵥv))))=
      naturalCoordinates (embed (sourceInternalRotation theta*ᵥv)) from
        by simpa only [mul_apply_eq_comp,one_apply_eq_self,sourceLockedDiracMatrix] using inverse]
  rw [dirac_embed,Matrix.mulVec_mulVec,sourceJointDirac_covariance,←Matrix.mulVec_mulVec,
    sourceGreenCoordinates_equation]

/-- The spatial part is the actual Euclidean rotation, so it preserves the source unit ball and volume. -/
def sourceSpatialRotation (theta : ℝ) : Position≃ₗᵢ[ℝ] Position where
  toFun x:=WithLp.toLp 2 (sourceRotatedMomentum theta x)
  invFun x:=WithLp.toLp 2 (sourceRotatedMomentum (-theta) x)
  left_inv x:=by
    ext j
    change sourceRotatedMomentum (-theta) (sourceRotatedMomentum theta x) j=x j
    rw [sourceRotatedMomentum_add,neg_add_cancel,sourceRotatedMomentum_zero]
  right_inv x:=by
    ext j
    change sourceRotatedMomentum theta (sourceRotatedMomentum (-theta) x) j=x j
    rw [sourceRotatedMomentum_add,add_neg_cancel,sourceRotatedMomentum_zero]
  map_add' x y:=by
    ext j
    fin_cases j <;> simp [sourceRotatedMomentum,Matrix.cons_val_two,PiLp.add_apply] <;> ring
  map_smul' c x:=by
    ext j
    fin_cases j <;> simp [sourceRotatedMomentum,Matrix.cons_val_two,PiLp.smul_apply] <;> ring
  norm_map' x:=by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.real_norm_sq_eq]
    exact sourceRotatedMomentum_square theta x

def sourceSpatialPull (theta : ℝ) : FullMatterL2→L[ℂ] FullMatterL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (sourceSpatialRotation theta)
    (sourceSpatialRotation theta).measurePreserving).toContinuousLinearMap

/-- The original physical preparation itself supplies radiality; no new envelope is chosen. -/
theorem sourceOriginalPacket_rotated (theta : ℝ) (v : Hilbert) :
    sourceSpatialPull theta (HistoryPrepared.preparation v)=HistoryPrepared.preparation v := by
  classical
  have changed:=(sourceSpatialRotation theta).measurePreserving.quasiMeasurePreserving.ae
    (PreparationVacuumActualSpatialPacket.sourcePacketShape_original v)
  have shape:=(sourceSpatialRotation theta).measurePreserving.quasiMeasurePreserving.ae
    PreparationVacuumActualSpatialPacket.sourcePacketShape_ae
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (HistoryPrepared.preparation v)
      (sourceSpatialRotation theta).measurePreserving,changed,shape,
    PreparationVacuumActualSpatialPacket.sourcePacketShape_original v,
    PreparationVacuumActualSpatialPacket.sourcePacketShape_ae] with x pulled rotated scalar original scalarOriginal
  change Lp.compMeasurePreserving (sourceSpatialRotation theta)
    (sourceSpatialRotation theta).measurePreserving (HistoryPrepared.preparation v) x=_
  rw [pulled]
  change HistoryPrepared.preparation v (sourceSpatialRotation theta x)=_
  rw [rotated,scalar,original,scalarOriginal]
  have ball : sourceSpatialRotation theta x∈Metric.ball (0:Position) 1 ↔ x∈Metric.ball (0:Position) 1 := by
    simp only [Metric.mem_ball,dist_zero_right,LinearIsometryEquiv.norm_map]
  change (if sourceSpatialRotation theta x∈Metric.ball (0:Position) 1 then ((HistoryPrepared.packetScale⁻¹:ℝ):ℂ) else 0) • v=
    (if x∈Metric.ball (0:Position) 1 then ((HistoryPrepared.packetScale⁻¹:ℝ):ℂ) else 0) • v
  simp only [ball]

private def rotatedSchwartz (theta : ℝ) (f : SchwartzMap Position Hilbert) : SchwartzMap Position Hilbert :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (sourceSpatialRotation theta).toContinuousLinearEquiv f

private theorem schwartz_pull (theta : ℝ) (f : SchwartzMap Position Hilbert) :
    sourceSpatialPull theta (f.toLp 2 volume)=(rotatedSchwartz theta f).toLp 2 volume := by
  apply Lp.ext
  have moved:=(sourceSpatialRotation theta).measurePreserving.quasiMeasurePreserving.ae (f.coeFn_toLp 2 volume)
  filter_upwards [Lp.coeFn_compMeasurePreserving (f.toLp 2 volume) (sourceSpatialRotation theta).measurePreserving,
    moved,(rotatedSchwartz theta f).coeFn_toLp 2 volume] with x pulled original changed
  change Lp.compMeasurePreserving (sourceSpatialRotation theta) (sourceSpatialRotation theta).measurePreserving
    (f.toLp 2 volume) x=_
  rw [pulled,changed]
  change f.toLp 2 volume (sourceSpatialRotation theta x)=f (sourceSpatialRotation theta x)
  exact original

private theorem fourier_schwartz_pull (theta : ℝ) (f : SchwartzMap Position Hilbert) :
    fourier (sourceSpatialPull theta (f.toLp 2 volume))=sourceSpatialPull theta (fourier (f.toLp 2 volume)) := by
  rw [schwartz_pull]
  change 𝓕 ((rotatedSchwartz theta f).toLp 2 volume)=sourceSpatialPull theta (𝓕 (f.toLp 2 volume))
  rw [SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq,schwartz_pull]
  apply Lp.ext
  filter_upwards [(𝓕 (rotatedSchwartz theta f)).coeFn_toLp 2 volume,
    (rotatedSchwartz theta (𝓕 f)).coeFn_toLp 2 volume] with x first second
  rw [first,second]
  simp only [SchwartzMap.fourier_coe]
  exact Real.fourier_comp_linearIsometry (sourceSpatialRotation theta) f x

/-- The original Fourier transform intertwines this actual spatial rotation, before choosing a packet. -/
theorem sourceFourierRotation (theta : ℝ) (field : FullMatterL2) :
    fourier (sourceSpatialPull theta field)=sourceSpatialPull theta (fourier field) := by
  apply DenseRange.induction_on (p:=fun g : FullMatterL2=>
      fourier (sourceSpatialPull theta g)=sourceSpatialPull theta (fourier g))
    (SchwartzMap.denseRange_toLpCLM (E:=Position) (F:=Hilbert) (p:=2) (μ:=volume) ENNReal.ofNat_ne_top) field
  · exact isClosed_eq (fourier.continuous.comp (sourceSpatialPull theta).continuous)
      ((sourceSpatialPull theta).continuous.comp fourier.continuous)
  · intro f
    exact fourier_schwartz_pull theta f

theorem sourceOriginalPacket_fourier_rotated (theta : ℝ) (v : Hilbert) :
    sourceSpatialPull theta (fourier (HistoryPrepared.preparation v))=fourier (HistoryPrepared.preparation v) := by
  rw [←sourceFourierRotation,sourceOriginalPacket_rotated]

private def chargedValues (side edge : Fin 2) : Source.Index→ℂ:=coordinates (sourceChargedRestriction side edge)

private theorem charged_embedded (side edge : Fin 2) : embed (chargedValues side edge)=sourceChargedRestriction side edge := by
  unfold chargedValues sourceChargedRestriction
  rw [actualRestState_source]
  rw [coordinates_embed]

private theorem charged_weight (side edge : Fin 2) :
    sourceLockedSourceMatrix*ᵥchargedValues side edge=-(sourceChargedPolarity edge:ℂ) • chargedValues side edge := by
  apply embedded_injective
  dsimp only
  rw [←sourceLockedSourceMatrix_original,←operator_coordinates]
  change sourceLockedFiberCharge (naturalCoordinates (embed (chargedValues side edge)))=_
  rw [charged_embedded,sourceLockedChargedMaker,map_smul,map_smul,charged_embedded]

private theorem rotation_eigen (theta weight : ℝ) (v : Source.Index→ℂ)
    (eigen : sourceLockedSourceMatrix*ᵥv=(weight:ℂ) • v) :
    sourceInternalRotation theta*ᵥv=Complex.exp ((theta*weight:ℝ)*Complex.I) • v := by
  funext index
  have entry:=congrFun eigen index
  simp only [sourceLockedSourceMatrix,Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul] at entry
  by_cases zero : v index=0
  · simp only [sourceInternalRotation,Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul,zero,mul_zero]
  · have charge : sourceLockedSourceWeight index=(weight:ℂ):=mul_right_cancel₀ zero entry
    simp only [sourceInternalRotation,Matrix.mulVec_diagonal,charge,Complex.ofReal_re,Pi.smul_apply,smul_eq_mul]

/-- The finite source action uses its original embedding and coordinate reader. -/
def sourceInternalFiber (theta : ℝ) : FiberOperators :=
  operator (embed.comp ((Matrix.mulVecLin (sourceInternalRotation theta)).comp coordinates))

def sourceInternalSpatial (theta : ℝ) : FullMatterL2→L[ℂ] FullMatterL2:=
  (sourceInternalFiber theta).compLpL 2 volume

private theorem internal_embed (theta : ℝ) (v : Source.Index→ℂ) :
    sourceInternalFiber theta (naturalCoordinates (embed v))=
      naturalCoordinates (embed (sourceInternalRotation theta*ᵥv)) := by
  simp only [sourceInternalFiber,operator_coordinates,LinearMap.comp_apply,coordinates_embed,Matrix.mulVecLin_apply]

private theorem internal_zero (v : Hilbert) :
    sourceInternalFiber 0 v=naturalCoordinates (embed (coordinates (naturalCoordinates.symm v))) := by
  obtain ⟨matter,rfl⟩:=naturalCoordinates.surjective v
  simp only [sourceInternalFiber,operator_coordinates,LinearMap.comp_apply,sourceInternalRotation_zero,
    Matrix.mulVecLin_apply,Matrix.one_mulVec,naturalCoordinates.symm_apply_apply]

private theorem internal_charged (theta : ℝ) (side edge : Fin 2) :
    sourceInternalFiber theta (naturalCoordinates (sourceChargedRestriction side edge))=
      Complex.exp ((theta*(-sourceChargedPolarity edge):ℝ)*Complex.I) •
        naturalCoordinates (sourceChargedRestriction side edge) := by
  rw [←charged_embedded,internal_embed]
  have eigen : sourceLockedSourceMatrix*ᵥchargedValues side edge=
      ((-sourceChargedPolarity edge:ℝ):ℂ) • chargedValues side edge := by
    simpa only [Complex.ofReal_neg] using charged_weight side edge
  rw [rotation_eigen theta (-sourceChargedPolarity edge) _ eigen,map_smul,map_smul]

private theorem packet_internal (theta : ℝ) (side edge : Fin 2) :
    sourceInternalSpatial theta (sourceChargedSpatialPacket side edge)=
      Complex.exp ((theta*(-sourceChargedPolarity edge):ℝ)*Complex.I) • sourceChargedSpatialPacket side edge := by
  apply Lp.ext
  filter_upwards [(sourceInternalFiber theta).coeFn_compLpL (sourceChargedSpatialPacket side edge),
    PreparationVacuumActualSpatialPacket.sourcePacketShape_original (naturalCoordinates (sourceChargedRestriction side edge)),
    Lp.coeFn_smul (Complex.exp ((theta*(-sourceChargedPolarity edge):ℝ)*Complex.I))
      (sourceChargedSpatialPacket side edge)] with x read packet scaled
  change (sourceInternalFiber theta).compLpL 2 volume (sourceChargedSpatialPacket side edge) x=_
  rw [read,scaled]
  simp only [Pi.smul_apply]
  change sourceChargedSpatialPacket side edge x=_ at packet
  rw [packet,map_smul,internal_charged]
  exact smul_comm (PreparationVacuumActualSpatialPacket.sourcePacketShape x)
    (Complex.exp ((theta*(-sourceChargedPolarity edge):ℝ)*Complex.I))
    (naturalCoordinates (sourceChargedRestriction side edge))

private theorem packet_fourier_internal (theta : ℝ) (side edge : Fin 2) :
    (fun k=>sourceInternalFiber theta (fourier (sourceChargedSpatialPacket side edge) k))=ᵐ[volume]
      fun k=>Complex.exp ((theta*(-sourceChargedPolarity edge):ℝ)*Complex.I) •
        fourier (sourceChargedSpatialPacket side edge) k := by
  have original:=congrArg FullSpace.fourier (packet_internal theta side edge)
  rw [sourceInternalSpatial,GaugeGreen.constant_fourier,map_smul] at original
  have read:=(sourceInternalFiber theta).coeFn_compLpL (fourier (sourceChargedSpatialPacket side edge))
  rw [original] at read
  exact read.symm.trans (Lp.coeFn_smul _ _)

private theorem green_internal (theta : ℝ) (p : Fin 3→ℝ) (v : Source.Index→ℂ) :
    sourceInternalFiber theta (Retarded.diracValue 0 p 0 1 (naturalCoordinates (embed v)))=
      Retarded.diracValue 0 (sourceRotatedMomentum theta p) 0 1
        (sourceInternalFiber theta (naturalCoordinates (embed v))) := by
  rw [sourceGreenCoordinates_original,internal_embed,internal_embed,sourceJointGreen_covariance]

private theorem filtered_fourier (side edge : Fin 2) :
    fourier (sourceChargedFilteredPacket side edge)=ᵐ[volume]
      fun k=>((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) •
        Retarded.diracValue 0 (physicalMomentum k) 0 1 (fourier (sourceChargedSpatialPacket side edge) k) := by
  have identity : sourceChargedFilteredPacket side edge=
      ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) • sourceChargedRawPacket side edge:=rfl
  rw [identity,map_smul]
  filter_upwards [Lp.coeFn_smul ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ)
    (fourier (sourceChargedRawPacket side edge)),
    SpatialGreen.green_fourier_ae 0 0 1 (by norm_num) (sourceChargedSpatialPacket side edge)] with k scaled green
  rw [scaled]
  change ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) •
    fourier (SpatialGreen.green 0 0 1 (by norm_num) (sourceChargedSpatialPacket side edge)) k=_
  rw [green]

private theorem physical_rotation (theta : ℝ) (k : Position) :
    physicalMomentum (sourceSpatialRotation theta k)=sourceRotatedMomentum theta (physicalMomentum k) := by
  funext j
  fin_cases j <;> simp [sourceSpatialRotation,physicalMomentum,sourceRotatedMomentum,Matrix.cons_val_two] <;> ring

private theorem packet_rotation_ae (theta : ℝ) (side edge : Fin 2) :
    (fun k=>fourier (sourceChargedSpatialPacket side edge) (sourceSpatialRotation theta k))=ᵐ[volume]
      fourier (sourceChargedSpatialPacket side edge) := by
  have fixed:=sourceOriginalPacket_fourier_rotated theta (naturalCoordinates (sourceChargedRestriction side edge))
  change sourceSpatialPull theta (fourier (sourceChargedSpatialPacket side edge))=_ at fixed
  have read:=Lp.coeFn_compMeasurePreserving (fourier (sourceChargedSpatialPacket side edge))
    (sourceSpatialRotation theta).measurePreserving
  change sourceSpatialPull theta (fourier (sourceChargedSpatialPacket side edge))=ᵐ[volume] _ at read
  rw [fixed] at read
  exact read.symm

/-- The joint orbit is built from the source internal rotation and the actual spatial rotation in the original Fourier carrier. -/
def sourceJointSpatialOrbit (theta : ℝ) (field : FullMatterL2) : FullMatterL2 :=
  fourier.symm (sourceInternalSpatial theta (sourceSpatialPull (-theta) (fourier field)))

theorem sourceJointSpatialOrbit_position (theta : ℝ) (field : FullMatterL2) :
    sourceJointSpatialOrbit theta field=sourceInternalSpatial theta (sourceSpatialPull (-theta) field) := by
  apply fourier.injective
  rw [sourceJointSpatialOrbit,fourier.apply_symm_apply]
  change _=fourier ((sourceInternalFiber theta).compLpL 2 volume (sourceSpatialPull (-theta) field))
  rw [GaugeGreen.constant_fourier,sourceFourierRotation]
  rfl

/-- Original unit-ball preparation, the full Green covariance and the original normalization generate the orbit phase. -/
theorem sourceJointFilteredOrbit (theta : ℝ) (side edge : Fin 2) :
    sourceJointSpatialOrbit theta (sourceChargedFilteredPacket side edge)=
      Complex.exp ((theta*(-sourceChargedPolarity edge):ℝ)*Complex.I) • sourceChargedFilteredPacket side edge := by
  apply fourier.injective
  rw [sourceJointSpatialOrbit,fourier.apply_symm_apply,map_smul]
  apply Lp.ext
  have moved:=(sourceSpatialRotation (-theta)).measurePreserving.quasiMeasurePreserving.ae (filtered_fourier side edge)
  have zero:=packet_fourier_internal 0 side edge
  simp only [zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_smul] at zero
  filter_upwards [(sourceInternalFiber theta).coeFn_compLpL
      (sourceSpatialPull (-theta) (fourier (sourceChargedFilteredPacket side edge))),
    Lp.coeFn_compMeasurePreserving (fourier (sourceChargedFilteredPacket side edge))
      (sourceSpatialRotation (-theta)).measurePreserving,
    Lp.coeFn_smul (Complex.exp ((theta*(-sourceChargedPolarity edge):ℝ)*Complex.I))
      (fourier (sourceChargedFilteredPacket side edge)),
    moved,packet_rotation_ae (-theta) side edge,packet_fourier_internal theta side edge,zero,
    filtered_fourier side edge] with k internal pulled scaled rotated input eigen retained actual
  change (sourceInternalFiber theta).compLpL 2 volume
    (sourceSpatialPull (-theta) (fourier (sourceChargedFilteredPacket side edge))) k=_
  rw [internal,scaled]
  simp only [Pi.smul_apply]
  change sourceInternalFiber theta (Lp.compMeasurePreserving (sourceSpatialRotation (-theta))
    (sourceSpatialRotation (-theta)).measurePreserving (fourier (sourceChargedFilteredPacket side edge)) k)=_
  rw [pulled]
  change sourceInternalFiber theta (fourier (sourceChargedFilteredPacket side edge) (sourceSpatialRotation (-theta) k))=_
  rw [rotated,input,map_smul,actual]
  have represented : fourier (sourceChargedSpatialPacket side edge) k=
      naturalCoordinates (embed (coordinates (naturalCoordinates.symm (fourier (sourceChargedSpatialPacket side edge) k)))) :=
    retained.symm.trans (internal_zero _)
  have passed:=green_internal theta (physicalMomentum (sourceSpatialRotation (-theta) k))
    (coordinates (naturalCoordinates.symm (fourier (sourceChargedSpatialPacket side edge) k)))
  have rotate : sourceRotatedMomentum theta (physicalMomentum (sourceSpatialRotation (-theta) k))=physicalMomentum k := by
    rw [physical_rotation,sourceRotatedMomentum_add,add_neg_cancel,sourceRotatedMomentum_zero]
  rw [←represented,rotate,eigen,map_smul] at passed
  rw [passed]
  exact smul_comm ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ)
    (Complex.exp ((theta*(-sourceChargedPolarity edge):ℝ)*Complex.I))
    (Retarded.diracValue 0 (physicalMomentum k) 0 1 (fourier (sourceChargedSpatialPacket side edge) k))

/-- Differentiation of the actual joint orbit generates its polarity; no charge outcome is assumed. -/
theorem sourceJointFilteredGenerator (side edge : Fin 2) :
    HasDerivAt (fun theta : ℝ=>sourceJointSpatialOrbit theta (sourceChargedFilteredPacket side edge))
      ((((-sourceChargedPolarity edge:ℝ):ℂ)*Complex.I) • sourceChargedFilteredPacket side edge) 0 := by
  have linear:=((hasDerivAt_id (0:ℝ)).ofReal_comp).mul_const (((-sourceChargedPolarity edge:ℝ):ℂ)*Complex.I)
  have generated:=linear.cexp.smul_const (sourceChargedFilteredPacket side edge)
  simpa only [sourceJointFilteredOrbit,Complex.ofReal_mul,mul_assoc,Complex.ofReal_zero,zero_mul,
    Complex.exp_zero,Complex.ofReal_one,one_mul,id_eq] using generated

/-- The earlier full Dirac torque is precisely the orbital part of this actual joint generator. -/
theorem sourceLockedTorque_orbital (side edge : Fin 2) :
    sourceLockedSpatialCharge (sourceChargedFilteredPacket side edge)-
      (-Complex.I) • deriv (fun theta : ℝ=>sourceJointSpatialOrbit theta (sourceChargedFilteredPacket side edge)) 0=
        sourceFilteredLockedCorrection side edge := by
  rw [(sourceJointFilteredGenerator side edge).deriv,sourceFilteredLockedAction,smul_smul]
  have scalar : (-Complex.I)*(((-sourceChargedPolarity edge:ℝ):ℂ)*Complex.I)=-(sourceChargedPolarity edge:ℂ) := by
    simp only [Complex.ofReal_neg]
    calc
      _=Complex.I*Complex.I*(sourceChargedPolarity edge:ℂ) := by ring
      _=_ := by rw [Complex.I_mul_I,neg_one_mul]
  rw [scalar]
  abel

end LowEnergy.PreparationPhysicalJointRotationCharge
