import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Mechanics

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace CPS1AddressedInteraction
noncomputable section
open CPS1ElectronicSource CPS1Deformation CPS1MolecularFrame
open scoped BigOperators InnerProductSpace Matrix
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)
variable {frame : CPS1Recycling.Frame}

abbrev KineticChannel (source : CPS1ElectronicSource.State frame) :=
  Fin 3 × PrimitiveIndex source × PrimitiveIndex source
abbrev AttractionChannel (source : CPS1ElectronicSource.State frame) :=
  NuclearIndex source × Bool × PrimitiveIndex source × PrimitiveIndex source
abbrev PairChannel (source : CPS1ElectronicSource.State frame) :=
  ActualIndex source × ActualIndex source × Bool × Bool × PrimitiveIndex source ×
    PrimitiveIndex source × PrimitiveIndex source × PrimitiveIndex source
abbrev Channel (source : CPS1ElectronicSource.State frame) :=
  KineticChannel source ⊕ (AttractionChannel source ⊕ (PairChannel source ⊕ PairChannel source))

def kineticMatrix (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (channel : KineticChannel source) : Matrix (ActualIndex source) (ActualIndex source) ℂ := fun i k =>
  ((1/(2*source.geometry.electronInertia) : ℝ) : ℂ) *
    (star (basisCoefficient source channel.2.1 i)*basisCoefficient source channel.2.2 k) *
    inner ℂ (rawJetAt source positions channel.2.1 (raise 0 channel.1))
      (rawJetAt source positions channel.2.2 (raise 0 channel.1))

def attractionMatrix (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (channel : AttractionChannel source) : Matrix (ActualIndex source) (ActualIndex source) ℂ := fun i k =>
  -((nucleus source channel.1).particle.charge : ℂ) *
    (star (basisCoefficient source channel.2.2.1 i)*basisCoefficient source channel.2.2.2 k) *
    rawNuclearIntegralAt source positions channel.2.2.1 channel.2.2.2 0 0 channel.2.1
      (positions channel.1)

def directMatrix (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) (channel : PairChannel source) :
    Matrix (ActualIndex source) (ActualIndex source) ℂ := fun i k =>
  densityAt source occupied channel.2.1 channel.1 *
    (star (basisCoefficient source channel.2.2.2.2.1 i) *
      basisCoefficient source channel.2.2.2.2.2.1 k *
      star (basisCoefficient source channel.2.2.2.2.2.2.1 channel.1) *
      basisCoefficient source channel.2.2.2.2.2.2.2 channel.2.1) *
    rawPairIntegralAt source positions channel.2.2.2.2.1 channel.2.2.2.2.2.1
      channel.2.2.2.2.2.2.1 channel.2.2.2.2.2.2.2 channel.2.2.1 channel.2.2.2.1

def exchangeMatrix (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) (channel : PairChannel source) :
    Matrix (ActualIndex source) (ActualIndex source) ℂ := fun i k =>
  -(densityAt source occupied channel.2.1 channel.1 *
    (star (basisCoefficient source channel.2.2.2.2.1 i) *
      basisCoefficient source channel.2.2.2.2.2.1 channel.2.1 *
      star (basisCoefficient source channel.2.2.2.2.2.2.1 channel.1) *
      basisCoefficient source channel.2.2.2.2.2.2.2 k) *
    rawPairIntegralAt source positions channel.2.2.2.2.1 channel.2.2.2.2.2.1
      channel.2.2.2.2.2.2.1 channel.2.2.2.2.2.2.2 channel.2.2.1 channel.2.2.2.1)

def channelMatrix (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) : Channel source → Matrix (ActualIndex source) (ActualIndex source) ℂ
  | .inl channel => kineticMatrix source positions channel
  | .inr (.inl channel) => attractionMatrix source positions channel
  | .inr (.inr (.inl channel)) => directMatrix source positions occupied channel
  | .inr (.inr (.inr channel)) => exchangeMatrix source positions occupied channel

/-- Every primitive leg carries its actual raw nuclear centre. A GS coordinate
may involve all these centres and is never assigned to one pivot atom. -/
def nuclearSupport (source : CPS1ElectronicSource.State frame) : Channel source → List (NuclearIndex source)
  | .inl channel => [channel.2.1.1.1,channel.2.2.1.1]
  | .inr (.inl channel) => [channel.1,channel.2.2.1.1.1,channel.2.2.2.1.1]
  | .inr (.inr (.inl channel)) | .inr (.inr (.inr channel)) =>
    [channel.2.2.2.2.1.1.1,channel.2.2.2.2.2.1.1.1,
     channel.2.2.2.2.2.2.1.1.1,channel.2.2.2.2.2.2.2.1.1]

def addressSupport (source : CPS1ElectronicSource.State frame) (channel : Channel source) :=
  (nuclearSupport source channel).map (address source)

theorem actual_address_support (source : CPS1ElectronicSource.State frame) (channel : Channel source) :
    addressSupport source channel =
      (nuclearSupport source channel).map (fun index => (source.geometry.nuclei.get index).particle.address) := rfl

theorem kinetic_split (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i k : ActualIndex source) :
    ∑ channel : KineticChannel source, kineticMatrix source positions channel i k = kineticAt source positions i k := by
  classical
  rw [Fintype.sum_prod_type,kineticAt,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro axis _
  rw [Fintype.sum_prod_type]
  unfold kineticMatrix basisJetAt
  rw [sum_inner]
  simp_rw [inner_smul_left,inner_sum,inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [starRingEnd_apply]
  ring

theorem attraction_split (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i k : ActualIndex source) :
    ∑ channel : AttractionChannel source, attractionMatrix source positions channel i k =
      attractionAt source positions i k := by
  classical
  rw [Fintype.sum_prod_type,attractionAt,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro nuclear _
  rw [Fintype.sum_prod_type]
  unfold nuclearIntegralAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spin _
  rw [Fintype.sum_prod_type]
  unfold attractionMatrix
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

private theorem pair_channel_sum (source : CPS1ElectronicSource.State frame)
    (value : PairChannel source → ℂ) :
    ∑ channel, value channel = ∑ j, ∑ l, ∑ spin : Bool, ∑ secondSpin : Bool,
      ∑ p : PrimitiveIndex source, ∑ q : PrimitiveIndex source,
      ∑ r : PrimitiveIndex source, ∑ s : PrimitiveIndex source,
        value (j,l,spin,secondSpin,p,q,r,s) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro spin _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro secondSpin _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fintype.sum_prod_type]

theorem direct_split (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) (i k : ActualIndex source) :
    ∑ channel : PairChannel source, directMatrix source positions occupied channel i k =
      ∑ j, ∑ l, densityAt source occupied l j * twoBodyAt source positions i j k l := by
  classical
  rw [pair_channel_sum]
  simp only [directMatrix,twoBodyAt,pairIntegralAt,Finset.mul_sum]
  repeat (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem exchange_split (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) (i k : ActualIndex source) :
    ∑ channel : PairChannel source, exchangeMatrix source positions occupied channel i k =
      -(∑ j, ∑ l, densityAt source occupied l j * twoBodyAt source positions i j l k) := by
  classical
  rw [pair_channel_sum]
  simp only [exchangeMatrix,twoBodyAt,pairIntegralAt,Finset.mul_sum,Finset.sum_neg_distrib]
  apply congrArg (fun value : ℂ => -value)
  repeat (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem fock_split (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) :
    ∑ channel : Channel source, channelMatrix source positions occupied channel =
      physicalFockAt source positions occupied := by
  classical
  simp only [Fintype.sum_sum_type,channelMatrix]
  ext i k
  simp only [Matrix.add_apply,Matrix.sum_apply,kinetic_split,attraction_split,
    direct_split,exchange_split,physicalFockAt,coreAt,mul_sub,Finset.sum_sub_distrib]
  ring

end
end CPS1AddressedInteraction
