import H0mework.Chemistry.LAlanineBasinPartition.RuntimeParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.SourceData

abbrev GridBlock := Fin 229
abbrev Bucket := Fin 20
abbrev Field := Fin 8
abbrev OldField := Fin 7

def atomicBucket (atom : Force.Interface.Atom) : Bucket := ⟨atom.val, by omega⟩

def cubeRead (rows : Array (Array (Array Int))) : GridBlock → Bucket → Field → Int :=
  fun block bucket field => ((rows[block.val]!)[bucket.val]!)[field.val]!

def countRead (rows : Array (Array Nat)) : GridBlock → Bucket → Nat :=
  fun block bucket => (rows[block.val]!)[bucket.val]!

def blockRead (rows : Array (Array Int)) : GridBlock → Field → Int :=
  fun block field => (rows[block.val]!)[field.val]!

def fieldRead (rows : Array Int) : Field → Int := fun field => rows[field.val]!

def bucketRead (rows : Array (Array Int)) : Bucket → Field → Int :=
  fun bucket field => (rows[bucket.val]!)[field.val]!

def bucketVectorRead (rows : Array Int) : Bucket → Int := fun bucket => rows[bucket.val]!

def bucketCountRead (rows : Array Nat) : Bucket → Nat := fun bucket => rows[bucket.val]!

def oldFieldRead (rows : Array Int) : OldField → Int := fun field => rows[field.val]!

def blockXcRead (rows : Array (Array Int)) : GridBlock → Fin 3 → Int :=
  fun block field => (rows[block.val]!)[field.val]!

def blockBucketRead (rows : Array (Array Int)) : GridBlock → Bucket → Int :=
  fun block bucket => (rows[block.val]!)[bucket.val]!

def atomScalarRead (rows : Array Int) : Force.Interface.Atom → Int := fun atom => rows[atom.val]!

def atomVectorRead (rows : Array (Array Int)) : Force.Interface.Atom → Fin 3 → Int :=
  fun atom axis => (rows[atom.val]!)[axis.val]!

def atomMatrixRead (rows : Array (Array (Array Int))) : Force.Interface.Atom → Matrix (Fin 3) (Fin 3) Int :=
  fun atom i j => ((rows[atom.val]!)[i.val]!)[j.val]!

noncomputable def oldBlockValue (block : GridBlock) (column : Nat) : Int :=
  (Runtime.basinParentLedger.xcGridBlocks[block.val]!)[column]!

noncomputable def oldComponentIntegral (component : Energy.Interface.EnergyComponent) : Int :=
  (Runtime.basinParentLedger.integral component).independentIntegral

def fieldNames : Array String := #["electron_density", "kinetic_positive_density",
  "kinetic_laplacian_density", "density_laplacian", "electron_nuclear_density",
  "coulomb_density", "b88_exchange_density", "lyp_correlation_density"]

end LAlanine40K2025.BasinPartition.SourceData
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
