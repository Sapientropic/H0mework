import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3WriterStep
set_option autoImplicit false
namespace FlyCNS.C3TraceWriter
structure Member where
  name : String
  dtype : String
  shape : Array Nat
  payload : ByteArray
def generate (members : Array Member) : ByteArray :=
  FlyCNS.C3Writer.archive (members.map fun m =>
    (m.name,FlyCNS.C3Writer.npy m.dtype m.shape m.payload))
end FlyCNS.C3TraceWriter
