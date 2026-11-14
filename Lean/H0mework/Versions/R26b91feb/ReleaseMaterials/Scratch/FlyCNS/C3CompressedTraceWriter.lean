import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3DeflateStream
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3TraceWriterStep

set_option autoImplicit false
namespace FlyCNS.C3CompressedTrace
open FlyCNS.C3Writer

def numpyChunks (headerSize payloadSize : Nat) : Array Nat := Id.run do
  let mut ends := #[headerSize]
  let mut offset := headerSize
  for _ in [:(payloadSize+16777215)/16777216] do
    offset:=min (headerSize+payloadSize) (offset+16777216)
    ends:=ends.push offset
  return ends

/-- NumPy ZIP_DEFLATED with forced ZIP64 local records. Member data, CRC,
raw/compressed sizes and every offset are generated internally from typed PL
trace members. No compressed stream or compressor is a caller argument. -/
def generate (members : Array FlyCNS.C3TraceWriter.Member) : Except String ByteArray := do
  let mut payload := ByteArray.empty
  let mut directory := ByteArray.empty
  for member in members do
    let raw := npy member.dtype member.shape member.payload
    let ends := numpyChunks (raw.size-member.payload.size) member.payload.size
    let compressed ← FlyCNS.C3Deflate.compress raw ends
    let file := (member.name++".npy").toUTF8
    let crc := crc32 raw
    let offset := payload.size
    let extra := little 1 2++little 16 2++little raw.size 8++little compressed.size 8
    let localHeader := little 0x04034B50 4++little 45 2++little 0 2++little 8 2++little 0 2++little 33 2++little crc 4++little 0xFFFFFFFF 4++little 0xFFFFFFFF 4++little file.size 2++little extra.size 2++file++extra
    payload:=payload++localHeader++compressed
    directory:=directory++little 0x02014B50 4++little 813 2++little 45 2++little 0 2++little 8 2++little 0 2++little 33 2++little crc 4++little compressed.size 4++little raw.size 4++little file.size 2++little 0 2++little 0 2++little 0 2++little 0 2++little 25165824 4++little offset 4++file
  let ending := little 0x06054B50 4++little 0 2++little 0 2++little members.size 2++little members.size 2++little directory.size 4++little payload.size 4++little 0 2
  return payload++directory++ending

end FlyCNS.C3CompressedTrace
