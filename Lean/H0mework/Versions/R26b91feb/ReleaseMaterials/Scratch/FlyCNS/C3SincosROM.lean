import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SincosStep
set_option autoImplicit false
namespace FlyCNS.C3Sincos

/-- Actual captured operator coefficients and integer reciprocal data, never argument/results. -/
def original : Material :=
  ⟨Float.ofBits 0x3fe921fb54442d18,Float.ofBits 0x412000013be57a40,#[Float.ofBits 0x3fe45f306dc9c883,Float.ofBits 0x3ff921fb54440000,Float.ofBits 0x3d868c234c4c0000,Float.ofBits 0x3b298a2e03707345],
    #[Float.ofBits 0x3de5d8fd1fd19ccd,Float.ofBits 0xbe5ae5e5a9291f5d,Float.ofBits 0x3ec71de3567d48a1,Float.ofBits 0xbf2a01a019bfdf03,Float.ofBits 0x3f8111111110f7d0,Float.ofBits 0xbfc5555555555548],
    #[Float.ofBits 0xbda8fa49a0861a9b,Float.ofBits 0x3e21ee9d7b4e3f05,Float.ofBits 0xbe927e4f7eac4bc6,Float.ofBits 0x3efa01a019c844f5,Float.ofBits 0xbf56c16c16c14f91,Float.ofBits 0x3fa555555555554b,Float.ofBits 0xbfe0000000000000],
    0xc90fdaa22168c235,#[0x7fefffffffffffff,0x35fdafd88fc6ae84,0x9e839cfbc5294975,0xba93dd63f5f2f8bd,0xa7a31fb34f2ff516,0xb69b3f6793e584db,0xf79788c5ad05368f,0x8ffc4bffef02cc07,0x4e422fc5defc941d,0x9cc8eb1cc1a99cfa,0x74ce38135a2fbf20,0x74411afa975da242,0x7f0ef58e5894d39f,0x324977504e8c90e,0xdb92371d2126e970,0xff28b1d5ef5de2b0,0x6db14acc9e21c820,0xfe13abe8fa9a6ee0,0x517cc1b727220a94,0x0]⟩

def sine (x : Float) : Float := evaluate original false x
def cosine (x : Float) : Float := evaluate original true x

end FlyCNS.C3Sincos
