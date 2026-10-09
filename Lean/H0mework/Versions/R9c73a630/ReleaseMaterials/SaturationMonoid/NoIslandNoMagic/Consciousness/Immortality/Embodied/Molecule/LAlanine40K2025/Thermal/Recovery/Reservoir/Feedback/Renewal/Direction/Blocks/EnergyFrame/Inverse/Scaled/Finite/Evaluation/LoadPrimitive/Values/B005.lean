import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B003
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B004

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v81_pa : Scalar.QComplex := ((999977292480220136705648937118 : Int)/10^30,(6739029895190555972769839371 : Int)/10^30)
theorem v81_pa_checked : Scalar.distance (sourceCoefficient 0 82 1 0) v81_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v81_pb : Scalar.QComplex := ((2907701099400893649249378 : Int)/10^30,(-431461963805169826892981031 : Int)/10^30)
theorem v81_pb_checked : Scalar.distance (sourceCoefficient 0 82 1 1) v81_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v81_pg : Scalar.QComplex := ((-93083694870065207025398 : Int)/10^30,(-627308047094052680385 : Int)/10^30)
theorem v81_pg_checked : Scalar.distance (sourceCoefficient 0 82 1 2) v81_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v81_mb : Scalar.QComplex := ((2535367774292512231447697 : Int)/10^30,(-431464312367252703198102897 : Int)/10^30)
theorem v81_mb_checked : Scalar.distance (sourceCoefficient 0 82 3 1) v81_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v81_mg : Scalar.QComplex := ((-93084201549343208409529 : Int)/10^30,(-546980777179721274279 : Int)/10^30)
theorem v81_mg_checked : Scalar.distance (sourceCoefficient 0 82 3 2) v81_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v81_upper : Scalar.QComplex := ((999987434085747654190016504442 : Int)/10^30,(5013149768607618874061255778 : Int)/10^30)
theorem v81_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 82 5) 1) 14) v81_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material81 : Material (0 : Basis) (82 : Basis) where
  plus := ![v81_pa,v81_pb,v81_pg]
  minus := ![(Primitive.Addresses.material81 1).one,v81_mb,v81_mg]
  upper := v81_upper
  lower := (Primitive.Addresses.material81 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v81_pa_checked.trans (by decide +kernel)
    · exact v81_pb_checked.trans (by decide +kernel)
    · exact v81_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 82 Primitive.Addresses.material81
    · exact v81_mb_checked.trans (by decide +kernel)
    · exact v81_mg_checked.trans (by decide +kernel)
  upper_error := v81_upper_checked
  lower_error := reuse_lower_error 0 82 Primitive.Addresses.material81

def v82_pa : Scalar.QComplex := ((999977383827509822790709075536 : Int)/10^30,(6725461581861598377459729657 : Int)/10^30)
theorem v82_pa_checked : Scalar.distance (sourceCoefficient 0 83 1 0) v82_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v82_pb : Scalar.QComplex := ((2901846637801776777397562 : Int)/10^30,(-431461985741425836683399753 : Int)/10^30)
theorem v82_pb_checked : Scalar.distance (sourceCoefficient 0 83 1 1) v82_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v82_pg : Scalar.QComplex := ((-93083701487907173437442 : Int)/10^30,(-626045016996484005623 : Int)/10^30)
theorem v82_pg_checked : Scalar.distance (sourceCoefficient 0 83 1 2) v82_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v82_mb : Scalar.QComplex := ((2529513295943278010906303 : Int)/10^30,(-431464329251363860242354446 : Int)/10^30)
theorem v82_mb_checked : Scalar.distance (sourceCoefficient 0 83 3 1) v82_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v82_mg : Scalar.QComplex := ((-93084207077244621258725 : Int)/10^30,(-545717741841536867693 : Int)/10^30)
theorem v82_mg_checked : Scalar.distance (sourceCoefficient 0 83 3 2) v82_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v82_upper : Scalar.QComplex := ((999987502015223391206565338632 : Int)/10^30,(4999581317829935099391604792 : Int)/10^30)
theorem v82_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 83 5) 1) 14) v82_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material82 : Material (0 : Basis) (83 : Basis) where
  plus := ![v82_pa,v82_pb,v82_pg]
  minus := ![(Primitive.Addresses.material82 1).one,v82_mb,v82_mg]
  upper := v82_upper
  lower := (Primitive.Addresses.material82 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v82_pa_checked.trans (by decide +kernel)
    · exact v82_pb_checked.trans (by decide +kernel)
    · exact v82_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 83 Primitive.Addresses.material82
    · exact v82_mb_checked.trans (by decide +kernel)
    · exact v82_mg_checked.trans (by decide +kernel)
  upper_error := v82_upper_checked
  lower_error := reuse_lower_error 0 83 Primitive.Addresses.material82

def v83_pa : Scalar.QComplex := ((999977619536526197541760983612 : Int)/10^30,(6690323315241171083596448639 : Int)/10^30)
theorem v83_pa_checked : Scalar.distance (sourceCoefficient 0 84 1 0) v83_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v83_pb : Scalar.QComplex := ((2886685164974572642040508 : Int)/10^30,(-431462042058070760513065488 : Int)/10^30)
theorem v83_pb_checked : Scalar.distance (sourceCoefficient 0 84 1 1) v83_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v83_pg : Scalar.QComplex := ((-93083718533391340544918 : Int)/10^30,(-622774110346523833129 : Int)/10^30)
theorem v83_pg_checked : Scalar.distance (sourceCoefficient 0 84 1 2) v83_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v83_mb : Scalar.QComplex := ((2514351780162654960922669 : Int)/10^30,(-431464372484319612321799133 : Int)/10^30)
theorem v83_mb_checked : Scalar.distance (sourceCoefficient 0 84 3 1) v83_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v83_mg : Scalar.QComplex := ((-93084221300077318804681 : Int)/10^30,(-542446821699999592692 : Int)/10^30)
theorem v83_mg_checked : Scalar.distance (sourceCoefficient 0 84 3 2) v83_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v83_upper : Scalar.QComplex := ((999987677078428236855257537010 : Int)/10^30,(4964442696731449398014896780 : Int)/10^30)
theorem v83_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 84 5) 1) 14) v83_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material83 : Material (0 : Basis) (84 : Basis) where
  plus := ![v83_pa,v83_pb,v83_pg]
  minus := ![(Primitive.Addresses.material83 1).one,v83_mb,v83_mg]
  upper := v83_upper
  lower := (Primitive.Addresses.material83 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v83_pa_checked.trans (by decide +kernel)
    · exact v83_pb_checked.trans (by decide +kernel)
    · exact v83_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 84 Primitive.Addresses.material83
    · exact v83_mb_checked.trans (by decide +kernel)
    · exact v83_mg_checked.trans (by decide +kernel)
  upper_error := v83_upper_checked
  lower_error := reuse_lower_error 0 84 Primitive.Addresses.material83

def v84_pa : Scalar.QComplex := ((999978145327274380489738054900 : Int)/10^30,(6611268246298820129774479588 : Int)/10^30)
theorem v84_pa_checked : Scalar.distance (sourceCoefficient 0 85 1 0) v84_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v84_pb : Scalar.QComplex := ((2852574460720100643359756 : Int)/10^30,(-431462166163921003986340754 : Int)/10^30)
theorem v84_pb_checked : Scalar.distance (sourceCoefficient 0 85 1 1) v84_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v84_pg : Scalar.QComplex := ((-93083756392574848998479 : Int)/10^30,(-615415132580757855731 : Int)/10^30)
theorem v84_pg_checked : Scalar.distance (sourceCoefficient 0 85 1 2) v84_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v84_mb : Scalar.QComplex := ((2480240981511397852264077 : Int)/10^30,(-431464467154122162995666034 : Int)/10^30)
theorem v84_mb_checked : Scalar.distance (sourceCoefficient 0 85 3 1) v84_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v84_mg : Scalar.QComplex := ((-93084252808780354753019 : Int)/10^30,(-535087814003547105920 : Int)/10^30)
theorem v84_mg_checked : Scalar.distance (sourceCoefficient 0 85 3 2) v84_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v84_upper : Scalar.QComplex := ((999988066426516141581057775592 : Int)/10^30,(4885386838065205173388382268 : Int)/10^30)
theorem v84_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 85 5) 1) 14) v84_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material84 : Material (0 : Basis) (85 : Basis) where
  plus := ![v84_pa,v84_pb,v84_pg]
  minus := ![(Primitive.Addresses.material84 1).one,v84_mb,v84_mg]
  upper := v84_upper
  lower := (Primitive.Addresses.material84 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v84_pa_checked.trans (by decide +kernel)
    · exact v84_pb_checked.trans (by decide +kernel)
    · exact v84_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 85 Primitive.Addresses.material84
    · exact v84_mb_checked.trans (by decide +kernel)
    · exact v84_mg_checked.trans (by decide +kernel)
  upper_error := v84_upper_checked
  lower_error := reuse_lower_error 0 85 Primitive.Addresses.material84

def v85_pa : Scalar.QComplex := ((999978241643915205555273622704 : Int)/10^30,(6596683920238211378578549423 : Int)/10^30)
theorem v85_pa_checked : Scalar.distance (sourceCoefficient 0 86 1 0) v85_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v85_pb : Scalar.QComplex := ((2846281612575918936731793 : Int)/10^30,(-431462188666498319078914128 : Int)/10^30)
theorem v85_pb_checked : Scalar.distance (sourceCoefficient 0 86 1 1) v85_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v85_pg : Scalar.QComplex := ((-93083763302794512653053 : Int)/10^30,(-614057525497100577921 : Int)/10^30)
theorem v85_pg_checked : Scalar.distance (sourceCoefficient 0 86 1 2) v85_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v85_mb : Scalar.QComplex := ((2473948116291620362618042 : Int)/10^30,(-431464484226246570280866369 : Int)/10^30)
theorem v85_mb_checked : Scalar.distance (sourceCoefficient 0 86 3 1) v85_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v85_mg : Scalar.QComplex := ((-93084258547443676574031 : Int)/10^30,(-533730201462180646071 : Int)/10^30)
theorem v85_mg_checked : Scalar.distance (sourceCoefficient 0 86 3 2) v85_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v85_upper : Scalar.QComplex := ((999988137571789813438414052390 : Int)/10^30,(4870802367492452607521467262 : Int)/10^30)
theorem v85_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 86 5) 1) 14) v85_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material85 : Material (0 : Basis) (86 : Basis) where
  plus := ![v85_pa,v85_pb,v85_pg]
  minus := ![(Primitive.Addresses.material85 1).one,v85_mb,v85_mg]
  upper := v85_upper
  lower := (Primitive.Addresses.material85 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v85_pa_checked.trans (by decide +kernel)
    · exact v85_pb_checked.trans (by decide +kernel)
    · exact v85_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 86 Primitive.Addresses.material85
    · exact v85_mb_checked.trans (by decide +kernel)
    · exact v85_mg_checked.trans (by decide +kernel)
  upper_error := v85_upper_checked
  lower_error := reuse_lower_error 0 86 Primitive.Addresses.material85

def v86_pa : Scalar.QComplex := ((999978248014238854306887102053 : Int)/10^30,(6595718184807992017459192829 : Int)/10^30)
theorem v86_pa_checked : Scalar.distance (sourceCoefficient 0 87 1 0) v86_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v86_pb : Scalar.QComplex := ((2845864916857358790562261 : Int)/10^30,(-431462190152239403159980723 : Int)/10^30)
theorem v86_pb_checked : Scalar.distance (sourceCoefficient 0 87 1 1) v86_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v86_pg : Scalar.QComplex := ((-93083763759555458819542 : Int)/10^30,(-613967628354380850448 : Int)/10^30)
theorem v86_pg_checked : Scalar.distance (sourceCoefficient 0 87 1 2) v86_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v86_mb : Scalar.QComplex := ((2473531419446087436136034 : Int)/10^30,(-431464485352397463313709319 : Int)/10^30)
theorem v86_mb_checked : Scalar.distance (sourceCoefficient 0 87 3 1) v86_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v86_mg : Scalar.QComplex := ((-93084258926627267317430 : Int)/10^30,(-533640303958769608544 : Int)/10^30)
theorem v86_mg_checked : Scalar.distance (sourceCoefficient 0 87 3 2) v86_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v86_upper : Scalar.QComplex := ((999988142275332232616497429923 : Int)/10^30,(4869836622505982019962996596 : Int)/10^30)
theorem v86_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 87 5) 1) 14) v86_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material86 : Material (0 : Basis) (87 : Basis) where
  plus := ![v86_pa,v86_pb,v86_pg]
  minus := ![(Primitive.Addresses.material86 1).one,v86_mb,v86_mg]
  upper := v86_upper
  lower := (Primitive.Addresses.material86 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v86_pa_checked.trans (by decide +kernel)
    · exact v86_pb_checked.trans (by decide +kernel)
    · exact v86_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 87 Primitive.Addresses.material86
    · exact v86_mb_checked.trans (by decide +kernel)
    · exact v86_mg_checked.trans (by decide +kernel)
  upper_error := v86_upper_checked
  lower_error := reuse_lower_error 0 87 Primitive.Addresses.material86

def v87_pa : Scalar.QComplex := ((999978325508061395831090940609 : Int)/10^30,(6583958846591277198626116111 : Int)/10^30)
theorem v87_pa_checked : Scalar.distance (sourceCoefficient 0 88 1 0) v87_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v87_pb : Scalar.QComplex := ((2840790995352445718797708 : Int)/10^30,(-431462208200413154150224568 : Int)/10^30)
theorem v87_pb_checked : Scalar.distance (sourceCoefficient 0 88 1 1) v87_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v87_pg : Scalar.QComplex := ((-93083769313207941237624 : Int)/10^30,(-612872990154441570382 : Int)/10^30)
theorem v87_pg_checked : Scalar.distance (sourceCoefficient 0 88 1 2) v87_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v87_mb : Scalar.QComplex := ((2468457484255666142785373 : Int)/10^30,(-431464499021998756345527634 : Int)/10^30)
theorem v87_mb_checked : Scalar.distance (sourceCoefficient 0 88 3 1) v87_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v87_mg : Scalar.QComplex := ((-93084263535654215983677 : Int)/10^30,(-532545661373862192648 : Int)/10^30)
theorem v87_mg_checked : Scalar.distance (sourceCoefficient 0 88 3 2) v87_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v87_upper : Scalar.QComplex := ((999988199473488392974957446769 : Int)/10^30,(4858077168056112604018641686 : Int)/10^30)
theorem v87_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 88 5) 1) 14) v87_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material87 : Material (0 : Basis) (88 : Basis) where
  plus := ![v87_pa,v87_pb,v87_pg]
  minus := ![(Primitive.Addresses.material87 1).one,v87_mb,v87_mg]
  upper := v87_upper
  lower := (Primitive.Addresses.material87 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v87_pa_checked.trans (by decide +kernel)
    · exact v87_pb_checked.trans (by decide +kernel)
    · exact v87_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 88 Primitive.Addresses.material87
    · exact v87_mb_checked.trans (by decide +kernel)
    · exact v87_mg_checked.trans (by decide +kernel)
  upper_error := v87_upper_checked
  lower_error := reuse_lower_error 0 88 Primitive.Addresses.material87

def v88_pa : Scalar.QComplex := ((999978431311132431755086653265 : Int)/10^30,(6567869709943782362603470989 : Int)/10^30)
theorem v88_pa_checked : Scalar.distance (sourceCoefficient 0 89 1 0) v88_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v88_pb : Scalar.QComplex := ((2833848851966462189295942 : Int)/10^30,(-431462232765048592378905418 : Int)/10^30)
theorem v88_pb_checked : Scalar.distance (sourceCoefficient 0 89 1 1) v88_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v88_pg : Scalar.QComplex := ((-93083776887388868045435 : Int)/10^30,(-611375305269587151692 : Int)/10^30)
theorem v88_pg_checked : Scalar.distance (sourceCoefficient 0 89 1 2) v88_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v88_mb : Scalar.QComplex := ((2461515322256385834430691 : Int)/10^30,(-431464517595867968465515528 : Int)/10^30)
theorem v88_mb_checked : Scalar.distance (sourceCoefficient 0 89 3 1) v88_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v88_mg : Scalar.QComplex := ((-93084269817397720171641 : Int)/10^30,(-531047970510487292780 : Int)/10^30)
theorem v88_mg_checked : Scalar.distance (sourceCoefficient 0 89 3 2) v88_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v88_upper : Scalar.QComplex := ((999988277508011589151989668889 : Int)/10^30,(4841987872764994613307433214 : Int)/10^30)
theorem v88_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 89 5) 1) 14) v88_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material88 : Material (0 : Basis) (89 : Basis) where
  plus := ![v88_pa,v88_pb,v88_pg]
  minus := ![(Primitive.Addresses.material88 1).one,v88_mb,v88_mg]
  upper := v88_upper
  lower := (Primitive.Addresses.material88 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v88_pa_checked.trans (by decide +kernel)
    · exact v88_pb_checked.trans (by decide +kernel)
    · exact v88_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 89 Primitive.Addresses.material88
    · exact v88_mb_checked.trans (by decide +kernel)
    · exact v88_mg_checked.trans (by decide +kernel)
  upper_error := v88_upper_checked
  lower_error := reuse_lower_error 0 89 Primitive.Addresses.material88

def v89_pa : Scalar.QComplex := ((999978603065349721358965739628 : Int)/10^30,(6541667331173670571871830429 : Int)/10^30)
theorem v89_pa_checked : Scalar.distance (sourceCoefficient 0 90 1 0) v89_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v89_pb : Scalar.QComplex := ((2822543046099985971983360 : Int)/10^30,(-431462272451645198552216145 : Int)/10^30)
theorem v89_pb_checked : Scalar.distance (sourceCoefficient 0 90 1 1) v89_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v89_pg : Scalar.QComplex := ((-93083789162340810676200 : Int)/10^30,(-608936211993476864230 : Int)/10^30)
theorem v89_pg_checked : Scalar.distance (sourceCoefficient 0 90 1 2) v89_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v89_mb : Scalar.QComplex := ((2450209486351832388892343 : Int)/10^30,(-431464547526048529330201421 : Int)/10^30)
theorem v89_mb_checked : Scalar.distance (sourceCoefficient 0 90 3 1) v89_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v89_mg : Scalar.QComplex := ((-93084279987517447676860 : Int)/10^30,(-528608867549832220906 : Int)/10^30)
theorem v89_mg_checked : Scalar.distance (sourceCoefficient 0 90 3 2) v89_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v89_upper : Scalar.QComplex := ((999988404039044375045373913643 : Int)/10^30,(4815785236588050432053776853 : Int)/10^30)
theorem v89_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 90 5) 1) 14) v89_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material89 : Material (0 : Basis) (90 : Basis) where
  plus := ![v89_pa,v89_pb,v89_pg]
  minus := ![(Primitive.Addresses.material89 1).one,v89_mb,v89_mg]
  upper := v89_upper
  lower := (Primitive.Addresses.material89 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v89_pa_checked.trans (by decide +kernel)
    · exact v89_pb_checked.trans (by decide +kernel)
    · exact v89_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 90 Primitive.Addresses.material89
    · exact v89_mb_checked.trans (by decide +kernel)
    · exact v89_mg_checked.trans (by decide +kernel)
  upper_error := v89_upper_checked
  lower_error := reuse_lower_error 0 90 Primitive.Addresses.material89

def v90_pa : Scalar.QComplex := ((999978699518423295088366267047 : Int)/10^30,(6526906575315324959052916005 : Int)/10^30)
theorem v90_pa_checked : Scalar.distance (sourceCoefficient 0 91 1 0) v90_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v90_pb : Scalar.QComplex := ((2816174073715288490819366 : Int)/10^30,(-431462294634616199314694893 : Int)/10^30)
theorem v90_pb_checked : Scalar.distance (sourceCoefficient 0 91 1 1) v90_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v90_pg : Scalar.QComplex := ((-93083796044434555677164 : Int)/10^30,(-607562181824791199387 : Int)/10^30)
theorem v90_pg_checked : Scalar.distance (sourceCoefficient 0 91 1 2) v90_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v90_mb : Scalar.QComplex := ((2443840497195689513236785 : Int)/10^30,(-431464564212874950232751873 : Int)/10^30)
theorem v90_mb_checked : Scalar.distance (sourceCoefficient 0 91 3 1) v90_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v90_mg : Scalar.QComplex := ((-93084285683882478605621 : Int)/10^30,(-527234831953823840206 : Int)/10^30)
theorem v90_mg_checked : Scalar.distance (sourceCoefficient 0 91 3 2) v90_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v90_upper : Scalar.QComplex := ((999988475016248767058441280316 : Int)/10^30,(4801024336244861916281489396 : Int)/10^30)
theorem v90_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 91 5) 1) 14) v90_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material90 : Material (0 : Basis) (91 : Basis) where
  plus := ![v90_pa,v90_pb,v90_pg]
  minus := ![(Primitive.Addresses.material90 1).one,v90_mb,v90_mg]
  upper := v90_upper
  lower := (Primitive.Addresses.material90 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v90_pa_checked.trans (by decide +kernel)
    · exact v90_pb_checked.trans (by decide +kernel)
    · exact v90_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 91 Primitive.Addresses.material90
    · exact v90_mb_checked.trans (by decide +kernel)
    · exact v90_mg_checked.trans (by decide +kernel)
  upper_error := v90_upper_checked
  lower_error := reuse_lower_error 0 91 Primitive.Addresses.material90

def v91_pa : Scalar.QComplex := ((999978907582347312196602200358 : Int)/10^30,(6494951148029765695439549148 : Int)/10^30)
theorem v91_pa_checked : Scalar.distance (sourceCoefficient 0 92 1 0) v91_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v91_pb : Scalar.QComplex := ((2802385944085906773957982 : Int)/10^30,(-431462342228891436695059202 : Int)/10^30)
theorem v91_pb_checked : Scalar.distance (sourceCoefficient 0 92 1 1) v91_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v91_pg : Scalar.QComplex := ((-93083810862350974730109 : Int)/10^30,(-604587556436660017658 : Int)/10^30)
theorem v91_pg_checked : Scalar.distance (sourceCoefficient 0 92 1 2) v91_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v91_mb : Scalar.QComplex := ((2430052331628542642772758 : Int)/10^30,(-431464599908597590238972943 : Int)/10^30)
theorem v91_mb_checked : Scalar.distance (sourceCoefficient 0 92 3 1) v91_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v91_mg : Scalar.QComplex := ((-93084297934825642468063 : Int)/10^30,(-524260194886087142113 : Int)/10^30)
theorem v91_mg_checked : Scalar.distance (sourceCoefficient 0 92 3 2) v91_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v91_upper : Scalar.QComplex := ((999988627927694376235276132945 : Int)/10^30,(4769068597453700404544648385 : Int)/10^30)
theorem v91_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 92 5) 1) 14) v91_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material91 : Material (0 : Basis) (92 : Basis) where
  plus := ![v91_pa,v91_pb,v91_pg]
  minus := ![(Primitive.Addresses.material91 1).one,v91_mb,v91_mg]
  upper := v91_upper
  lower := (Primitive.Addresses.material91 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v91_pa_checked.trans (by decide +kernel)
    · exact v91_pb_checked.trans (by decide +kernel)
    · exact v91_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 92 Primitive.Addresses.material91
    · exact v91_mb_checked.trans (by decide +kernel)
    · exact v91_mg_checked.trans (by decide +kernel)
  upper_error := v91_upper_checked
  lower_error := reuse_lower_error 0 92 Primitive.Addresses.material91

def v92_pa : Scalar.QComplex := ((999979153188181661593291995932 : Int)/10^30,(6457026331610691534809551092 : Int)/10^30)
theorem v92_pa_checked : Scalar.distance (sourceCoefficient 0 93 1 0) v92_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v92_pb : Scalar.QComplex := ((2786022144352589988415636 : Int)/10^30,(-431462397951577210675999937 : Int)/10^30)
theorem v92_pb_checked : Scalar.distance (sourceCoefficient 0 93 1 1) v92_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v92_pg : Scalar.QComplex := ((-93083828304392691783223 : Int)/10^30,(-601057260536194643831 : Int)/10^30)
theorem v92_pg_checked : Scalar.distance (sourceCoefficient 0 93 1 2) v92_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v92_mb : Scalar.QComplex := ((2413688489902048194196101 : Int)/10^30,(-431464641510040444446291647 : Int)/10^30)
theorem v92_mb_checked : Scalar.distance (sourceCoefficient 0 93 3 1) v92_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v92_mg : Scalar.QComplex := ((-93084312330374501575337 : Int)/10^30,(-520729885248415833103 : Int)/10^30)
theorem v92_mg_checked : Scalar.distance (sourceCoefficient 0 93 3 2) v92_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v92_upper : Scalar.QComplex := ((999988808078370297740319117252 : Int)/10^30,(4731143413625796438427432053 : Int)/10^30)
theorem v92_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 93 5) 1) 14) v92_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material92 : Material (0 : Basis) (93 : Basis) where
  plus := ![v92_pa,v92_pb,v92_pg]
  minus := ![(Primitive.Addresses.material92 1).one,v92_mb,v92_mg]
  upper := v92_upper
  lower := (Primitive.Addresses.material92 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v92_pa_checked.trans (by decide +kernel)
    · exact v92_pb_checked.trans (by decide +kernel)
    · exact v92_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 93 Primitive.Addresses.material92
    · exact v92_mb_checked.trans (by decide +kernel)
    · exact v92_mg_checked.trans (by decide +kernel)
  upper_error := v92_upper_checked
  lower_error := reuse_lower_error 0 93 Primitive.Addresses.material92

def v93_pa : Scalar.QComplex := ((999979441450212482147085742073 : Int)/10^30,(6412228701556607765388781000 : Int)/10^30)
theorem v93_pa_checked : Scalar.distance (sourceCoefficient 0 94 1 0) v93_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v93_pb : Scalar.QComplex := ((2766692866203435497652827 : Int)/10^30,(-431462462706419230482520787 : Int)/10^30)
theorem v93_pb_checked : Scalar.distance (sourceCoefficient 0 94 1 1) v93_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v93_pg : Scalar.QComplex := ((-93083848706081057400285 : Int)/10^30,(-596887197459652368780 : Int)/10^30)
theorem v93_pg_checked : Scalar.distance (sourceCoefficient 0 94 1 2) v93_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v93_mb : Scalar.QComplex := ((2394359163069555136743197 : Int)/10^30,(-431464689584561868716552637 : Int)/10^30)
theorem v93_mb_checked : Scalar.distance (sourceCoefficient 0 94 3 1) v93_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v93_mg : Scalar.QComplex := ((-93084329133478648324468 : Int)/10^30,(-516559806118840421153 : Int)/10^30)
theorem v93_mg_checked : Scalar.distance (sourceCoefficient 0 94 3 2) v93_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v93_upper : Scalar.QComplex := ((999989019023326321764464805776 : Int)/10^30,(4686345352778406066162281083 : Int)/10^30)
theorem v93_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 94 5) 1) 14) v93_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material93 : Material (0 : Basis) (94 : Basis) where
  plus := ![v93_pa,v93_pb,v93_pg]
  minus := ![(Primitive.Addresses.material93 1).one,v93_mb,v93_mg]
  upper := v93_upper
  lower := (Primitive.Addresses.material93 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v93_pa_checked.trans (by decide +kernel)
    · exact v93_pb_checked.trans (by decide +kernel)
    · exact v93_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 94 Primitive.Addresses.material93
    · exact v93_mb_checked.trans (by decide +kernel)
    · exact v93_mg_checked.trans (by decide +kernel)
  upper_error := v93_upper_checked
  lower_error := reuse_lower_error 0 94 Primitive.Addresses.material93

def v94_pa : Scalar.QComplex := ((999979724366576879574542167946 : Int)/10^30,(6367955381826268901575362916 : Int)/10^30)
theorem v94_pa_checked : Scalar.distance (sourceCoefficient 0 95 1 0) v94_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v94_pb : Scalar.QComplex := ((2747589820877293084305477 : Int)/10^30,(-431462525568971761004565214 : Int)/10^30)
theorem v94_pb_checked : Scalar.distance (sourceCoefficient 0 95 1 1) v94_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v94_pg : Scalar.QComplex := ((-93083868654844768909308 : Int)/10^30,(-592765941066755064335 : Int)/10^30)
theorem v94_pg_checked : Scalar.distance (sourceCoefficient 0 95 1 2) v94_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v94_mb : Scalar.QComplex := ((2375256070608797941045197 : Int)/10^30,(-431464735962023245399509271 : Int)/10^30)
theorem v94_mb_checked : Scalar.distance (sourceCoefficient 0 95 3 1) v94_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v94_mg : Scalar.QComplex := ((-93084345525776279424286 : Int)/10^30,(-512438534045590598439 : Int)/10^30)
theorem v94_mg_checked : Scalar.distance (sourceCoefficient 0 95 3 2) v94_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v94_upper : Scalar.QComplex := ((999989225527535938127159138426 : Int)/10^30,(4642071610699997253349934277 : Int)/10^30)
theorem v94_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 95 5) 1) 14) v94_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material94 : Material (0 : Basis) (95 : Basis) where
  plus := ![v94_pa,v94_pb,v94_pg]
  minus := ![(Primitive.Addresses.material94 1).one,v94_mb,v94_mg]
  upper := v94_upper
  lower := (Primitive.Addresses.material94 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v94_pa_checked.trans (by decide +kernel)
    · exact v94_pb_checked.trans (by decide +kernel)
    · exact v94_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 95 Primitive.Addresses.material94
    · exact v94_mb_checked.trans (by decide +kernel)
    · exact v94_mg_checked.trans (by decide +kernel)
  upper_error := v94_upper_checked
  lower_error := reuse_lower_error 0 95 Primitive.Addresses.material94

def v95_pa : Scalar.QComplex := ((999979859549319245329769328215 : Int)/10^30,(6346691714882306818889673873 : Int)/10^30)
theorem v95_pa_checked : Scalar.distance (sourceCoefficient 0 96 1 0) v95_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v95_pb : Scalar.QComplex := ((2738414978295992082178722 : Int)/10^30,(-431462555359829459205074057 : Int)/10^30)
theorem v95_pb_checked : Scalar.distance (sourceCoefficient 0 96 1 1) v95_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v95_pg : Scalar.QComplex := ((-93083878160196805324332 : Int)/10^30,(-590786577016352419107 : Int)/10^30)
theorem v95_pg_checked : Scalar.distance (sourceCoefficient 0 96 1 2) v95_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v95_mb : Scalar.QComplex := ((2366081205735541679833468 : Int)/10^30,(-431464757835393923009853087 : Int)/10^30)
theorem v95_mb_checked : Scalar.distance (sourceCoefficient 0 96 3 1) v95_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v95_mg : Scalar.QComplex := ((-93084353323022748312377 : Int)/10^30,(-510459162529504948319 : Int)/10^30)
theorem v95_mg_checked : Scalar.distance (sourceCoefficient 0 96 3 2) v95_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v95_upper : Scalar.QComplex := ((999989324010916844585199672939 : Int)/10^30,(4620807742112619637210511572 : Int)/10^30)
theorem v95_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 96 5) 1) 14) v95_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material95 : Material (0 : Basis) (96 : Basis) where
  plus := ![v95_pa,v95_pb,v95_pg]
  minus := ![(Primitive.Addresses.material95 1).one,v95_mb,v95_mg]
  upper := v95_upper
  lower := (Primitive.Addresses.material95 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v95_pa_checked.trans (by decide +kernel)
    · exact v95_pb_checked.trans (by decide +kernel)
    · exact v95_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 96 Primitive.Addresses.material95
    · exact v95_mb_checked.trans (by decide +kernel)
    · exact v95_mg_checked.trans (by decide +kernel)
  upper_error := v95_upper_checked
  lower_error := reuse_lower_error 0 96 Primitive.Addresses.material95

def v96_pa : Scalar.QComplex := ((999980321211093753023744568467 : Int)/10^30,(6273530948179114217845965495 : Int)/10^30)
theorem v96_pa_checked : Scalar.distance (sourceCoefficient 0 97 1 0) v96_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v96_pb : Scalar.QComplex := ((2706847592081474224093017 : Int)/10^30,(-431462655872408262438876291 : Int)/10^30)
theorem v96_pb_checked : Scalar.distance (sourceCoefficient 0 97 1 1) v96_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v96_pg : Scalar.QComplex := ((-93083910489618987870947 : Int)/10^30,(-583976285180201520428 : Int)/10^30)
theorem v96_pg_checked : Scalar.distance (sourceCoefficient 0 97 1 2) v96_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v96_mb : Scalar.QComplex := ((2334513744537175821545044 : Int)/10^30,(-431464831106702739985550536 : Int)/10^30)
theorem v96_mb_checked : Scalar.distance (sourceCoefficient 0 97 3 1) v96_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v96_mg : Scalar.QComplex := ((-93084379775457762697524 : Int)/10^30,(-503648845330301665538 : Int)/10^30)
theorem v96_mg_checked : Scalar.distance (sourceCoefficient 0 97 3 2) v96_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v96_upper : Scalar.QComplex := ((999989659403157524495406885319 : Int)/10^30,(4547646287587453801957125210 : Int)/10^30)
theorem v96_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 97 5) 1) 14) v96_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material96 : Material (0 : Basis) (97 : Basis) where
  plus := ![v96_pa,v96_pb,v96_pg]
  minus := ![(Primitive.Addresses.material96 1).one,v96_mb,v96_mg]
  upper := v96_upper
  lower := (Primitive.Addresses.material96 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v96_pa_checked.trans (by decide +kernel)
    · exact v96_pb_checked.trans (by decide +kernel)
    · exact v96_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 97 Primitive.Addresses.material96
    · exact v96_mb_checked.trans (by decide +kernel)
    · exact v96_mg_checked.trans (by decide +kernel)
  upper_error := v96_upper_checked
  lower_error := reuse_lower_error 0 97 Primitive.Addresses.material96

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
