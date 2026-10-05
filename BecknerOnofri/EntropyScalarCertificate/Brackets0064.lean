import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0160
import BecknerOnofri.EntropyScalarCertificate.Bessel0161
import BecknerOnofri.EntropyScalarCertificate.Bessel0162
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0064
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1024b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨0,by decide⟩
def lo1024b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨1,by decide⟩
def lo1024 : CheckedMoment :=
  CheckedMoment.ofBessel lo1024b1 lo1024b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1024b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨5,by decide⟩
def hi1024b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨6,by decide⟩
def hi1024 : CheckedMoment :=
  CheckedMoment.ofBessel hi1024b1 hi1024b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1024 : meanBracketCheck (253/500) lo1024 hi1024=true := by decide +kernel
def bracket1024 : MeanBracket := meanBracketOfMoments (253/500) lo1024 hi1024 accepted1024
def lo1025b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨10,by decide⟩
def lo1025b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨11,by decide⟩
def lo1025 : CheckedMoment :=
  CheckedMoment.ofBessel lo1025b1 lo1025b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1025b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨15,by decide⟩
def hi1025b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨16,by decide⟩
def hi1025 : CheckedMoment :=
  CheckedMoment.ofBessel hi1025b1 hi1025b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1025 : meanBracketCheck (507/1000) lo1025 hi1025=true := by decide +kernel
def bracket1025 : MeanBracket := meanBracketOfMoments (507/1000) lo1025 hi1025 accepted1025
def lo1026b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨20,by decide⟩
def lo1026b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨21,by decide⟩
def lo1026 : CheckedMoment :=
  CheckedMoment.ofBessel lo1026b1 lo1026b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1026b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨25,by decide⟩
def hi1026b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨26,by decide⟩
def hi1026 : CheckedMoment :=
  CheckedMoment.ofBessel hi1026b1 hi1026b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1026 : meanBracketCheck (127/250) lo1026 hi1026=true := by decide +kernel
def bracket1026 : MeanBracket := meanBracketOfMoments (127/250) lo1026 hi1026 accepted1026
def lo1027b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨30,by decide⟩
def lo1027b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨31,by decide⟩
def lo1027 : CheckedMoment :=
  CheckedMoment.ofBessel lo1027b1 lo1027b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1027b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨35,by decide⟩
def hi1027b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨36,by decide⟩
def hi1027 : CheckedMoment :=
  CheckedMoment.ofBessel hi1027b1 hi1027b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1027 : meanBracketCheck (509/1000) lo1027 hi1027=true := by decide +kernel
def bracket1027 : MeanBracket := meanBracketOfMoments (509/1000) lo1027 hi1027 accepted1027
def lo1028b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨40,by decide⟩
def lo1028b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨41,by decide⟩
def lo1028 : CheckedMoment :=
  CheckedMoment.ofBessel lo1028b1 lo1028b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1028b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨45,by decide⟩
def hi1028b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨46,by decide⟩
def hi1028 : CheckedMoment :=
  CheckedMoment.ofBessel hi1028b1 hi1028b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1028 : meanBracketCheck (51/100) lo1028 hi1028=true := by decide +kernel
def bracket1028 : MeanBracket := meanBracketOfMoments (51/100) lo1028 hi1028 accepted1028
def lo1029b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨50,by decide⟩
def lo1029b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨51,by decide⟩
def lo1029 : CheckedMoment :=
  CheckedMoment.ofBessel lo1029b1 lo1029b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1029b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨55,by decide⟩
def hi1029b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨56,by decide⟩
def hi1029 : CheckedMoment :=
  CheckedMoment.ofBessel hi1029b1 hi1029b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1029 : meanBracketCheck (511/1000) lo1029 hi1029=true := by decide +kernel
def bracket1029 : MeanBracket := meanBracketOfMoments (511/1000) lo1029 hi1029 accepted1029
def lo1030b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨60,by decide⟩
def lo1030b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨61,by decide⟩
def lo1030 : CheckedMoment :=
  CheckedMoment.ofBessel lo1030b1 lo1030b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1030b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨1,by decide⟩
def hi1030b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨2,by decide⟩
def hi1030 : CheckedMoment :=
  CheckedMoment.ofBessel hi1030b1 hi1030b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1030 : meanBracketCheck (64/125) lo1030 hi1030=true := by decide +kernel
def bracket1030 : MeanBracket := meanBracketOfMoments (64/125) lo1030 hi1030 accepted1030
def lo1031b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨6,by decide⟩
def lo1031b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨7,by decide⟩
def lo1031 : CheckedMoment :=
  CheckedMoment.ofBessel lo1031b1 lo1031b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1031b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨11,by decide⟩
def hi1031b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨12,by decide⟩
def hi1031 : CheckedMoment :=
  CheckedMoment.ofBessel hi1031b1 hi1031b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1031 : meanBracketCheck (513/1000) lo1031 hi1031=true := by decide +kernel
def bracket1031 : MeanBracket := meanBracketOfMoments (513/1000) lo1031 hi1031 accepted1031
def lo1032b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨16,by decide⟩
def lo1032b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨17,by decide⟩
def lo1032 : CheckedMoment :=
  CheckedMoment.ofBessel lo1032b1 lo1032b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1032b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨21,by decide⟩
def hi1032b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨22,by decide⟩
def hi1032 : CheckedMoment :=
  CheckedMoment.ofBessel hi1032b1 hi1032b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1032 : meanBracketCheck (257/500) lo1032 hi1032=true := by decide +kernel
def bracket1032 : MeanBracket := meanBracketOfMoments (257/500) lo1032 hi1032 accepted1032
def lo1033b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨26,by decide⟩
def lo1033b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨27,by decide⟩
def lo1033 : CheckedMoment :=
  CheckedMoment.ofBessel lo1033b1 lo1033b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1033b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨31,by decide⟩
def hi1033b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨32,by decide⟩
def hi1033 : CheckedMoment :=
  CheckedMoment.ofBessel hi1033b1 hi1033b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1033 : meanBracketCheck (103/200) lo1033 hi1033=true := by decide +kernel
def bracket1033 : MeanBracket := meanBracketOfMoments (103/200) lo1033 hi1033 accepted1033
def lo1034b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨36,by decide⟩
def lo1034b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨37,by decide⟩
def lo1034 : CheckedMoment :=
  CheckedMoment.ofBessel lo1034b1 lo1034b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1034b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨41,by decide⟩
def hi1034b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨42,by decide⟩
def hi1034 : CheckedMoment :=
  CheckedMoment.ofBessel hi1034b1 hi1034b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1034 : meanBracketCheck (129/250) lo1034 hi1034=true := by decide +kernel
def bracket1034 : MeanBracket := meanBracketOfMoments (129/250) lo1034 hi1034 accepted1034
def lo1035b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨46,by decide⟩
def lo1035b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨47,by decide⟩
def lo1035 : CheckedMoment :=
  CheckedMoment.ofBessel lo1035b1 lo1035b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1035b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨51,by decide⟩
def hi1035b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨52,by decide⟩
def hi1035 : CheckedMoment :=
  CheckedMoment.ofBessel hi1035b1 hi1035b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1035 : meanBracketCheck (517/1000) lo1035 hi1035=true := by decide +kernel
def bracket1035 : MeanBracket := meanBracketOfMoments (517/1000) lo1035 hi1035 accepted1035
def lo1036b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨56,by decide⟩
def lo1036b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨57,by decide⟩
def lo1036 : CheckedMoment :=
  CheckedMoment.ofBessel lo1036b1 lo1036b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1036b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨61,by decide⟩
def hi1036b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨62,by decide⟩
def hi1036 : CheckedMoment :=
  CheckedMoment.ofBessel hi1036b1 hi1036b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1036 : meanBracketCheck (259/500) lo1036 hi1036=true := by decide +kernel
def bracket1036 : MeanBracket := meanBracketOfMoments (259/500) lo1036 hi1036 accepted1036
def lo1037b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨2,by decide⟩
def lo1037b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨3,by decide⟩
def lo1037 : CheckedMoment :=
  CheckedMoment.ofBessel lo1037b1 lo1037b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1037b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨7,by decide⟩
def hi1037b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨8,by decide⟩
def hi1037 : CheckedMoment :=
  CheckedMoment.ofBessel hi1037b1 hi1037b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1037 : meanBracketCheck (519/1000) lo1037 hi1037=true := by decide +kernel
def bracket1037 : MeanBracket := meanBracketOfMoments (519/1000) lo1037 hi1037 accepted1037
def lo1038b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨12,by decide⟩
def lo1038b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨13,by decide⟩
def lo1038 : CheckedMoment :=
  CheckedMoment.ofBessel lo1038b1 lo1038b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1038b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨17,by decide⟩
def hi1038b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨18,by decide⟩
def hi1038 : CheckedMoment :=
  CheckedMoment.ofBessel hi1038b1 hi1038b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1038 : meanBracketCheck (13/25) lo1038 hi1038=true := by decide +kernel
def bracket1038 : MeanBracket := meanBracketOfMoments (13/25) lo1038 hi1038 accepted1038
def lo1039b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨22,by decide⟩
def lo1039b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨23,by decide⟩
def lo1039 : CheckedMoment :=
  CheckedMoment.ofBessel lo1039b1 lo1039b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1039b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨27,by decide⟩
def hi1039b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨28,by decide⟩
def hi1039 : CheckedMoment :=
  CheckedMoment.ofBessel hi1039b1 hi1039b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1039 : meanBracketCheck (521/1000) lo1039 hi1039=true := by decide +kernel
def bracket1039 : MeanBracket := meanBracketOfMoments (521/1000) lo1039 hi1039 accepted1039
#print axioms bracket1024
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0064
