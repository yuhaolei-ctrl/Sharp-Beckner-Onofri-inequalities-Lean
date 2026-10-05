module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0167
public import BecknerOnofri.EntropyScalarCertificate.Bessel0168
public import BecknerOnofri.EntropyScalarCertificate.Bessel0169

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0067
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1072b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨32,by decide⟩
def lo1072b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨33,by decide⟩
def lo1072 : CheckedMoment :=
  CheckedMoment.ofBessel lo1072b1 lo1072b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1072b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨37,by decide⟩
def hi1072b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨38,by decide⟩
def hi1072 : CheckedMoment :=
  CheckedMoment.ofBessel hi1072b1 hi1072b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1072 : meanBracketCheck (277/500) lo1072 hi1072=true := by decide +kernel
def bracket1072 : MeanBracket := meanBracketOfMoments (277/500) lo1072 hi1072 accepted1072
def lo1073b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨42,by decide⟩
def lo1073b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨43,by decide⟩
def lo1073 : CheckedMoment :=
  CheckedMoment.ofBessel lo1073b1 lo1073b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1073b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨47,by decide⟩
def hi1073b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨48,by decide⟩
def hi1073 : CheckedMoment :=
  CheckedMoment.ofBessel hi1073b1 hi1073b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1073 : meanBracketCheck (111/200) lo1073 hi1073=true := by decide +kernel
def bracket1073 : MeanBracket := meanBracketOfMoments (111/200) lo1073 hi1073 accepted1073
def lo1074b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨52,by decide⟩
def lo1074b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨53,by decide⟩
def lo1074 : CheckedMoment :=
  CheckedMoment.ofBessel lo1074b1 lo1074b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1074b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨57,by decide⟩
def hi1074b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨58,by decide⟩
def hi1074 : CheckedMoment :=
  CheckedMoment.ofBessel hi1074b1 hi1074b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1074 : meanBracketCheck (139/250) lo1074 hi1074=true := by decide +kernel
def bracket1074 : MeanBracket := meanBracketOfMoments (139/250) lo1074 hi1074 accepted1074
def lo1075b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨62,by decide⟩
def lo1075b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨63,by decide⟩
def lo1075 : CheckedMoment :=
  CheckedMoment.ofBessel lo1075b1 lo1075b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1075b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨3,by decide⟩
def hi1075b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨4,by decide⟩
def hi1075 : CheckedMoment :=
  CheckedMoment.ofBessel hi1075b1 hi1075b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1075 : meanBracketCheck (557/1000) lo1075 hi1075=true := by decide +kernel
def bracket1075 : MeanBracket := meanBracketOfMoments (557/1000) lo1075 hi1075 accepted1075
def lo1076b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨8,by decide⟩
def lo1076b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨9,by decide⟩
def lo1076 : CheckedMoment :=
  CheckedMoment.ofBessel lo1076b1 lo1076b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1076b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨13,by decide⟩
def hi1076b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨14,by decide⟩
def hi1076 : CheckedMoment :=
  CheckedMoment.ofBessel hi1076b1 hi1076b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1076 : meanBracketCheck (279/500) lo1076 hi1076=true := by decide +kernel
def bracket1076 : MeanBracket := meanBracketOfMoments (279/500) lo1076 hi1076 accepted1076
def lo1077b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨18,by decide⟩
def lo1077b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨19,by decide⟩
def lo1077 : CheckedMoment :=
  CheckedMoment.ofBessel lo1077b1 lo1077b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1077b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨23,by decide⟩
def hi1077b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨24,by decide⟩
def hi1077 : CheckedMoment :=
  CheckedMoment.ofBessel hi1077b1 hi1077b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1077 : meanBracketCheck (559/1000) lo1077 hi1077=true := by decide +kernel
def bracket1077 : MeanBracket := meanBracketOfMoments (559/1000) lo1077 hi1077 accepted1077
def lo1078b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨28,by decide⟩
def lo1078b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨29,by decide⟩
def lo1078 : CheckedMoment :=
  CheckedMoment.ofBessel lo1078b1 lo1078b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1078b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨33,by decide⟩
def hi1078b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨34,by decide⟩
def hi1078 : CheckedMoment :=
  CheckedMoment.ofBessel hi1078b1 hi1078b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1078 : meanBracketCheck (14/25) lo1078 hi1078=true := by decide +kernel
def bracket1078 : MeanBracket := meanBracketOfMoments (14/25) lo1078 hi1078 accepted1078
def lo1079b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨38,by decide⟩
def lo1079b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨39,by decide⟩
def lo1079 : CheckedMoment :=
  CheckedMoment.ofBessel lo1079b1 lo1079b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1079b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨43,by decide⟩
def hi1079b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨44,by decide⟩
def hi1079 : CheckedMoment :=
  CheckedMoment.ofBessel hi1079b1 hi1079b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1079 : meanBracketCheck (561/1000) lo1079 hi1079=true := by decide +kernel
def bracket1079 : MeanBracket := meanBracketOfMoments (561/1000) lo1079 hi1079 accepted1079
def lo1080b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨48,by decide⟩
def lo1080b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨49,by decide⟩
def lo1080 : CheckedMoment :=
  CheckedMoment.ofBessel lo1080b1 lo1080b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1080b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨53,by decide⟩
def hi1080b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨54,by decide⟩
def hi1080 : CheckedMoment :=
  CheckedMoment.ofBessel hi1080b1 hi1080b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1080 : meanBracketCheck (281/500) lo1080 hi1080=true := by decide +kernel
def bracket1080 : MeanBracket := meanBracketOfMoments (281/500) lo1080 hi1080 accepted1080
def lo1081b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨58,by decide⟩
def lo1081b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨59,by decide⟩
def lo1081 : CheckedMoment :=
  CheckedMoment.ofBessel lo1081b1 lo1081b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1081b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨63,by decide⟩
def hi1081b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨0,by decide⟩
def hi1081 : CheckedMoment :=
  CheckedMoment.ofBessel hi1081b1 hi1081b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1081 : meanBracketCheck (563/1000) lo1081 hi1081=true := by decide +kernel
def bracket1081 : MeanBracket := meanBracketOfMoments (563/1000) lo1081 hi1081 accepted1081
def lo1082b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨4,by decide⟩
def lo1082b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨5,by decide⟩
def lo1082 : CheckedMoment :=
  CheckedMoment.ofBessel lo1082b1 lo1082b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1082b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨9,by decide⟩
def hi1082b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨10,by decide⟩
def hi1082 : CheckedMoment :=
  CheckedMoment.ofBessel hi1082b1 hi1082b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1082 : meanBracketCheck (141/250) lo1082 hi1082=true := by decide +kernel
def bracket1082 : MeanBracket := meanBracketOfMoments (141/250) lo1082 hi1082 accepted1082
def lo1083b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨14,by decide⟩
def lo1083b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨15,by decide⟩
def lo1083 : CheckedMoment :=
  CheckedMoment.ofBessel lo1083b1 lo1083b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1083b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨19,by decide⟩
def hi1083b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨20,by decide⟩
def hi1083 : CheckedMoment :=
  CheckedMoment.ofBessel hi1083b1 hi1083b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1083 : meanBracketCheck (113/200) lo1083 hi1083=true := by decide +kernel
def bracket1083 : MeanBracket := meanBracketOfMoments (113/200) lo1083 hi1083 accepted1083
def lo1084b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨24,by decide⟩
def lo1084b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨25,by decide⟩
def lo1084 : CheckedMoment :=
  CheckedMoment.ofBessel lo1084b1 lo1084b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1084b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨29,by decide⟩
def hi1084b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨30,by decide⟩
def hi1084 : CheckedMoment :=
  CheckedMoment.ofBessel hi1084b1 hi1084b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1084 : meanBracketCheck (283/500) lo1084 hi1084=true := by decide +kernel
def bracket1084 : MeanBracket := meanBracketOfMoments (283/500) lo1084 hi1084 accepted1084
def lo1085b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨34,by decide⟩
def lo1085b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨35,by decide⟩
def lo1085 : CheckedMoment :=
  CheckedMoment.ofBessel lo1085b1 lo1085b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1085b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨39,by decide⟩
def hi1085b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨40,by decide⟩
def hi1085 : CheckedMoment :=
  CheckedMoment.ofBessel hi1085b1 hi1085b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1085 : meanBracketCheck (567/1000) lo1085 hi1085=true := by decide +kernel
def bracket1085 : MeanBracket := meanBracketOfMoments (567/1000) lo1085 hi1085 accepted1085
def lo1086b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨44,by decide⟩
def lo1086b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨45,by decide⟩
def lo1086 : CheckedMoment :=
  CheckedMoment.ofBessel lo1086b1 lo1086b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1086b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨49,by decide⟩
def hi1086b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨50,by decide⟩
def hi1086 : CheckedMoment :=
  CheckedMoment.ofBessel hi1086b1 hi1086b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1086 : meanBracketCheck (71/125) lo1086 hi1086=true := by decide +kernel
def bracket1086 : MeanBracket := meanBracketOfMoments (71/125) lo1086 hi1086 accepted1086
def lo1087b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨54,by decide⟩
def lo1087b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨55,by decide⟩
def lo1087 : CheckedMoment :=
  CheckedMoment.ofBessel lo1087b1 lo1087b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1087b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨59,by decide⟩
def hi1087b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨60,by decide⟩
def hi1087 : CheckedMoment :=
  CheckedMoment.ofBessel hi1087b1 hi1087b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1087 : meanBracketCheck (569/1000) lo1087 hi1087=true := by decide +kernel
def bracket1087 : MeanBracket := meanBracketOfMoments (569/1000) lo1087 hi1087 accepted1087
#print axioms bracket1072
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0067
