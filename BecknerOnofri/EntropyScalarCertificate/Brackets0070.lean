module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0175
public import BecknerOnofri.EntropyScalarCertificate.Bessel0176
public import BecknerOnofri.EntropyScalarCertificate.Bessel0177

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0070
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1120b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨0,by decide⟩
def lo1120b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨1,by decide⟩
def lo1120 : CheckedMoment :=
  CheckedMoment.ofBessel lo1120b1 lo1120b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1120b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨5,by decide⟩
def hi1120b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨6,by decide⟩
def hi1120 : CheckedMoment :=
  CheckedMoment.ofBessel hi1120b1 hi1120b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1120 : meanBracketCheck (301/500) lo1120 hi1120=true := by decide +kernel
def bracket1120 : MeanBracket := meanBracketOfMoments (301/500) lo1120 hi1120 accepted1120
def lo1121b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨10,by decide⟩
def lo1121b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨11,by decide⟩
def lo1121 : CheckedMoment :=
  CheckedMoment.ofBessel lo1121b1 lo1121b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1121b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨15,by decide⟩
def hi1121b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨16,by decide⟩
def hi1121 : CheckedMoment :=
  CheckedMoment.ofBessel hi1121b1 hi1121b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1121 : meanBracketCheck (603/1000) lo1121 hi1121=true := by decide +kernel
def bracket1121 : MeanBracket := meanBracketOfMoments (603/1000) lo1121 hi1121 accepted1121
def lo1122b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨20,by decide⟩
def lo1122b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨21,by decide⟩
def lo1122 : CheckedMoment :=
  CheckedMoment.ofBessel lo1122b1 lo1122b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1122b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨25,by decide⟩
def hi1122b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨26,by decide⟩
def hi1122 : CheckedMoment :=
  CheckedMoment.ofBessel hi1122b1 hi1122b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1122 : meanBracketCheck (151/250) lo1122 hi1122=true := by decide +kernel
def bracket1122 : MeanBracket := meanBracketOfMoments (151/250) lo1122 hi1122 accepted1122
def lo1123b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨30,by decide⟩
def lo1123b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨31,by decide⟩
def lo1123 : CheckedMoment :=
  CheckedMoment.ofBessel lo1123b1 lo1123b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1123b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨35,by decide⟩
def hi1123b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨36,by decide⟩
def hi1123 : CheckedMoment :=
  CheckedMoment.ofBessel hi1123b1 hi1123b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1123 : meanBracketCheck (121/200) lo1123 hi1123=true := by decide +kernel
def bracket1123 : MeanBracket := meanBracketOfMoments (121/200) lo1123 hi1123 accepted1123
def lo1124b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨40,by decide⟩
def lo1124b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨41,by decide⟩
def lo1124 : CheckedMoment :=
  CheckedMoment.ofBessel lo1124b1 lo1124b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1124b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨45,by decide⟩
def hi1124b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨46,by decide⟩
def hi1124 : CheckedMoment :=
  CheckedMoment.ofBessel hi1124b1 hi1124b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1124 : meanBracketCheck (303/500) lo1124 hi1124=true := by decide +kernel
def bracket1124 : MeanBracket := meanBracketOfMoments (303/500) lo1124 hi1124 accepted1124
def lo1125b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨50,by decide⟩
def lo1125b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨51,by decide⟩
def lo1125 : CheckedMoment :=
  CheckedMoment.ofBessel lo1125b1 lo1125b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1125b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨55,by decide⟩
def hi1125b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨56,by decide⟩
def hi1125 : CheckedMoment :=
  CheckedMoment.ofBessel hi1125b1 hi1125b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1125 : meanBracketCheck (607/1000) lo1125 hi1125=true := by decide +kernel
def bracket1125 : MeanBracket := meanBracketOfMoments (607/1000) lo1125 hi1125 accepted1125
def lo1126b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨60,by decide⟩
def lo1126b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨61,by decide⟩
def lo1126 : CheckedMoment :=
  CheckedMoment.ofBessel lo1126b1 lo1126b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1126b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨1,by decide⟩
def hi1126b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨2,by decide⟩
def hi1126 : CheckedMoment :=
  CheckedMoment.ofBessel hi1126b1 hi1126b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1126 : meanBracketCheck (76/125) lo1126 hi1126=true := by decide +kernel
def bracket1126 : MeanBracket := meanBracketOfMoments (76/125) lo1126 hi1126 accepted1126
def lo1127b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨6,by decide⟩
def lo1127b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨7,by decide⟩
def lo1127 : CheckedMoment :=
  CheckedMoment.ofBessel lo1127b1 lo1127b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1127b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨11,by decide⟩
def hi1127b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨12,by decide⟩
def hi1127 : CheckedMoment :=
  CheckedMoment.ofBessel hi1127b1 hi1127b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1127 : meanBracketCheck (609/1000) lo1127 hi1127=true := by decide +kernel
def bracket1127 : MeanBracket := meanBracketOfMoments (609/1000) lo1127 hi1127 accepted1127
def lo1128b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨16,by decide⟩
def lo1128b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨17,by decide⟩
def lo1128 : CheckedMoment :=
  CheckedMoment.ofBessel lo1128b1 lo1128b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1128b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨21,by decide⟩
def hi1128b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨22,by decide⟩
def hi1128 : CheckedMoment :=
  CheckedMoment.ofBessel hi1128b1 hi1128b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1128 : meanBracketCheck (61/100) lo1128 hi1128=true := by decide +kernel
def bracket1128 : MeanBracket := meanBracketOfMoments (61/100) lo1128 hi1128 accepted1128
def lo1129b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨26,by decide⟩
def lo1129b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨27,by decide⟩
def lo1129 : CheckedMoment :=
  CheckedMoment.ofBessel lo1129b1 lo1129b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1129b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨31,by decide⟩
def hi1129b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨32,by decide⟩
def hi1129 : CheckedMoment :=
  CheckedMoment.ofBessel hi1129b1 hi1129b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1129 : meanBracketCheck (611/1000) lo1129 hi1129=true := by decide +kernel
def bracket1129 : MeanBracket := meanBracketOfMoments (611/1000) lo1129 hi1129 accepted1129
def lo1130b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨36,by decide⟩
def lo1130b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨37,by decide⟩
def lo1130 : CheckedMoment :=
  CheckedMoment.ofBessel lo1130b1 lo1130b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1130b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨41,by decide⟩
def hi1130b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨42,by decide⟩
def hi1130 : CheckedMoment :=
  CheckedMoment.ofBessel hi1130b1 hi1130b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1130 : meanBracketCheck (153/250) lo1130 hi1130=true := by decide +kernel
def bracket1130 : MeanBracket := meanBracketOfMoments (153/250) lo1130 hi1130 accepted1130
def lo1131b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨46,by decide⟩
def lo1131b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨47,by decide⟩
def lo1131 : CheckedMoment :=
  CheckedMoment.ofBessel lo1131b1 lo1131b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1131b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨51,by decide⟩
def hi1131b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨52,by decide⟩
def hi1131 : CheckedMoment :=
  CheckedMoment.ofBessel hi1131b1 hi1131b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1131 : meanBracketCheck (613/1000) lo1131 hi1131=true := by decide +kernel
def bracket1131 : MeanBracket := meanBracketOfMoments (613/1000) lo1131 hi1131 accepted1131
def lo1132b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨56,by decide⟩
def lo1132b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨57,by decide⟩
def lo1132 : CheckedMoment :=
  CheckedMoment.ofBessel lo1132b1 lo1132b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1132b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨61,by decide⟩
def hi1132b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨62,by decide⟩
def hi1132 : CheckedMoment :=
  CheckedMoment.ofBessel hi1132b1 hi1132b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1132 : meanBracketCheck (307/500) lo1132 hi1132=true := by decide +kernel
def bracket1132 : MeanBracket := meanBracketOfMoments (307/500) lo1132 hi1132 accepted1132
def lo1133b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨2,by decide⟩
def lo1133b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨3,by decide⟩
def lo1133 : CheckedMoment :=
  CheckedMoment.ofBessel lo1133b1 lo1133b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1133b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨7,by decide⟩
def hi1133b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨8,by decide⟩
def hi1133 : CheckedMoment :=
  CheckedMoment.ofBessel hi1133b1 hi1133b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1133 : meanBracketCheck (123/200) lo1133 hi1133=true := by decide +kernel
def bracket1133 : MeanBracket := meanBracketOfMoments (123/200) lo1133 hi1133 accepted1133
def lo1134b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨12,by decide⟩
def lo1134b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨13,by decide⟩
def lo1134 : CheckedMoment :=
  CheckedMoment.ofBessel lo1134b1 lo1134b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1134b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨17,by decide⟩
def hi1134b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨18,by decide⟩
def hi1134 : CheckedMoment :=
  CheckedMoment.ofBessel hi1134b1 hi1134b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1134 : meanBracketCheck (77/125) lo1134 hi1134=true := by decide +kernel
def bracket1134 : MeanBracket := meanBracketOfMoments (77/125) lo1134 hi1134 accepted1134
def lo1135b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨22,by decide⟩
def lo1135b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨23,by decide⟩
def lo1135 : CheckedMoment :=
  CheckedMoment.ofBessel lo1135b1 lo1135b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1135b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨27,by decide⟩
def hi1135b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨28,by decide⟩
def hi1135 : CheckedMoment :=
  CheckedMoment.ofBessel hi1135b1 hi1135b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1135 : meanBracketCheck (617/1000) lo1135 hi1135=true := by decide +kernel
def bracket1135 : MeanBracket := meanBracketOfMoments (617/1000) lo1135 hi1135 accepted1135
#print axioms bracket1120
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0070
