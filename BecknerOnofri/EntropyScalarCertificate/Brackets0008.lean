import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0020
import BecknerOnofri.EntropyScalarCertificate.Bessel0021
import BecknerOnofri.EntropyScalarCertificate.Bessel0022
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0008
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0128b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨0,by decide⟩
def lo0128b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨1,by decide⟩
def lo0128 : CheckedMoment :=
  CheckedMoment.ofBessel lo0128b1 lo0128b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0128b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨5,by decide⟩
def hi0128b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨6,by decide⟩
def hi0128 : CheckedMoment :=
  CheckedMoment.ofBessel hi0128b1 hi0128b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0128 : meanBracketCheck (821/10000) lo0128 hi0128=true := by decide +kernel
def bracket0128 : MeanBracket := meanBracketOfMoments (821/10000) lo0128 hi0128 accepted0128
def lo0129b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨10,by decide⟩
def lo0129b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨11,by decide⟩
def lo0129 : CheckedMoment :=
  CheckedMoment.ofBessel lo0129b1 lo0129b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0129b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨15,by decide⟩
def hi0129b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨16,by decide⟩
def hi0129 : CheckedMoment :=
  CheckedMoment.ofBessel hi0129b1 hi0129b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0129 : meanBracketCheck (823/10000) lo0129 hi0129=true := by decide +kernel
def bracket0129 : MeanBracket := meanBracketOfMoments (823/10000) lo0129 hi0129 accepted0129
def lo0130b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨20,by decide⟩
def lo0130b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨21,by decide⟩
def lo0130 : CheckedMoment :=
  CheckedMoment.ofBessel lo0130b1 lo0130b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0130b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨25,by decide⟩
def hi0130b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨26,by decide⟩
def hi0130 : CheckedMoment :=
  CheckedMoment.ofBessel hi0130b1 hi0130b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0130 : meanBracketCheck (33/400) lo0130 hi0130=true := by decide +kernel
def bracket0130 : MeanBracket := meanBracketOfMoments (33/400) lo0130 hi0130 accepted0130
def lo0131b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨30,by decide⟩
def lo0131b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨31,by decide⟩
def lo0131 : CheckedMoment :=
  CheckedMoment.ofBessel lo0131b1 lo0131b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0131b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨35,by decide⟩
def hi0131b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨36,by decide⟩
def hi0131 : CheckedMoment :=
  CheckedMoment.ofBessel hi0131b1 hi0131b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0131 : meanBracketCheck (827/10000) lo0131 hi0131=true := by decide +kernel
def bracket0131 : MeanBracket := meanBracketOfMoments (827/10000) lo0131 hi0131 accepted0131
def lo0132b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨40,by decide⟩
def lo0132b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨41,by decide⟩
def lo0132 : CheckedMoment :=
  CheckedMoment.ofBessel lo0132b1 lo0132b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0132b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨45,by decide⟩
def hi0132b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨46,by decide⟩
def hi0132 : CheckedMoment :=
  CheckedMoment.ofBessel hi0132b1 hi0132b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0132 : meanBracketCheck (829/10000) lo0132 hi0132=true := by decide +kernel
def bracket0132 : MeanBracket := meanBracketOfMoments (829/10000) lo0132 hi0132 accepted0132
def lo0133b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨50,by decide⟩
def lo0133b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨51,by decide⟩
def lo0133 : CheckedMoment :=
  CheckedMoment.ofBessel lo0133b1 lo0133b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0133b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨55,by decide⟩
def hi0133b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨56,by decide⟩
def hi0133 : CheckedMoment :=
  CheckedMoment.ofBessel hi0133b1 hi0133b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0133 : meanBracketCheck (831/10000) lo0133 hi0133=true := by decide +kernel
def bracket0133 : MeanBracket := meanBracketOfMoments (831/10000) lo0133 hi0133 accepted0133
def lo0134b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨60,by decide⟩
def lo0134b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨61,by decide⟩
def lo0134 : CheckedMoment :=
  CheckedMoment.ofBessel lo0134b1 lo0134b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0134b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨1,by decide⟩
def hi0134b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨2,by decide⟩
def hi0134 : CheckedMoment :=
  CheckedMoment.ofBessel hi0134b1 hi0134b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0134 : meanBracketCheck (833/10000) lo0134 hi0134=true := by decide +kernel
def bracket0134 : MeanBracket := meanBracketOfMoments (833/10000) lo0134 hi0134 accepted0134
def lo0135b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨6,by decide⟩
def lo0135b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨7,by decide⟩
def lo0135 : CheckedMoment :=
  CheckedMoment.ofBessel lo0135b1 lo0135b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0135b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨11,by decide⟩
def hi0135b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨12,by decide⟩
def hi0135 : CheckedMoment :=
  CheckedMoment.ofBessel hi0135b1 hi0135b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0135 : meanBracketCheck (167/2000) lo0135 hi0135=true := by decide +kernel
def bracket0135 : MeanBracket := meanBracketOfMoments (167/2000) lo0135 hi0135 accepted0135
def lo0136b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨16,by decide⟩
def lo0136b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨17,by decide⟩
def lo0136 : CheckedMoment :=
  CheckedMoment.ofBessel lo0136b1 lo0136b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0136b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨21,by decide⟩
def hi0136b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨22,by decide⟩
def hi0136 : CheckedMoment :=
  CheckedMoment.ofBessel hi0136b1 hi0136b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0136 : meanBracketCheck (837/10000) lo0136 hi0136=true := by decide +kernel
def bracket0136 : MeanBracket := meanBracketOfMoments (837/10000) lo0136 hi0136 accepted0136
def lo0137b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨26,by decide⟩
def lo0137b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨27,by decide⟩
def lo0137 : CheckedMoment :=
  CheckedMoment.ofBessel lo0137b1 lo0137b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0137b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨31,by decide⟩
def hi0137b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨32,by decide⟩
def hi0137 : CheckedMoment :=
  CheckedMoment.ofBessel hi0137b1 hi0137b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0137 : meanBracketCheck (839/10000) lo0137 hi0137=true := by decide +kernel
def bracket0137 : MeanBracket := meanBracketOfMoments (839/10000) lo0137 hi0137 accepted0137
def lo0138b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨36,by decide⟩
def lo0138b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨37,by decide⟩
def lo0138 : CheckedMoment :=
  CheckedMoment.ofBessel lo0138b1 lo0138b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0138b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨41,by decide⟩
def hi0138b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨42,by decide⟩
def hi0138 : CheckedMoment :=
  CheckedMoment.ofBessel hi0138b1 hi0138b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0138 : meanBracketCheck (841/10000) lo0138 hi0138=true := by decide +kernel
def bracket0138 : MeanBracket := meanBracketOfMoments (841/10000) lo0138 hi0138 accepted0138
def lo0139b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨46,by decide⟩
def lo0139b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨47,by decide⟩
def lo0139 : CheckedMoment :=
  CheckedMoment.ofBessel lo0139b1 lo0139b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0139b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨51,by decide⟩
def hi0139b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨52,by decide⟩
def hi0139 : CheckedMoment :=
  CheckedMoment.ofBessel hi0139b1 hi0139b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0139 : meanBracketCheck (843/10000) lo0139 hi0139=true := by decide +kernel
def bracket0139 : MeanBracket := meanBracketOfMoments (843/10000) lo0139 hi0139 accepted0139
def lo0140b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨56,by decide⟩
def lo0140b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨57,by decide⟩
def lo0140 : CheckedMoment :=
  CheckedMoment.ofBessel lo0140b1 lo0140b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0140b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨61,by decide⟩
def hi0140b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨62,by decide⟩
def hi0140 : CheckedMoment :=
  CheckedMoment.ofBessel hi0140b1 hi0140b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0140 : meanBracketCheck (169/2000) lo0140 hi0140=true := by decide +kernel
def bracket0140 : MeanBracket := meanBracketOfMoments (169/2000) lo0140 hi0140 accepted0140
def lo0141b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨2,by decide⟩
def lo0141b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨3,by decide⟩
def lo0141 : CheckedMoment :=
  CheckedMoment.ofBessel lo0141b1 lo0141b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0141b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨7,by decide⟩
def hi0141b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨8,by decide⟩
def hi0141 : CheckedMoment :=
  CheckedMoment.ofBessel hi0141b1 hi0141b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0141 : meanBracketCheck (847/10000) lo0141 hi0141=true := by decide +kernel
def bracket0141 : MeanBracket := meanBracketOfMoments (847/10000) lo0141 hi0141 accepted0141
def lo0142b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨12,by decide⟩
def lo0142b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨13,by decide⟩
def lo0142 : CheckedMoment :=
  CheckedMoment.ofBessel lo0142b1 lo0142b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0142b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨17,by decide⟩
def hi0142b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨18,by decide⟩
def hi0142 : CheckedMoment :=
  CheckedMoment.ofBessel hi0142b1 hi0142b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0142 : meanBracketCheck (849/10000) lo0142 hi0142=true := by decide +kernel
def bracket0142 : MeanBracket := meanBracketOfMoments (849/10000) lo0142 hi0142 accepted0142
def lo0143b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨22,by decide⟩
def lo0143b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨23,by decide⟩
def lo0143 : CheckedMoment :=
  CheckedMoment.ofBessel lo0143b1 lo0143b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0143b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨27,by decide⟩
def hi0143b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨28,by decide⟩
def hi0143 : CheckedMoment :=
  CheckedMoment.ofBessel hi0143b1 hi0143b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0143 : meanBracketCheck (851/10000) lo0143 hi0143=true := by decide +kernel
def bracket0143 : MeanBracket := meanBracketOfMoments (851/10000) lo0143 hi0143 accepted0143
#print axioms bracket0128
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0008
