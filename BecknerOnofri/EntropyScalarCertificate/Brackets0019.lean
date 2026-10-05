module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0047
public import BecknerOnofri.EntropyScalarCertificate.Bessel0048
public import BecknerOnofri.EntropyScalarCertificate.Bessel0049

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0019
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0304b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨32,by decide⟩
def lo0304b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨33,by decide⟩
def lo0304 : CheckedMoment :=
  CheckedMoment.ofBessel lo0304b1 lo0304b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0304b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨37,by decide⟩
def hi0304b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨38,by decide⟩
def hi0304 : CheckedMoment :=
  CheckedMoment.ofBessel hi0304b1 hi0304b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0304 : meanBracketCheck (1173/10000) lo0304 hi0304=true := by decide +kernel
def bracket0304 : MeanBracket := meanBracketOfMoments (1173/10000) lo0304 hi0304 accepted0304
def lo0305b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨42,by decide⟩
def lo0305b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨43,by decide⟩
def lo0305 : CheckedMoment :=
  CheckedMoment.ofBessel lo0305b1 lo0305b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0305b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨47,by decide⟩
def hi0305b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨48,by decide⟩
def hi0305 : CheckedMoment :=
  CheckedMoment.ofBessel hi0305b1 hi0305b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0305 : meanBracketCheck (47/400) lo0305 hi0305=true := by decide +kernel
def bracket0305 : MeanBracket := meanBracketOfMoments (47/400) lo0305 hi0305 accepted0305
def lo0306b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨52,by decide⟩
def lo0306b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨53,by decide⟩
def lo0306 : CheckedMoment :=
  CheckedMoment.ofBessel lo0306b1 lo0306b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0306b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨57,by decide⟩
def hi0306b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨58,by decide⟩
def hi0306 : CheckedMoment :=
  CheckedMoment.ofBessel hi0306b1 hi0306b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0306 : meanBracketCheck (1177/10000) lo0306 hi0306=true := by decide +kernel
def bracket0306 : MeanBracket := meanBracketOfMoments (1177/10000) lo0306 hi0306 accepted0306
def lo0307b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨62,by decide⟩
def lo0307b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨63,by decide⟩
def lo0307 : CheckedMoment :=
  CheckedMoment.ofBessel lo0307b1 lo0307b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0307b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨3,by decide⟩
def hi0307b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨4,by decide⟩
def hi0307 : CheckedMoment :=
  CheckedMoment.ofBessel hi0307b1 hi0307b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0307 : meanBracketCheck (1179/10000) lo0307 hi0307=true := by decide +kernel
def bracket0307 : MeanBracket := meanBracketOfMoments (1179/10000) lo0307 hi0307 accepted0307
def lo0308b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨8,by decide⟩
def lo0308b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨9,by decide⟩
def lo0308 : CheckedMoment :=
  CheckedMoment.ofBessel lo0308b1 lo0308b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0308b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨13,by decide⟩
def hi0308b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨14,by decide⟩
def hi0308 : CheckedMoment :=
  CheckedMoment.ofBessel hi0308b1 hi0308b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0308 : meanBracketCheck (1181/10000) lo0308 hi0308=true := by decide +kernel
def bracket0308 : MeanBracket := meanBracketOfMoments (1181/10000) lo0308 hi0308 accepted0308
def lo0309b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨18,by decide⟩
def lo0309b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨19,by decide⟩
def lo0309 : CheckedMoment :=
  CheckedMoment.ofBessel lo0309b1 lo0309b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0309b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨23,by decide⟩
def hi0309b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨24,by decide⟩
def hi0309 : CheckedMoment :=
  CheckedMoment.ofBessel hi0309b1 hi0309b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0309 : meanBracketCheck (1183/10000) lo0309 hi0309=true := by decide +kernel
def bracket0309 : MeanBracket := meanBracketOfMoments (1183/10000) lo0309 hi0309 accepted0309
def lo0310b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨28,by decide⟩
def lo0310b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨29,by decide⟩
def lo0310 : CheckedMoment :=
  CheckedMoment.ofBessel lo0310b1 lo0310b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0310b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨33,by decide⟩
def hi0310b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨34,by decide⟩
def hi0310 : CheckedMoment :=
  CheckedMoment.ofBessel hi0310b1 hi0310b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0310 : meanBracketCheck (237/2000) lo0310 hi0310=true := by decide +kernel
def bracket0310 : MeanBracket := meanBracketOfMoments (237/2000) lo0310 hi0310 accepted0310
def lo0311b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨38,by decide⟩
def lo0311b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨39,by decide⟩
def lo0311 : CheckedMoment :=
  CheckedMoment.ofBessel lo0311b1 lo0311b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0311b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨43,by decide⟩
def hi0311b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨44,by decide⟩
def hi0311 : CheckedMoment :=
  CheckedMoment.ofBessel hi0311b1 hi0311b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0311 : meanBracketCheck (1187/10000) lo0311 hi0311=true := by decide +kernel
def bracket0311 : MeanBracket := meanBracketOfMoments (1187/10000) lo0311 hi0311 accepted0311
def lo0312b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨48,by decide⟩
def lo0312b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨49,by decide⟩
def lo0312 : CheckedMoment :=
  CheckedMoment.ofBessel lo0312b1 lo0312b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0312b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨53,by decide⟩
def hi0312b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨54,by decide⟩
def hi0312 : CheckedMoment :=
  CheckedMoment.ofBessel hi0312b1 hi0312b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0312 : meanBracketCheck (1189/10000) lo0312 hi0312=true := by decide +kernel
def bracket0312 : MeanBracket := meanBracketOfMoments (1189/10000) lo0312 hi0312 accepted0312
def lo0313b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨58,by decide⟩
def lo0313b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨59,by decide⟩
def lo0313 : CheckedMoment :=
  CheckedMoment.ofBessel lo0313b1 lo0313b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0313b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨63,by decide⟩
def hi0313b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨0,by decide⟩
def hi0313 : CheckedMoment :=
  CheckedMoment.ofBessel hi0313b1 hi0313b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0313 : meanBracketCheck (1191/10000) lo0313 hi0313=true := by decide +kernel
def bracket0313 : MeanBracket := meanBracketOfMoments (1191/10000) lo0313 hi0313 accepted0313
def lo0314b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨4,by decide⟩
def lo0314b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨5,by decide⟩
def lo0314 : CheckedMoment :=
  CheckedMoment.ofBessel lo0314b1 lo0314b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0314b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨9,by decide⟩
def hi0314b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨10,by decide⟩
def hi0314 : CheckedMoment :=
  CheckedMoment.ofBessel hi0314b1 hi0314b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0314 : meanBracketCheck (1193/10000) lo0314 hi0314=true := by decide +kernel
def bracket0314 : MeanBracket := meanBracketOfMoments (1193/10000) lo0314 hi0314 accepted0314
def lo0315b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨14,by decide⟩
def lo0315b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨15,by decide⟩
def lo0315 : CheckedMoment :=
  CheckedMoment.ofBessel lo0315b1 lo0315b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0315b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨19,by decide⟩
def hi0315b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨20,by decide⟩
def hi0315 : CheckedMoment :=
  CheckedMoment.ofBessel hi0315b1 hi0315b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0315 : meanBracketCheck (239/2000) lo0315 hi0315=true := by decide +kernel
def bracket0315 : MeanBracket := meanBracketOfMoments (239/2000) lo0315 hi0315 accepted0315
def lo0316b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨24,by decide⟩
def lo0316b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨25,by decide⟩
def lo0316 : CheckedMoment :=
  CheckedMoment.ofBessel lo0316b1 lo0316b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0316b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨29,by decide⟩
def hi0316b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨30,by decide⟩
def hi0316 : CheckedMoment :=
  CheckedMoment.ofBessel hi0316b1 hi0316b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0316 : meanBracketCheck (1197/10000) lo0316 hi0316=true := by decide +kernel
def bracket0316 : MeanBracket := meanBracketOfMoments (1197/10000) lo0316 hi0316 accepted0316
def lo0317b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨34,by decide⟩
def lo0317b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨35,by decide⟩
def lo0317 : CheckedMoment :=
  CheckedMoment.ofBessel lo0317b1 lo0317b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0317b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨39,by decide⟩
def hi0317b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨40,by decide⟩
def hi0317 : CheckedMoment :=
  CheckedMoment.ofBessel hi0317b1 hi0317b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0317 : meanBracketCheck (1199/10000) lo0317 hi0317=true := by decide +kernel
def bracket0317 : MeanBracket := meanBracketOfMoments (1199/10000) lo0317 hi0317 accepted0317
def lo0318b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨44,by decide⟩
def lo0318b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨45,by decide⟩
def lo0318 : CheckedMoment :=
  CheckedMoment.ofBessel lo0318b1 lo0318b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0318b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨49,by decide⟩
def hi0318b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨50,by decide⟩
def hi0318 : CheckedMoment :=
  CheckedMoment.ofBessel hi0318b1 hi0318b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0318 : meanBracketCheck (1201/10000) lo0318 hi0318=true := by decide +kernel
def bracket0318 : MeanBracket := meanBracketOfMoments (1201/10000) lo0318 hi0318 accepted0318
def lo0319b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨54,by decide⟩
def lo0319b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨55,by decide⟩
def lo0319 : CheckedMoment :=
  CheckedMoment.ofBessel lo0319b1 lo0319b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0319b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨59,by decide⟩
def hi0319b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨60,by decide⟩
def hi0319 : CheckedMoment :=
  CheckedMoment.ofBessel hi0319b1 hi0319b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0319 : meanBracketCheck (1203/10000) lo0319 hi0319=true := by decide +kernel
def bracket0319 : MeanBracket := meanBracketOfMoments (1203/10000) lo0319 hi0319 accepted0319
#print axioms bracket0304
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0019
