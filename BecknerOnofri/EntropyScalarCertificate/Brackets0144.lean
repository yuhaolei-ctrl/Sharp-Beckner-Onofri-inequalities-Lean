import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0360
import BecknerOnofri.EntropyScalarCertificate.Bessel0361
import BecknerOnofri.EntropyScalarCertificate.Bessel0362
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0144
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2304b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨0,by decide⟩
def lo2304b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨1,by decide⟩
def lo2304 : CheckedMoment :=
  CheckedMoment.ofBessel lo2304b1 lo2304b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2304b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨5,by decide⟩
def hi2304b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨6,by decide⟩
def hi2304 : CheckedMoment :=
  CheckedMoment.ofBessel hi2304b1 hi2304b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2304 : meanBracketCheck (4913/5000) lo2304 hi2304=true := by decide +kernel
def bracket2304 : MeanBracket := meanBracketOfMoments (4913/5000) lo2304 hi2304 accepted2304
def lo2305b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨10,by decide⟩
def lo2305b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨11,by decide⟩
def lo2305 : CheckedMoment :=
  CheckedMoment.ofBessel lo2305b1 lo2305b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2305b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨15,by decide⟩
def hi2305b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨16,by decide⟩
def hi2305 : CheckedMoment :=
  CheckedMoment.ofBessel hi2305b1 hi2305b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2305 : meanBracketCheck (9827/10000) lo2305 hi2305=true := by decide +kernel
def bracket2305 : MeanBracket := meanBracketOfMoments (9827/10000) lo2305 hi2305 accepted2305
def lo2306b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨20,by decide⟩
def lo2306b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨21,by decide⟩
def lo2306 : CheckedMoment :=
  CheckedMoment.ofBessel lo2306b1 lo2306b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2306b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨25,by decide⟩
def hi2306b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨26,by decide⟩
def hi2306 : CheckedMoment :=
  CheckedMoment.ofBessel hi2306b1 hi2306b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2306 : meanBracketCheck (2457/2500) lo2306 hi2306=true := by decide +kernel
def bracket2306 : MeanBracket := meanBracketOfMoments (2457/2500) lo2306 hi2306 accepted2306
def lo2307b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨30,by decide⟩
def lo2307b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨31,by decide⟩
def lo2307 : CheckedMoment :=
  CheckedMoment.ofBessel lo2307b1 lo2307b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2307b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨35,by decide⟩
def hi2307b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨36,by decide⟩
def hi2307 : CheckedMoment :=
  CheckedMoment.ofBessel hi2307b1 hi2307b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2307 : meanBracketCheck (9829/10000) lo2307 hi2307=true := by decide +kernel
def bracket2307 : MeanBracket := meanBracketOfMoments (9829/10000) lo2307 hi2307 accepted2307
def lo2308b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨40,by decide⟩
def lo2308b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨41,by decide⟩
def lo2308 : CheckedMoment :=
  CheckedMoment.ofBessel lo2308b1 lo2308b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2308b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨45,by decide⟩
def hi2308b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨46,by decide⟩
def hi2308 : CheckedMoment :=
  CheckedMoment.ofBessel hi2308b1 hi2308b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2308 : meanBracketCheck (983/1000) lo2308 hi2308=true := by decide +kernel
def bracket2308 : MeanBracket := meanBracketOfMoments (983/1000) lo2308 hi2308 accepted2308
def lo2309b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨50,by decide⟩
def lo2309b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨51,by decide⟩
def lo2309 : CheckedMoment :=
  CheckedMoment.ofBessel lo2309b1 lo2309b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2309b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨55,by decide⟩
def hi2309b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨56,by decide⟩
def hi2309 : CheckedMoment :=
  CheckedMoment.ofBessel hi2309b1 hi2309b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2309 : meanBracketCheck (9831/10000) lo2309 hi2309=true := by decide +kernel
def bracket2309 : MeanBracket := meanBracketOfMoments (9831/10000) lo2309 hi2309 accepted2309
def lo2310b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨60,by decide⟩
def lo2310b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨61,by decide⟩
def lo2310 : CheckedMoment :=
  CheckedMoment.ofBessel lo2310b1 lo2310b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2310b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨1,by decide⟩
def hi2310b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨2,by decide⟩
def hi2310 : CheckedMoment :=
  CheckedMoment.ofBessel hi2310b1 hi2310b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2310 : meanBracketCheck (1229/1250) lo2310 hi2310=true := by decide +kernel
def bracket2310 : MeanBracket := meanBracketOfMoments (1229/1250) lo2310 hi2310 accepted2310
def lo2311b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨6,by decide⟩
def lo2311b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨7,by decide⟩
def lo2311 : CheckedMoment :=
  CheckedMoment.ofBessel lo2311b1 lo2311b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2311b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨11,by decide⟩
def hi2311b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨12,by decide⟩
def hi2311 : CheckedMoment :=
  CheckedMoment.ofBessel hi2311b1 hi2311b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2311 : meanBracketCheck (9833/10000) lo2311 hi2311=true := by decide +kernel
def bracket2311 : MeanBracket := meanBracketOfMoments (9833/10000) lo2311 hi2311 accepted2311
def lo2312b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨16,by decide⟩
def lo2312b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨17,by decide⟩
def lo2312 : CheckedMoment :=
  CheckedMoment.ofBessel lo2312b1 lo2312b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2312b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨21,by decide⟩
def hi2312b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨22,by decide⟩
def hi2312 : CheckedMoment :=
  CheckedMoment.ofBessel hi2312b1 hi2312b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2312 : meanBracketCheck (4917/5000) lo2312 hi2312=true := by decide +kernel
def bracket2312 : MeanBracket := meanBracketOfMoments (4917/5000) lo2312 hi2312 accepted2312
def lo2313b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨26,by decide⟩
def lo2313b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨27,by decide⟩
def lo2313 : CheckedMoment :=
  CheckedMoment.ofBessel lo2313b1 lo2313b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2313b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨31,by decide⟩
def hi2313b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨32,by decide⟩
def hi2313 : CheckedMoment :=
  CheckedMoment.ofBessel hi2313b1 hi2313b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2313 : meanBracketCheck (1967/2000) lo2313 hi2313=true := by decide +kernel
def bracket2313 : MeanBracket := meanBracketOfMoments (1967/2000) lo2313 hi2313 accepted2313
def lo2314b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨36,by decide⟩
def lo2314b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨37,by decide⟩
def lo2314 : CheckedMoment :=
  CheckedMoment.ofBessel lo2314b1 lo2314b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2314b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨41,by decide⟩
def hi2314b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨42,by decide⟩
def hi2314 : CheckedMoment :=
  CheckedMoment.ofBessel hi2314b1 hi2314b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2314 : meanBracketCheck (2459/2500) lo2314 hi2314=true := by decide +kernel
def bracket2314 : MeanBracket := meanBracketOfMoments (2459/2500) lo2314 hi2314 accepted2314
def lo2315b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨46,by decide⟩
def lo2315b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨47,by decide⟩
def lo2315 : CheckedMoment :=
  CheckedMoment.ofBessel lo2315b1 lo2315b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2315b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨51,by decide⟩
def hi2315b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨52,by decide⟩
def hi2315 : CheckedMoment :=
  CheckedMoment.ofBessel hi2315b1 hi2315b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2315 : meanBracketCheck (9837/10000) lo2315 hi2315=true := by decide +kernel
def bracket2315 : MeanBracket := meanBracketOfMoments (9837/10000) lo2315 hi2315 accepted2315
def lo2316b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨56,by decide⟩
def lo2316b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨57,by decide⟩
def lo2316 : CheckedMoment :=
  CheckedMoment.ofBessel lo2316b1 lo2316b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2316b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨61,by decide⟩
def hi2316b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨62,by decide⟩
def hi2316 : CheckedMoment :=
  CheckedMoment.ofBessel hi2316b1 hi2316b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2316 : meanBracketCheck (4919/5000) lo2316 hi2316=true := by decide +kernel
def bracket2316 : MeanBracket := meanBracketOfMoments (4919/5000) lo2316 hi2316 accepted2316
def lo2317b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨2,by decide⟩
def lo2317b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨3,by decide⟩
def lo2317 : CheckedMoment :=
  CheckedMoment.ofBessel lo2317b1 lo2317b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2317b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨7,by decide⟩
def hi2317b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨8,by decide⟩
def hi2317 : CheckedMoment :=
  CheckedMoment.ofBessel hi2317b1 hi2317b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2317 : meanBracketCheck (9839/10000) lo2317 hi2317=true := by decide +kernel
def bracket2317 : MeanBracket := meanBracketOfMoments (9839/10000) lo2317 hi2317 accepted2317
def lo2318b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨12,by decide⟩
def lo2318b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨13,by decide⟩
def lo2318 : CheckedMoment :=
  CheckedMoment.ofBessel lo2318b1 lo2318b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2318b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨17,by decide⟩
def hi2318b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨18,by decide⟩
def hi2318 : CheckedMoment :=
  CheckedMoment.ofBessel hi2318b1 hi2318b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2318 : meanBracketCheck (123/125) lo2318 hi2318=true := by decide +kernel
def bracket2318 : MeanBracket := meanBracketOfMoments (123/125) lo2318 hi2318 accepted2318
def lo2319b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨22,by decide⟩
def lo2319b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨23,by decide⟩
def lo2319 : CheckedMoment :=
  CheckedMoment.ofBessel lo2319b1 lo2319b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2319b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨27,by decide⟩
def hi2319b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨28,by decide⟩
def hi2319 : CheckedMoment :=
  CheckedMoment.ofBessel hi2319b1 hi2319b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2319 : meanBracketCheck (9841/10000) lo2319 hi2319=true := by decide +kernel
def bracket2319 : MeanBracket := meanBracketOfMoments (9841/10000) lo2319 hi2319 accepted2319
#print axioms bracket2304
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0144
