import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0365
import BecknerOnofri.EntropyScalarCertificate.Bessel0366
import BecknerOnofri.EntropyScalarCertificate.Bessel0367
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0146
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2336b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨0,by decide⟩
def lo2336b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨1,by decide⟩
def lo2336 : CheckedMoment :=
  CheckedMoment.ofBessel lo2336b1 lo2336b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2336b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨5,by decide⟩
def hi2336b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨6,by decide⟩
def hi2336 : CheckedMoment :=
  CheckedMoment.ofBessel hi2336b1 hi2336b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2336 : meanBracketCheck (4929/5000) lo2336 hi2336=true := by decide +kernel
def bracket2336 : MeanBracket := meanBracketOfMoments (4929/5000) lo2336 hi2336 accepted2336
def lo2337b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨10,by decide⟩
def lo2337b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨11,by decide⟩
def lo2337 : CheckedMoment :=
  CheckedMoment.ofBessel lo2337b1 lo2337b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2337b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨15,by decide⟩
def hi2337b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨16,by decide⟩
def hi2337 : CheckedMoment :=
  CheckedMoment.ofBessel hi2337b1 hi2337b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2337 : meanBracketCheck (9859/10000) lo2337 hi2337=true := by decide +kernel
def bracket2337 : MeanBracket := meanBracketOfMoments (9859/10000) lo2337 hi2337 accepted2337
def lo2338b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨20,by decide⟩
def lo2338b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨21,by decide⟩
def lo2338 : CheckedMoment :=
  CheckedMoment.ofBessel lo2338b1 lo2338b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2338b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨25,by decide⟩
def hi2338b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨26,by decide⟩
def hi2338 : CheckedMoment :=
  CheckedMoment.ofBessel hi2338b1 hi2338b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2338 : meanBracketCheck (493/500) lo2338 hi2338=true := by decide +kernel
def bracket2338 : MeanBracket := meanBracketOfMoments (493/500) lo2338 hi2338 accepted2338
def lo2339b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨30,by decide⟩
def lo2339b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨31,by decide⟩
def lo2339 : CheckedMoment :=
  CheckedMoment.ofBessel lo2339b1 lo2339b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2339b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨35,by decide⟩
def hi2339b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨36,by decide⟩
def hi2339 : CheckedMoment :=
  CheckedMoment.ofBessel hi2339b1 hi2339b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2339 : meanBracketCheck (9861/10000) lo2339 hi2339=true := by decide +kernel
def bracket2339 : MeanBracket := meanBracketOfMoments (9861/10000) lo2339 hi2339 accepted2339
def lo2340b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨40,by decide⟩
def lo2340b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨41,by decide⟩
def lo2340 : CheckedMoment :=
  CheckedMoment.ofBessel lo2340b1 lo2340b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2340b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨45,by decide⟩
def hi2340b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨46,by decide⟩
def hi2340 : CheckedMoment :=
  CheckedMoment.ofBessel hi2340b1 hi2340b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2340 : meanBracketCheck (4931/5000) lo2340 hi2340=true := by decide +kernel
def bracket2340 : MeanBracket := meanBracketOfMoments (4931/5000) lo2340 hi2340 accepted2340
def lo2341b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨50,by decide⟩
def lo2341b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨51,by decide⟩
def lo2341 : CheckedMoment :=
  CheckedMoment.ofBessel lo2341b1 lo2341b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2341b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨55,by decide⟩
def hi2341b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨56,by decide⟩
def hi2341 : CheckedMoment :=
  CheckedMoment.ofBessel hi2341b1 hi2341b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2341 : meanBracketCheck (9863/10000) lo2341 hi2341=true := by decide +kernel
def bracket2341 : MeanBracket := meanBracketOfMoments (9863/10000) lo2341 hi2341 accepted2341
def lo2342b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨60,by decide⟩
def lo2342b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨61,by decide⟩
def lo2342 : CheckedMoment :=
  CheckedMoment.ofBessel lo2342b1 lo2342b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2342b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨1,by decide⟩
def hi2342b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨2,by decide⟩
def hi2342 : CheckedMoment :=
  CheckedMoment.ofBessel hi2342b1 hi2342b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2342 : meanBracketCheck (1233/1250) lo2342 hi2342=true := by decide +kernel
def bracket2342 : MeanBracket := meanBracketOfMoments (1233/1250) lo2342 hi2342 accepted2342
def lo2343b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨6,by decide⟩
def lo2343b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨7,by decide⟩
def lo2343 : CheckedMoment :=
  CheckedMoment.ofBessel lo2343b1 lo2343b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2343b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨11,by decide⟩
def hi2343b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨12,by decide⟩
def hi2343 : CheckedMoment :=
  CheckedMoment.ofBessel hi2343b1 hi2343b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2343 : meanBracketCheck (1973/2000) lo2343 hi2343=true := by decide +kernel
def bracket2343 : MeanBracket := meanBracketOfMoments (1973/2000) lo2343 hi2343 accepted2343
def lo2344b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨16,by decide⟩
def lo2344b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨17,by decide⟩
def lo2344 : CheckedMoment :=
  CheckedMoment.ofBessel lo2344b1 lo2344b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2344b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨21,by decide⟩
def hi2344b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨22,by decide⟩
def hi2344 : CheckedMoment :=
  CheckedMoment.ofBessel hi2344b1 hi2344b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2344 : meanBracketCheck (4933/5000) lo2344 hi2344=true := by decide +kernel
def bracket2344 : MeanBracket := meanBracketOfMoments (4933/5000) lo2344 hi2344 accepted2344
def lo2345b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨26,by decide⟩
def lo2345b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨27,by decide⟩
def lo2345 : CheckedMoment :=
  CheckedMoment.ofBessel lo2345b1 lo2345b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2345b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨31,by decide⟩
def hi2345b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨32,by decide⟩
def hi2345 : CheckedMoment :=
  CheckedMoment.ofBessel hi2345b1 hi2345b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2345 : meanBracketCheck (9867/10000) lo2345 hi2345=true := by decide +kernel
def bracket2345 : MeanBracket := meanBracketOfMoments (9867/10000) lo2345 hi2345 accepted2345
def lo2346b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨36,by decide⟩
def lo2346b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨37,by decide⟩
def lo2346 : CheckedMoment :=
  CheckedMoment.ofBessel lo2346b1 lo2346b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2346b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨41,by decide⟩
def hi2346b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨42,by decide⟩
def hi2346 : CheckedMoment :=
  CheckedMoment.ofBessel hi2346b1 hi2346b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2346 : meanBracketCheck (2467/2500) lo2346 hi2346=true := by decide +kernel
def bracket2346 : MeanBracket := meanBracketOfMoments (2467/2500) lo2346 hi2346 accepted2346
def lo2347b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨46,by decide⟩
def lo2347b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨47,by decide⟩
def lo2347 : CheckedMoment :=
  CheckedMoment.ofBessel lo2347b1 lo2347b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2347b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨51,by decide⟩
def hi2347b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨52,by decide⟩
def hi2347 : CheckedMoment :=
  CheckedMoment.ofBessel hi2347b1 hi2347b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2347 : meanBracketCheck (9869/10000) lo2347 hi2347=true := by decide +kernel
def bracket2347 : MeanBracket := meanBracketOfMoments (9869/10000) lo2347 hi2347 accepted2347
def lo2348b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨56,by decide⟩
def lo2348b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨57,by decide⟩
def lo2348 : CheckedMoment :=
  CheckedMoment.ofBessel lo2348b1 lo2348b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2348b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨61,by decide⟩
def hi2348b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨62,by decide⟩
def hi2348 : CheckedMoment :=
  CheckedMoment.ofBessel hi2348b1 hi2348b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2348 : meanBracketCheck (987/1000) lo2348 hi2348=true := by decide +kernel
def bracket2348 : MeanBracket := meanBracketOfMoments (987/1000) lo2348 hi2348 accepted2348
def lo2349b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨2,by decide⟩
def lo2349b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨3,by decide⟩
def lo2349 : CheckedMoment :=
  CheckedMoment.ofBessel lo2349b1 lo2349b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2349b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨7,by decide⟩
def hi2349b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨8,by decide⟩
def hi2349 : CheckedMoment :=
  CheckedMoment.ofBessel hi2349b1 hi2349b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2349 : meanBracketCheck (9871/10000) lo2349 hi2349=true := by decide +kernel
def bracket2349 : MeanBracket := meanBracketOfMoments (9871/10000) lo2349 hi2349 accepted2349
def lo2350b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨12,by decide⟩
def lo2350b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨13,by decide⟩
def lo2350 : CheckedMoment :=
  CheckedMoment.ofBessel lo2350b1 lo2350b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2350b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨17,by decide⟩
def hi2350b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨18,by decide⟩
def hi2350 : CheckedMoment :=
  CheckedMoment.ofBessel hi2350b1 hi2350b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2350 : meanBracketCheck (617/625) lo2350 hi2350=true := by decide +kernel
def bracket2350 : MeanBracket := meanBracketOfMoments (617/625) lo2350 hi2350 accepted2350
def lo2351b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨22,by decide⟩
def lo2351b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨23,by decide⟩
def lo2351 : CheckedMoment :=
  CheckedMoment.ofBessel lo2351b1 lo2351b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2351b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨27,by decide⟩
def hi2351b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨28,by decide⟩
def hi2351 : CheckedMoment :=
  CheckedMoment.ofBessel hi2351b1 hi2351b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2351 : meanBracketCheck (9873/10000) lo2351 hi2351=true := by decide +kernel
def bracket2351 : MeanBracket := meanBracketOfMoments (9873/10000) lo2351 hi2351 accepted2351
#print axioms bracket2336
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0146
