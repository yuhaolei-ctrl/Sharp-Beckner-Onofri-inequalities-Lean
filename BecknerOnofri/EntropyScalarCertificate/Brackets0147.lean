module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0367
public import BecknerOnofri.EntropyScalarCertificate.Bessel0368
public import BecknerOnofri.EntropyScalarCertificate.Bessel0369

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0147
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2352b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨32,by decide⟩
def lo2352b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨33,by decide⟩
def lo2352 : CheckedMoment :=
  CheckedMoment.ofBessel lo2352b1 lo2352b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2352b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨37,by decide⟩
def hi2352b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨38,by decide⟩
def hi2352 : CheckedMoment :=
  CheckedMoment.ofBessel hi2352b1 hi2352b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2352 : meanBracketCheck (4937/5000) lo2352 hi2352=true := by decide +kernel
def bracket2352 : MeanBracket := meanBracketOfMoments (4937/5000) lo2352 hi2352 accepted2352
def lo2353b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨42,by decide⟩
def lo2353b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨43,by decide⟩
def lo2353 : CheckedMoment :=
  CheckedMoment.ofBessel lo2353b1 lo2353b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2353b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨47,by decide⟩
def hi2353b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨48,by decide⟩
def hi2353 : CheckedMoment :=
  CheckedMoment.ofBessel hi2353b1 hi2353b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2353 : meanBracketCheck (79/80) lo2353 hi2353=true := by decide +kernel
def bracket2353 : MeanBracket := meanBracketOfMoments (79/80) lo2353 hi2353 accepted2353
def lo2354b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨52,by decide⟩
def lo2354b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨53,by decide⟩
def lo2354 : CheckedMoment :=
  CheckedMoment.ofBessel lo2354b1 lo2354b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2354b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨57,by decide⟩
def hi2354b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨58,by decide⟩
def hi2354 : CheckedMoment :=
  CheckedMoment.ofBessel hi2354b1 hi2354b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2354 : meanBracketCheck (2469/2500) lo2354 hi2354=true := by decide +kernel
def bracket2354 : MeanBracket := meanBracketOfMoments (2469/2500) lo2354 hi2354 accepted2354
def lo2355b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨62,by decide⟩
def lo2355b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨63,by decide⟩
def lo2355 : CheckedMoment :=
  CheckedMoment.ofBessel lo2355b1 lo2355b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2355b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨3,by decide⟩
def hi2355b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨4,by decide⟩
def hi2355 : CheckedMoment :=
  CheckedMoment.ofBessel hi2355b1 hi2355b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2355 : meanBracketCheck (9877/10000) lo2355 hi2355=true := by decide +kernel
def bracket2355 : MeanBracket := meanBracketOfMoments (9877/10000) lo2355 hi2355 accepted2355
def lo2356b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨8,by decide⟩
def lo2356b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨9,by decide⟩
def lo2356 : CheckedMoment :=
  CheckedMoment.ofBessel lo2356b1 lo2356b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2356b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨13,by decide⟩
def hi2356b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨14,by decide⟩
def hi2356 : CheckedMoment :=
  CheckedMoment.ofBessel hi2356b1 hi2356b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2356 : meanBracketCheck (4939/5000) lo2356 hi2356=true := by decide +kernel
def bracket2356 : MeanBracket := meanBracketOfMoments (4939/5000) lo2356 hi2356 accepted2356
def lo2357b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨18,by decide⟩
def lo2357b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨19,by decide⟩
def lo2357 : CheckedMoment :=
  CheckedMoment.ofBessel lo2357b1 lo2357b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2357b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨23,by decide⟩
def hi2357b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨24,by decide⟩
def hi2357 : CheckedMoment :=
  CheckedMoment.ofBessel hi2357b1 hi2357b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2357 : meanBracketCheck (9879/10000) lo2357 hi2357=true := by decide +kernel
def bracket2357 : MeanBracket := meanBracketOfMoments (9879/10000) lo2357 hi2357 accepted2357
def lo2358b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨28,by decide⟩
def lo2358b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨29,by decide⟩
def lo2358 : CheckedMoment :=
  CheckedMoment.ofBessel lo2358b1 lo2358b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2358b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨33,by decide⟩
def hi2358b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨34,by decide⟩
def hi2358 : CheckedMoment :=
  CheckedMoment.ofBessel hi2358b1 hi2358b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2358 : meanBracketCheck (247/250) lo2358 hi2358=true := by decide +kernel
def bracket2358 : MeanBracket := meanBracketOfMoments (247/250) lo2358 hi2358 accepted2358
def lo2359b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨38,by decide⟩
def lo2359b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨39,by decide⟩
def lo2359 : CheckedMoment :=
  CheckedMoment.ofBessel lo2359b1 lo2359b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2359b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨43,by decide⟩
def hi2359b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨44,by decide⟩
def hi2359 : CheckedMoment :=
  CheckedMoment.ofBessel hi2359b1 hi2359b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2359 : meanBracketCheck (9881/10000) lo2359 hi2359=true := by decide +kernel
def bracket2359 : MeanBracket := meanBracketOfMoments (9881/10000) lo2359 hi2359 accepted2359
def lo2360b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨48,by decide⟩
def lo2360b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨49,by decide⟩
def lo2360 : CheckedMoment :=
  CheckedMoment.ofBessel lo2360b1 lo2360b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2360b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨53,by decide⟩
def hi2360b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨54,by decide⟩
def hi2360 : CheckedMoment :=
  CheckedMoment.ofBessel hi2360b1 hi2360b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2360 : meanBracketCheck (4941/5000) lo2360 hi2360=true := by decide +kernel
def bracket2360 : MeanBracket := meanBracketOfMoments (4941/5000) lo2360 hi2360 accepted2360
def lo2361b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨58,by decide⟩
def lo2361b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨59,by decide⟩
def lo2361 : CheckedMoment :=
  CheckedMoment.ofBessel lo2361b1 lo2361b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2361b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨63,by decide⟩
def hi2361b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨0,by decide⟩
def hi2361 : CheckedMoment :=
  CheckedMoment.ofBessel hi2361b1 hi2361b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2361 : meanBracketCheck (9883/10000) lo2361 hi2361=true := by decide +kernel
def bracket2361 : MeanBracket := meanBracketOfMoments (9883/10000) lo2361 hi2361 accepted2361
def lo2362b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨4,by decide⟩
def lo2362b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨5,by decide⟩
def lo2362 : CheckedMoment :=
  CheckedMoment.ofBessel lo2362b1 lo2362b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2362b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨9,by decide⟩
def hi2362b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨10,by decide⟩
def hi2362 : CheckedMoment :=
  CheckedMoment.ofBessel hi2362b1 hi2362b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2362 : meanBracketCheck (2471/2500) lo2362 hi2362=true := by decide +kernel
def bracket2362 : MeanBracket := meanBracketOfMoments (2471/2500) lo2362 hi2362 accepted2362
def lo2363b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨14,by decide⟩
def lo2363b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨15,by decide⟩
def lo2363 : CheckedMoment :=
  CheckedMoment.ofBessel lo2363b1 lo2363b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2363b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨19,by decide⟩
def hi2363b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨20,by decide⟩
def hi2363 : CheckedMoment :=
  CheckedMoment.ofBessel hi2363b1 hi2363b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2363 : meanBracketCheck (1977/2000) lo2363 hi2363=true := by decide +kernel
def bracket2363 : MeanBracket := meanBracketOfMoments (1977/2000) lo2363 hi2363 accepted2363
def lo2364b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨24,by decide⟩
def lo2364b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨25,by decide⟩
def lo2364 : CheckedMoment :=
  CheckedMoment.ofBessel lo2364b1 lo2364b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2364b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨29,by decide⟩
def hi2364b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨30,by decide⟩
def hi2364 : CheckedMoment :=
  CheckedMoment.ofBessel hi2364b1 hi2364b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2364 : meanBracketCheck (4943/5000) lo2364 hi2364=true := by decide +kernel
def bracket2364 : MeanBracket := meanBracketOfMoments (4943/5000) lo2364 hi2364 accepted2364
def lo2365b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨34,by decide⟩
def lo2365b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨35,by decide⟩
def lo2365 : CheckedMoment :=
  CheckedMoment.ofBessel lo2365b1 lo2365b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2365b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨39,by decide⟩
def hi2365b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨40,by decide⟩
def hi2365 : CheckedMoment :=
  CheckedMoment.ofBessel hi2365b1 hi2365b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2365 : meanBracketCheck (9887/10000) lo2365 hi2365=true := by decide +kernel
def bracket2365 : MeanBracket := meanBracketOfMoments (9887/10000) lo2365 hi2365 accepted2365
def lo2366b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨44,by decide⟩
def lo2366b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨45,by decide⟩
def lo2366 : CheckedMoment :=
  CheckedMoment.ofBessel lo2366b1 lo2366b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2366b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨49,by decide⟩
def hi2366b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨50,by decide⟩
def hi2366 : CheckedMoment :=
  CheckedMoment.ofBessel hi2366b1 hi2366b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2366 : meanBracketCheck (618/625) lo2366 hi2366=true := by decide +kernel
def bracket2366 : MeanBracket := meanBracketOfMoments (618/625) lo2366 hi2366 accepted2366
def lo2367b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨54,by decide⟩
def lo2367b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨55,by decide⟩
def lo2367 : CheckedMoment :=
  CheckedMoment.ofBessel lo2367b1 lo2367b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2367b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨59,by decide⟩
def hi2367b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨60,by decide⟩
def hi2367 : CheckedMoment :=
  CheckedMoment.ofBessel hi2367b1 hi2367b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2367 : meanBracketCheck (9889/10000) lo2367 hi2367=true := by decide +kernel
def bracket2367 : MeanBracket := meanBracketOfMoments (9889/10000) lo2367 hi2367 accepted2367
#print axioms bracket2352
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0147
