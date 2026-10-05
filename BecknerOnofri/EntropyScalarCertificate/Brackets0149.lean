module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0372
public import BecknerOnofri.EntropyScalarCertificate.Bessel0373
public import BecknerOnofri.EntropyScalarCertificate.Bessel0374

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0149
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2384b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨32,by decide⟩
def lo2384b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨33,by decide⟩
def lo2384 : CheckedMoment :=
  CheckedMoment.ofBessel lo2384b1 lo2384b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2384b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨37,by decide⟩
def hi2384b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨38,by decide⟩
def hi2384 : CheckedMoment :=
  CheckedMoment.ofBessel hi2384b1 hi2384b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2384 : meanBracketCheck (24753/25000) lo2384 hi2384=true := by decide +kernel
def bracket2384 : MeanBracket := meanBracketOfMoments (24753/25000) lo2384 hi2384 accepted2384
def lo2385b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨42,by decide⟩
def lo2385b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨43,by decide⟩
def lo2385 : CheckedMoment :=
  CheckedMoment.ofBessel lo2385b1 lo2385b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2385b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨47,by decide⟩
def hi2385b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨48,by decide⟩
def hi2385 : CheckedMoment :=
  CheckedMoment.ofBessel hi2385b1 hi2385b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2385 : meanBracketCheck (49507/50000) lo2385 hi2385=true := by decide +kernel
def bracket2385 : MeanBracket := meanBracketOfMoments (49507/50000) lo2385 hi2385 accepted2385
def lo2386b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨52,by decide⟩
def lo2386b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨53,by decide⟩
def lo2386 : CheckedMoment :=
  CheckedMoment.ofBessel lo2386b1 lo2386b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2386b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨57,by decide⟩
def hi2386b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨58,by decide⟩
def hi2386 : CheckedMoment :=
  CheckedMoment.ofBessel hi2386b1 hi2386b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2386 : meanBracketCheck (12377/12500) lo2386 hi2386=true := by decide +kernel
def bracket2386 : MeanBracket := meanBracketOfMoments (12377/12500) lo2386 hi2386 accepted2386
def lo2387b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨62,by decide⟩
def lo2387b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨63,by decide⟩
def lo2387 : CheckedMoment :=
  CheckedMoment.ofBessel lo2387b1 lo2387b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2387b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨3,by decide⟩
def hi2387b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨4,by decide⟩
def hi2387 : CheckedMoment :=
  CheckedMoment.ofBessel hi2387b1 hi2387b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2387 : meanBracketCheck (49509/50000) lo2387 hi2387=true := by decide +kernel
def bracket2387 : MeanBracket := meanBracketOfMoments (49509/50000) lo2387 hi2387 accepted2387
def lo2388b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨8,by decide⟩
def lo2388b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨9,by decide⟩
def lo2388 : CheckedMoment :=
  CheckedMoment.ofBessel lo2388b1 lo2388b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2388b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨13,by decide⟩
def hi2388b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨14,by decide⟩
def hi2388 : CheckedMoment :=
  CheckedMoment.ofBessel hi2388b1 hi2388b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2388 : meanBracketCheck (4951/5000) lo2388 hi2388=true := by decide +kernel
def bracket2388 : MeanBracket := meanBracketOfMoments (4951/5000) lo2388 hi2388 accepted2388
def lo2389b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨18,by decide⟩
def lo2389b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨19,by decide⟩
def lo2389 : CheckedMoment :=
  CheckedMoment.ofBessel lo2389b1 lo2389b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2389b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨23,by decide⟩
def hi2389b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨24,by decide⟩
def hi2389 : CheckedMoment :=
  CheckedMoment.ofBessel hi2389b1 hi2389b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2389 : meanBracketCheck (49511/50000) lo2389 hi2389=true := by decide +kernel
def bracket2389 : MeanBracket := meanBracketOfMoments (49511/50000) lo2389 hi2389 accepted2389
def lo2390b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨28,by decide⟩
def lo2390b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨29,by decide⟩
def lo2390 : CheckedMoment :=
  CheckedMoment.ofBessel lo2390b1 lo2390b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2390b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨33,by decide⟩
def hi2390b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨34,by decide⟩
def hi2390 : CheckedMoment :=
  CheckedMoment.ofBessel hi2390b1 hi2390b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2390 : meanBracketCheck (6189/6250) lo2390 hi2390=true := by decide +kernel
def bracket2390 : MeanBracket := meanBracketOfMoments (6189/6250) lo2390 hi2390 accepted2390
def lo2391b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨38,by decide⟩
def lo2391b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨39,by decide⟩
def lo2391 : CheckedMoment :=
  CheckedMoment.ofBessel lo2391b1 lo2391b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2391b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨43,by decide⟩
def hi2391b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨44,by decide⟩
def hi2391 : CheckedMoment :=
  CheckedMoment.ofBessel hi2391b1 hi2391b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2391 : meanBracketCheck (49513/50000) lo2391 hi2391=true := by decide +kernel
def bracket2391 : MeanBracket := meanBracketOfMoments (49513/50000) lo2391 hi2391 accepted2391
def lo2392b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨48,by decide⟩
def lo2392b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨49,by decide⟩
def lo2392 : CheckedMoment :=
  CheckedMoment.ofBessel lo2392b1 lo2392b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2392b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨53,by decide⟩
def hi2392b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨54,by decide⟩
def hi2392 : CheckedMoment :=
  CheckedMoment.ofBessel hi2392b1 hi2392b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2392 : meanBracketCheck (24757/25000) lo2392 hi2392=true := by decide +kernel
def bracket2392 : MeanBracket := meanBracketOfMoments (24757/25000) lo2392 hi2392 accepted2392
def lo2393b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨58,by decide⟩
def lo2393b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨59,by decide⟩
def lo2393 : CheckedMoment :=
  CheckedMoment.ofBessel lo2393b1 lo2393b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2393b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨63,by decide⟩
def hi2393b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨0,by decide⟩
def hi2393 : CheckedMoment :=
  CheckedMoment.ofBessel hi2393b1 hi2393b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2393 : meanBracketCheck (9903/10000) lo2393 hi2393=true := by decide +kernel
def bracket2393 : MeanBracket := meanBracketOfMoments (9903/10000) lo2393 hi2393 accepted2393
def lo2394b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨4,by decide⟩
def lo2394b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨5,by decide⟩
def lo2394 : CheckedMoment :=
  CheckedMoment.ofBessel lo2394b1 lo2394b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2394b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨9,by decide⟩
def hi2394b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨10,by decide⟩
def hi2394 : CheckedMoment :=
  CheckedMoment.ofBessel hi2394b1 hi2394b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2394 : meanBracketCheck (12379/12500) lo2394 hi2394=true := by decide +kernel
def bracket2394 : MeanBracket := meanBracketOfMoments (12379/12500) lo2394 hi2394 accepted2394
def lo2395b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨14,by decide⟩
def lo2395b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨15,by decide⟩
def lo2395 : CheckedMoment :=
  CheckedMoment.ofBessel lo2395b1 lo2395b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2395b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨19,by decide⟩
def hi2395b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨20,by decide⟩
def hi2395 : CheckedMoment :=
  CheckedMoment.ofBessel hi2395b1 hi2395b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2395 : meanBracketCheck (49517/50000) lo2395 hi2395=true := by decide +kernel
def bracket2395 : MeanBracket := meanBracketOfMoments (49517/50000) lo2395 hi2395 accepted2395
def lo2396b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨24,by decide⟩
def lo2396b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨25,by decide⟩
def lo2396 : CheckedMoment :=
  CheckedMoment.ofBessel lo2396b1 lo2396b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2396b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨29,by decide⟩
def hi2396b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨30,by decide⟩
def hi2396 : CheckedMoment :=
  CheckedMoment.ofBessel hi2396b1 hi2396b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2396 : meanBracketCheck (24759/25000) lo2396 hi2396=true := by decide +kernel
def bracket2396 : MeanBracket := meanBracketOfMoments (24759/25000) lo2396 hi2396 accepted2396
def lo2397b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨34,by decide⟩
def lo2397b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨35,by decide⟩
def lo2397 : CheckedMoment :=
  CheckedMoment.ofBessel lo2397b1 lo2397b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2397b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨39,by decide⟩
def hi2397b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨40,by decide⟩
def hi2397 : CheckedMoment :=
  CheckedMoment.ofBessel hi2397b1 hi2397b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2397 : meanBracketCheck (49519/50000) lo2397 hi2397=true := by decide +kernel
def bracket2397 : MeanBracket := meanBracketOfMoments (49519/50000) lo2397 hi2397 accepted2397
def lo2398b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨44,by decide⟩
def lo2398b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨45,by decide⟩
def lo2398 : CheckedMoment :=
  CheckedMoment.ofBessel lo2398b1 lo2398b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2398b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨49,by decide⟩
def hi2398b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨50,by decide⟩
def hi2398 : CheckedMoment :=
  CheckedMoment.ofBessel hi2398b1 hi2398b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2398 : meanBracketCheck (619/625) lo2398 hi2398=true := by decide +kernel
def bracket2398 : MeanBracket := meanBracketOfMoments (619/625) lo2398 hi2398 accepted2398
def lo2399b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨54,by decide⟩
def lo2399b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨55,by decide⟩
def lo2399 : CheckedMoment :=
  CheckedMoment.ofBessel lo2399b1 lo2399b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2399b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨59,by decide⟩
def hi2399b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨60,by decide⟩
def hi2399 : CheckedMoment :=
  CheckedMoment.ofBessel hi2399b1 hi2399b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2399 : meanBracketCheck (49521/50000) lo2399 hi2399=true := by decide +kernel
def bracket2399 : MeanBracket := meanBracketOfMoments (49521/50000) lo2399 hi2399 accepted2399
#print axioms bracket2384
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0149
