import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0370
import BecknerOnofri.EntropyScalarCertificate.Bessel0371
import BecknerOnofri.EntropyScalarCertificate.Bessel0372
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0148
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2368b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨0,by decide⟩
def lo2368b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨1,by decide⟩
def lo2368 : CheckedMoment :=
  CheckedMoment.ofBessel lo2368b1 lo2368b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2368b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨5,by decide⟩
def hi2368b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨6,by decide⟩
def hi2368 : CheckedMoment :=
  CheckedMoment.ofBessel hi2368b1 hi2368b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2368 : meanBracketCheck (989/1000) lo2368 hi2368=true := by decide +kernel
def bracket2368 : MeanBracket := meanBracketOfMoments (989/1000) lo2368 hi2368 accepted2368
def lo2369b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨10,by decide⟩
def lo2369b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨11,by decide⟩
def lo2369 : CheckedMoment :=
  CheckedMoment.ofBessel lo2369b1 lo2369b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2369b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨15,by decide⟩
def hi2369b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨16,by decide⟩
def hi2369 : CheckedMoment :=
  CheckedMoment.ofBessel hi2369b1 hi2369b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2369 : meanBracketCheck (9891/10000) lo2369 hi2369=true := by decide +kernel
def bracket2369 : MeanBracket := meanBracketOfMoments (9891/10000) lo2369 hi2369 accepted2369
def lo2370b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨20,by decide⟩
def lo2370b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨21,by decide⟩
def lo2370 : CheckedMoment :=
  CheckedMoment.ofBessel lo2370b1 lo2370b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2370b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨25,by decide⟩
def hi2370b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨26,by decide⟩
def hi2370 : CheckedMoment :=
  CheckedMoment.ofBessel hi2370b1 hi2370b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2370 : meanBracketCheck (2473/2500) lo2370 hi2370=true := by decide +kernel
def bracket2370 : MeanBracket := meanBracketOfMoments (2473/2500) lo2370 hi2370 accepted2370
def lo2371b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨30,by decide⟩
def lo2371b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨31,by decide⟩
def lo2371 : CheckedMoment :=
  CheckedMoment.ofBessel lo2371b1 lo2371b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2371b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨35,by decide⟩
def hi2371b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨36,by decide⟩
def hi2371 : CheckedMoment :=
  CheckedMoment.ofBessel hi2371b1 hi2371b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2371 : meanBracketCheck (9893/10000) lo2371 hi2371=true := by decide +kernel
def bracket2371 : MeanBracket := meanBracketOfMoments (9893/10000) lo2371 hi2371 accepted2371
def lo2372b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨40,by decide⟩
def lo2372b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨41,by decide⟩
def lo2372 : CheckedMoment :=
  CheckedMoment.ofBessel lo2372b1 lo2372b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2372b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨45,by decide⟩
def hi2372b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨46,by decide⟩
def hi2372 : CheckedMoment :=
  CheckedMoment.ofBessel hi2372b1 hi2372b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2372 : meanBracketCheck (4947/5000) lo2372 hi2372=true := by decide +kernel
def bracket2372 : MeanBracket := meanBracketOfMoments (4947/5000) lo2372 hi2372 accepted2372
def lo2373b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨50,by decide⟩
def lo2373b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨51,by decide⟩
def lo2373 : CheckedMoment :=
  CheckedMoment.ofBessel lo2373b1 lo2373b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2373b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨55,by decide⟩
def hi2373b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨56,by decide⟩
def hi2373 : CheckedMoment :=
  CheckedMoment.ofBessel hi2373b1 hi2373b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2373 : meanBracketCheck (1979/2000) lo2373 hi2373=true := by decide +kernel
def bracket2373 : MeanBracket := meanBracketOfMoments (1979/2000) lo2373 hi2373 accepted2373
def lo2374b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨60,by decide⟩
def lo2374b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨61,by decide⟩
def lo2374 : CheckedMoment :=
  CheckedMoment.ofBessel lo2374b1 lo2374b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2374b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨1,by decide⟩
def hi2374b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨2,by decide⟩
def hi2374 : CheckedMoment :=
  CheckedMoment.ofBessel hi2374b1 hi2374b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2374 : meanBracketCheck (1237/1250) lo2374 hi2374=true := by decide +kernel
def bracket2374 : MeanBracket := meanBracketOfMoments (1237/1250) lo2374 hi2374 accepted2374
def lo2375b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨6,by decide⟩
def lo2375b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨7,by decide⟩
def lo2375 : CheckedMoment :=
  CheckedMoment.ofBessel lo2375b1 lo2375b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2375b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨11,by decide⟩
def hi2375b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨12,by decide⟩
def hi2375 : CheckedMoment :=
  CheckedMoment.ofBessel hi2375b1 hi2375b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2375 : meanBracketCheck (9897/10000) lo2375 hi2375=true := by decide +kernel
def bracket2375 : MeanBracket := meanBracketOfMoments (9897/10000) lo2375 hi2375 accepted2375
def lo2376b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨16,by decide⟩
def lo2376b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨17,by decide⟩
def lo2376 : CheckedMoment :=
  CheckedMoment.ofBessel lo2376b1 lo2376b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2376b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨21,by decide⟩
def hi2376b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨22,by decide⟩
def hi2376 : CheckedMoment :=
  CheckedMoment.ofBessel hi2376b1 hi2376b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2376 : meanBracketCheck (4949/5000) lo2376 hi2376=true := by decide +kernel
def bracket2376 : MeanBracket := meanBracketOfMoments (4949/5000) lo2376 hi2376 accepted2376
def lo2377b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨26,by decide⟩
def lo2377b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨27,by decide⟩
def lo2377 : CheckedMoment :=
  CheckedMoment.ofBessel lo2377b1 lo2377b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2377b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨31,by decide⟩
def hi2377b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨32,by decide⟩
def hi2377 : CheckedMoment :=
  CheckedMoment.ofBessel hi2377b1 hi2377b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2377 : meanBracketCheck (9899/10000) lo2377 hi2377=true := by decide +kernel
def bracket2377 : MeanBracket := meanBracketOfMoments (9899/10000) lo2377 hi2377 accepted2377
def lo2378b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨36,by decide⟩
def lo2378b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨37,by decide⟩
def lo2378 : CheckedMoment :=
  CheckedMoment.ofBessel lo2378b1 lo2378b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2378b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨41,by decide⟩
def hi2378b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨42,by decide⟩
def hi2378 : CheckedMoment :=
  CheckedMoment.ofBessel hi2378b1 hi2378b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2378 : meanBracketCheck (99/100) lo2378 hi2378=true := by decide +kernel
def bracket2378 : MeanBracket := meanBracketOfMoments (99/100) lo2378 hi2378 accepted2378
def lo2379b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨46,by decide⟩
def lo2379b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨47,by decide⟩
def lo2379 : CheckedMoment :=
  CheckedMoment.ofBessel lo2379b1 lo2379b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2379b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨51,by decide⟩
def hi2379b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨52,by decide⟩
def hi2379 : CheckedMoment :=
  CheckedMoment.ofBessel hi2379b1 hi2379b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2379 : meanBracketCheck (49501/50000) lo2379 hi2379=true := by decide +kernel
def bracket2379 : MeanBracket := meanBracketOfMoments (49501/50000) lo2379 hi2379 accepted2379
def lo2380b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨56,by decide⟩
def lo2380b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨57,by decide⟩
def lo2380 : CheckedMoment :=
  CheckedMoment.ofBessel lo2380b1 lo2380b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2380b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨61,by decide⟩
def hi2380b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨62,by decide⟩
def hi2380 : CheckedMoment :=
  CheckedMoment.ofBessel hi2380b1 hi2380b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2380 : meanBracketCheck (24751/25000) lo2380 hi2380=true := by decide +kernel
def bracket2380 : MeanBracket := meanBracketOfMoments (24751/25000) lo2380 hi2380 accepted2380
def lo2381b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨2,by decide⟩
def lo2381b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨3,by decide⟩
def lo2381 : CheckedMoment :=
  CheckedMoment.ofBessel lo2381b1 lo2381b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2381b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨7,by decide⟩
def hi2381b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨8,by decide⟩
def hi2381 : CheckedMoment :=
  CheckedMoment.ofBessel hi2381b1 hi2381b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2381 : meanBracketCheck (49503/50000) lo2381 hi2381=true := by decide +kernel
def bracket2381 : MeanBracket := meanBracketOfMoments (49503/50000) lo2381 hi2381 accepted2381
def lo2382b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨12,by decide⟩
def lo2382b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨13,by decide⟩
def lo2382 : CheckedMoment :=
  CheckedMoment.ofBessel lo2382b1 lo2382b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2382b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨17,by decide⟩
def hi2382b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨18,by decide⟩
def hi2382 : CheckedMoment :=
  CheckedMoment.ofBessel hi2382b1 hi2382b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2382 : meanBracketCheck (3094/3125) lo2382 hi2382=true := by decide +kernel
def bracket2382 : MeanBracket := meanBracketOfMoments (3094/3125) lo2382 hi2382 accepted2382
def lo2383b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨22,by decide⟩
def lo2383b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨23,by decide⟩
def lo2383 : CheckedMoment :=
  CheckedMoment.ofBessel lo2383b1 lo2383b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2383b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨27,by decide⟩
def hi2383b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨28,by decide⟩
def hi2383 : CheckedMoment :=
  CheckedMoment.ofBessel hi2383b1 hi2383b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2383 : meanBracketCheck (9901/10000) lo2383 hi2383=true := by decide +kernel
def bracket2383 : MeanBracket := meanBracketOfMoments (9901/10000) lo2383 hi2383 accepted2383
#print axioms bracket2368
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0148
