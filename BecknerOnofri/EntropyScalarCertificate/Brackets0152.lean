import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0380
import BecknerOnofri.EntropyScalarCertificate.Bessel0381
import BecknerOnofri.EntropyScalarCertificate.Bessel0382
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0152
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2432b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨0,by decide⟩
def lo2432b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨1,by decide⟩
def lo2432 : CheckedMoment :=
  CheckedMoment.ofBessel lo2432b1 lo2432b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2432b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨5,by decide⟩
def hi2432b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨6,by decide⟩
def hi2432 : CheckedMoment :=
  CheckedMoment.ofBessel hi2432b1 hi2432b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2432 : meanBracketCheck (24777/25000) lo2432 hi2432=true := by decide +kernel
def bracket2432 : MeanBracket := meanBracketOfMoments (24777/25000) lo2432 hi2432 accepted2432
def lo2433b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨10,by decide⟩
def lo2433b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨11,by decide⟩
def lo2433 : CheckedMoment :=
  CheckedMoment.ofBessel lo2433b1 lo2433b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2433b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨15,by decide⟩
def hi2433b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨16,by decide⟩
def hi2433 : CheckedMoment :=
  CheckedMoment.ofBessel hi2433b1 hi2433b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2433 : meanBracketCheck (9911/10000) lo2433 hi2433=true := by decide +kernel
def bracket2433 : MeanBracket := meanBracketOfMoments (9911/10000) lo2433 hi2433 accepted2433
def lo2434b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨20,by decide⟩
def lo2434b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨21,by decide⟩
def lo2434 : CheckedMoment :=
  CheckedMoment.ofBessel lo2434b1 lo2434b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2434b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨25,by decide⟩
def hi2434b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨26,by decide⟩
def hi2434 : CheckedMoment :=
  CheckedMoment.ofBessel hi2434b1 hi2434b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2434 : meanBracketCheck (12389/12500) lo2434 hi2434=true := by decide +kernel
def bracket2434 : MeanBracket := meanBracketOfMoments (12389/12500) lo2434 hi2434 accepted2434
def lo2435b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨30,by decide⟩
def lo2435b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨31,by decide⟩
def lo2435 : CheckedMoment :=
  CheckedMoment.ofBessel lo2435b1 lo2435b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2435b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨35,by decide⟩
def hi2435b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨36,by decide⟩
def hi2435 : CheckedMoment :=
  CheckedMoment.ofBessel hi2435b1 hi2435b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2435 : meanBracketCheck (49557/50000) lo2435 hi2435=true := by decide +kernel
def bracket2435 : MeanBracket := meanBracketOfMoments (49557/50000) lo2435 hi2435 accepted2435
def lo2436b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨40,by decide⟩
def lo2436b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨41,by decide⟩
def lo2436 : CheckedMoment :=
  CheckedMoment.ofBessel lo2436b1 lo2436b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2436b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨45,by decide⟩
def hi2436b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨46,by decide⟩
def hi2436 : CheckedMoment :=
  CheckedMoment.ofBessel hi2436b1 hi2436b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2436 : meanBracketCheck (24779/25000) lo2436 hi2436=true := by decide +kernel
def bracket2436 : MeanBracket := meanBracketOfMoments (24779/25000) lo2436 hi2436 accepted2436
def lo2437b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨50,by decide⟩
def lo2437b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨51,by decide⟩
def lo2437 : CheckedMoment :=
  CheckedMoment.ofBessel lo2437b1 lo2437b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2437b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨55,by decide⟩
def hi2437b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨56,by decide⟩
def hi2437 : CheckedMoment :=
  CheckedMoment.ofBessel hi2437b1 hi2437b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2437 : meanBracketCheck (49559/50000) lo2437 hi2437=true := by decide +kernel
def bracket2437 : MeanBracket := meanBracketOfMoments (49559/50000) lo2437 hi2437 accepted2437
def lo2438b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨60,by decide⟩
def lo2438b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨61,by decide⟩
def lo2438 : CheckedMoment :=
  CheckedMoment.ofBessel lo2438b1 lo2438b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2438b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨1,by decide⟩
def hi2438b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨2,by decide⟩
def hi2438 : CheckedMoment :=
  CheckedMoment.ofBessel hi2438b1 hi2438b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2438 : meanBracketCheck (1239/1250) lo2438 hi2438=true := by decide +kernel
def bracket2438 : MeanBracket := meanBracketOfMoments (1239/1250) lo2438 hi2438 accepted2438
def lo2439b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨6,by decide⟩
def lo2439b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨7,by decide⟩
def lo2439 : CheckedMoment :=
  CheckedMoment.ofBessel lo2439b1 lo2439b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2439b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨11,by decide⟩
def hi2439b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨12,by decide⟩
def hi2439 : CheckedMoment :=
  CheckedMoment.ofBessel hi2439b1 hi2439b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2439 : meanBracketCheck (49561/50000) lo2439 hi2439=true := by decide +kernel
def bracket2439 : MeanBracket := meanBracketOfMoments (49561/50000) lo2439 hi2439 accepted2439
def lo2440b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨16,by decide⟩
def lo2440b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨17,by decide⟩
def lo2440 : CheckedMoment :=
  CheckedMoment.ofBessel lo2440b1 lo2440b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2440b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨21,by decide⟩
def hi2440b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨22,by decide⟩
def hi2440 : CheckedMoment :=
  CheckedMoment.ofBessel hi2440b1 hi2440b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2440 : meanBracketCheck (24781/25000) lo2440 hi2440=true := by decide +kernel
def bracket2440 : MeanBracket := meanBracketOfMoments (24781/25000) lo2440 hi2440 accepted2440
def lo2441b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨26,by decide⟩
def lo2441b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨27,by decide⟩
def lo2441 : CheckedMoment :=
  CheckedMoment.ofBessel lo2441b1 lo2441b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2441b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨31,by decide⟩
def hi2441b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨32,by decide⟩
def hi2441 : CheckedMoment :=
  CheckedMoment.ofBessel hi2441b1 hi2441b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2441 : meanBracketCheck (49563/50000) lo2441 hi2441=true := by decide +kernel
def bracket2441 : MeanBracket := meanBracketOfMoments (49563/50000) lo2441 hi2441 accepted2441
def lo2442b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨36,by decide⟩
def lo2442b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨37,by decide⟩
def lo2442 : CheckedMoment :=
  CheckedMoment.ofBessel lo2442b1 lo2442b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2442b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨41,by decide⟩
def hi2442b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨42,by decide⟩
def hi2442 : CheckedMoment :=
  CheckedMoment.ofBessel hi2442b1 hi2442b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2442 : meanBracketCheck (12391/12500) lo2442 hi2442=true := by decide +kernel
def bracket2442 : MeanBracket := meanBracketOfMoments (12391/12500) lo2442 hi2442 accepted2442
def lo2443b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨46,by decide⟩
def lo2443b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨47,by decide⟩
def lo2443 : CheckedMoment :=
  CheckedMoment.ofBessel lo2443b1 lo2443b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2443b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨51,by decide⟩
def hi2443b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨52,by decide⟩
def hi2443 : CheckedMoment :=
  CheckedMoment.ofBessel hi2443b1 hi2443b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2443 : meanBracketCheck (9913/10000) lo2443 hi2443=true := by decide +kernel
def bracket2443 : MeanBracket := meanBracketOfMoments (9913/10000) lo2443 hi2443 accepted2443
def lo2444b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨56,by decide⟩
def lo2444b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨57,by decide⟩
def lo2444 : CheckedMoment :=
  CheckedMoment.ofBessel lo2444b1 lo2444b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2444b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨61,by decide⟩
def hi2444b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨62,by decide⟩
def hi2444 : CheckedMoment :=
  CheckedMoment.ofBessel hi2444b1 hi2444b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2444 : meanBracketCheck (24783/25000) lo2444 hi2444=true := by decide +kernel
def bracket2444 : MeanBracket := meanBracketOfMoments (24783/25000) lo2444 hi2444 accepted2444
def lo2445b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨2,by decide⟩
def lo2445b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨3,by decide⟩
def lo2445 : CheckedMoment :=
  CheckedMoment.ofBessel lo2445b1 lo2445b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2445b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨7,by decide⟩
def hi2445b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨8,by decide⟩
def hi2445 : CheckedMoment :=
  CheckedMoment.ofBessel hi2445b1 hi2445b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2445 : meanBracketCheck (49567/50000) lo2445 hi2445=true := by decide +kernel
def bracket2445 : MeanBracket := meanBracketOfMoments (49567/50000) lo2445 hi2445 accepted2445
def lo2446b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨12,by decide⟩
def lo2446b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨13,by decide⟩
def lo2446 : CheckedMoment :=
  CheckedMoment.ofBessel lo2446b1 lo2446b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2446b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨17,by decide⟩
def hi2446b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨18,by decide⟩
def hi2446 : CheckedMoment :=
  CheckedMoment.ofBessel hi2446b1 hi2446b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2446 : meanBracketCheck (3098/3125) lo2446 hi2446=true := by decide +kernel
def bracket2446 : MeanBracket := meanBracketOfMoments (3098/3125) lo2446 hi2446 accepted2446
def lo2447b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨22,by decide⟩
def lo2447b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨23,by decide⟩
def lo2447 : CheckedMoment :=
  CheckedMoment.ofBessel lo2447b1 lo2447b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2447b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨27,by decide⟩
def hi2447b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨28,by decide⟩
def hi2447 : CheckedMoment :=
  CheckedMoment.ofBessel hi2447b1 hi2447b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2447 : meanBracketCheck (49569/50000) lo2447 hi2447=true := by decide +kernel
def bracket2447 : MeanBracket := meanBracketOfMoments (49569/50000) lo2447 hi2447 accepted2447
#print axioms bracket2432
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0152
