import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0067
import BecknerOnofri.EntropyScalarCertificate.Bessel0068
import BecknerOnofri.EntropyScalarCertificate.Bessel0069
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0027
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0432b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨32,by decide⟩
def lo0432b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨33,by decide⟩
def lo0432 : CheckedMoment :=
  CheckedMoment.ofBessel lo0432b1 lo0432b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0432b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨37,by decide⟩
def hi0432b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨38,by decide⟩
def hi0432 : CheckedMoment :=
  CheckedMoment.ofBessel hi0432b1 hi0432b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0432 : meanBracketCheck (1429/10000) lo0432 hi0432=true := by decide +kernel
def bracket0432 : MeanBracket := meanBracketOfMoments (1429/10000) lo0432 hi0432 accepted0432
def lo0433b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨42,by decide⟩
def lo0433b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨43,by decide⟩
def lo0433 : CheckedMoment :=
  CheckedMoment.ofBessel lo0433b1 lo0433b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0433b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨47,by decide⟩
def hi0433b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨48,by decide⟩
def hi0433 : CheckedMoment :=
  CheckedMoment.ofBessel hi0433b1 hi0433b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0433 : meanBracketCheck (1431/10000) lo0433 hi0433=true := by decide +kernel
def bracket0433 : MeanBracket := meanBracketOfMoments (1431/10000) lo0433 hi0433 accepted0433
def lo0434b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨52,by decide⟩
def lo0434b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨53,by decide⟩
def lo0434 : CheckedMoment :=
  CheckedMoment.ofBessel lo0434b1 lo0434b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0434b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨57,by decide⟩
def hi0434b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨58,by decide⟩
def hi0434 : CheckedMoment :=
  CheckedMoment.ofBessel hi0434b1 hi0434b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0434 : meanBracketCheck (1433/10000) lo0434 hi0434=true := by decide +kernel
def bracket0434 : MeanBracket := meanBracketOfMoments (1433/10000) lo0434 hi0434 accepted0434
def lo0435b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨62,by decide⟩
def lo0435b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨63,by decide⟩
def lo0435 : CheckedMoment :=
  CheckedMoment.ofBessel lo0435b1 lo0435b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0435b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨3,by decide⟩
def hi0435b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨4,by decide⟩
def hi0435 : CheckedMoment :=
  CheckedMoment.ofBessel hi0435b1 hi0435b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0435 : meanBracketCheck (287/2000) lo0435 hi0435=true := by decide +kernel
def bracket0435 : MeanBracket := meanBracketOfMoments (287/2000) lo0435 hi0435 accepted0435
def lo0436b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨8,by decide⟩
def lo0436b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨9,by decide⟩
def lo0436 : CheckedMoment :=
  CheckedMoment.ofBessel lo0436b1 lo0436b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0436b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨13,by decide⟩
def hi0436b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨14,by decide⟩
def hi0436 : CheckedMoment :=
  CheckedMoment.ofBessel hi0436b1 hi0436b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0436 : meanBracketCheck (1437/10000) lo0436 hi0436=true := by decide +kernel
def bracket0436 : MeanBracket := meanBracketOfMoments (1437/10000) lo0436 hi0436 accepted0436
def lo0437b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨18,by decide⟩
def lo0437b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨19,by decide⟩
def lo0437 : CheckedMoment :=
  CheckedMoment.ofBessel lo0437b1 lo0437b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0437b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨23,by decide⟩
def hi0437b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨24,by decide⟩
def hi0437 : CheckedMoment :=
  CheckedMoment.ofBessel hi0437b1 hi0437b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0437 : meanBracketCheck (1439/10000) lo0437 hi0437=true := by decide +kernel
def bracket0437 : MeanBracket := meanBracketOfMoments (1439/10000) lo0437 hi0437 accepted0437
def lo0438b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨28,by decide⟩
def lo0438b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨29,by decide⟩
def lo0438 : CheckedMoment :=
  CheckedMoment.ofBessel lo0438b1 lo0438b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0438b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨33,by decide⟩
def hi0438b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨34,by decide⟩
def hi0438 : CheckedMoment :=
  CheckedMoment.ofBessel hi0438b1 hi0438b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0438 : meanBracketCheck (1441/10000) lo0438 hi0438=true := by decide +kernel
def bracket0438 : MeanBracket := meanBracketOfMoments (1441/10000) lo0438 hi0438 accepted0438
def lo0439b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨38,by decide⟩
def lo0439b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨39,by decide⟩
def lo0439 : CheckedMoment :=
  CheckedMoment.ofBessel lo0439b1 lo0439b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0439b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨43,by decide⟩
def hi0439b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨44,by decide⟩
def hi0439 : CheckedMoment :=
  CheckedMoment.ofBessel hi0439b1 hi0439b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0439 : meanBracketCheck (1443/10000) lo0439 hi0439=true := by decide +kernel
def bracket0439 : MeanBracket := meanBracketOfMoments (1443/10000) lo0439 hi0439 accepted0439
def lo0440b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨48,by decide⟩
def lo0440b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨49,by decide⟩
def lo0440 : CheckedMoment :=
  CheckedMoment.ofBessel lo0440b1 lo0440b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0440b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨53,by decide⟩
def hi0440b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨54,by decide⟩
def hi0440 : CheckedMoment :=
  CheckedMoment.ofBessel hi0440b1 hi0440b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0440 : meanBracketCheck (289/2000) lo0440 hi0440=true := by decide +kernel
def bracket0440 : MeanBracket := meanBracketOfMoments (289/2000) lo0440 hi0440 accepted0440
def lo0441b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨58,by decide⟩
def lo0441b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨59,by decide⟩
def lo0441 : CheckedMoment :=
  CheckedMoment.ofBessel lo0441b1 lo0441b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0441b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨63,by decide⟩
def hi0441b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨0,by decide⟩
def hi0441 : CheckedMoment :=
  CheckedMoment.ofBessel hi0441b1 hi0441b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0441 : meanBracketCheck (1447/10000) lo0441 hi0441=true := by decide +kernel
def bracket0441 : MeanBracket := meanBracketOfMoments (1447/10000) lo0441 hi0441 accepted0441
def lo0442b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨4,by decide⟩
def lo0442b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨5,by decide⟩
def lo0442 : CheckedMoment :=
  CheckedMoment.ofBessel lo0442b1 lo0442b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0442b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨9,by decide⟩
def hi0442b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨10,by decide⟩
def hi0442 : CheckedMoment :=
  CheckedMoment.ofBessel hi0442b1 hi0442b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0442 : meanBracketCheck (1449/10000) lo0442 hi0442=true := by decide +kernel
def bracket0442 : MeanBracket := meanBracketOfMoments (1449/10000) lo0442 hi0442 accepted0442
def lo0443b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨14,by decide⟩
def lo0443b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨15,by decide⟩
def lo0443 : CheckedMoment :=
  CheckedMoment.ofBessel lo0443b1 lo0443b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0443b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨19,by decide⟩
def hi0443b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨20,by decide⟩
def hi0443 : CheckedMoment :=
  CheckedMoment.ofBessel hi0443b1 hi0443b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0443 : meanBracketCheck (1451/10000) lo0443 hi0443=true := by decide +kernel
def bracket0443 : MeanBracket := meanBracketOfMoments (1451/10000) lo0443 hi0443 accepted0443
def lo0444b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨24,by decide⟩
def lo0444b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨25,by decide⟩
def lo0444 : CheckedMoment :=
  CheckedMoment.ofBessel lo0444b1 lo0444b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0444b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨29,by decide⟩
def hi0444b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨30,by decide⟩
def hi0444 : CheckedMoment :=
  CheckedMoment.ofBessel hi0444b1 hi0444b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0444 : meanBracketCheck (1453/10000) lo0444 hi0444=true := by decide +kernel
def bracket0444 : MeanBracket := meanBracketOfMoments (1453/10000) lo0444 hi0444 accepted0444
def lo0445b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨34,by decide⟩
def lo0445b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨35,by decide⟩
def lo0445 : CheckedMoment :=
  CheckedMoment.ofBessel lo0445b1 lo0445b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0445b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨39,by decide⟩
def hi0445b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨40,by decide⟩
def hi0445 : CheckedMoment :=
  CheckedMoment.ofBessel hi0445b1 hi0445b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0445 : meanBracketCheck (291/2000) lo0445 hi0445=true := by decide +kernel
def bracket0445 : MeanBracket := meanBracketOfMoments (291/2000) lo0445 hi0445 accepted0445
def lo0446b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨44,by decide⟩
def lo0446b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨45,by decide⟩
def lo0446 : CheckedMoment :=
  CheckedMoment.ofBessel lo0446b1 lo0446b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0446b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨49,by decide⟩
def hi0446b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨50,by decide⟩
def hi0446 : CheckedMoment :=
  CheckedMoment.ofBessel hi0446b1 hi0446b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0446 : meanBracketCheck (1457/10000) lo0446 hi0446=true := by decide +kernel
def bracket0446 : MeanBracket := meanBracketOfMoments (1457/10000) lo0446 hi0446 accepted0446
def lo0447b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨54,by decide⟩
def lo0447b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨55,by decide⟩
def lo0447 : CheckedMoment :=
  CheckedMoment.ofBessel lo0447b1 lo0447b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0447b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨59,by decide⟩
def hi0447b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨60,by decide⟩
def hi0447 : CheckedMoment :=
  CheckedMoment.ofBessel hi0447b1 hi0447b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0447 : meanBracketCheck (1459/10000) lo0447 hi0447=true := by decide +kernel
def bracket0447 : MeanBracket := meanBracketOfMoments (1459/10000) lo0447 hi0447 accepted0447
#print axioms bracket0432
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0027
