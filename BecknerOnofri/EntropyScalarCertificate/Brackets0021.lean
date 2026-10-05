module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0052
public import BecknerOnofri.EntropyScalarCertificate.Bessel0053
public import BecknerOnofri.EntropyScalarCertificate.Bessel0054

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0021
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0336b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨32,by decide⟩
def lo0336b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨33,by decide⟩
def lo0336 : CheckedMoment :=
  CheckedMoment.ofBessel lo0336b1 lo0336b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0336b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨37,by decide⟩
def hi0336b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨38,by decide⟩
def hi0336 : CheckedMoment :=
  CheckedMoment.ofBessel hi0336b1 hi0336b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0336 : meanBracketCheck (1237/10000) lo0336 hi0336=true := by decide +kernel
def bracket0336 : MeanBracket := meanBracketOfMoments (1237/10000) lo0336 hi0336 accepted0336
def lo0337b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨42,by decide⟩
def lo0337b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨43,by decide⟩
def lo0337 : CheckedMoment :=
  CheckedMoment.ofBessel lo0337b1 lo0337b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0337b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨47,by decide⟩
def hi0337b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨48,by decide⟩
def hi0337 : CheckedMoment :=
  CheckedMoment.ofBessel hi0337b1 hi0337b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0337 : meanBracketCheck (1239/10000) lo0337 hi0337=true := by decide +kernel
def bracket0337 : MeanBracket := meanBracketOfMoments (1239/10000) lo0337 hi0337 accepted0337
def lo0338b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨52,by decide⟩
def lo0338b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨53,by decide⟩
def lo0338 : CheckedMoment :=
  CheckedMoment.ofBessel lo0338b1 lo0338b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0338b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨57,by decide⟩
def hi0338b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨58,by decide⟩
def hi0338 : CheckedMoment :=
  CheckedMoment.ofBessel hi0338b1 hi0338b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0338 : meanBracketCheck (1241/10000) lo0338 hi0338=true := by decide +kernel
def bracket0338 : MeanBracket := meanBracketOfMoments (1241/10000) lo0338 hi0338 accepted0338
def lo0339b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨62,by decide⟩
def lo0339b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨63,by decide⟩
def lo0339 : CheckedMoment :=
  CheckedMoment.ofBessel lo0339b1 lo0339b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0339b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨3,by decide⟩
def hi0339b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨4,by decide⟩
def hi0339 : CheckedMoment :=
  CheckedMoment.ofBessel hi0339b1 hi0339b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0339 : meanBracketCheck (1243/10000) lo0339 hi0339=true := by decide +kernel
def bracket0339 : MeanBracket := meanBracketOfMoments (1243/10000) lo0339 hi0339 accepted0339
def lo0340b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨8,by decide⟩
def lo0340b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨9,by decide⟩
def lo0340 : CheckedMoment :=
  CheckedMoment.ofBessel lo0340b1 lo0340b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0340b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨13,by decide⟩
def hi0340b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨14,by decide⟩
def hi0340 : CheckedMoment :=
  CheckedMoment.ofBessel hi0340b1 hi0340b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0340 : meanBracketCheck (249/2000) lo0340 hi0340=true := by decide +kernel
def bracket0340 : MeanBracket := meanBracketOfMoments (249/2000) lo0340 hi0340 accepted0340
def lo0341b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨18,by decide⟩
def lo0341b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨19,by decide⟩
def lo0341 : CheckedMoment :=
  CheckedMoment.ofBessel lo0341b1 lo0341b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0341b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨23,by decide⟩
def hi0341b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨24,by decide⟩
def hi0341 : CheckedMoment :=
  CheckedMoment.ofBessel hi0341b1 hi0341b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0341 : meanBracketCheck (1247/10000) lo0341 hi0341=true := by decide +kernel
def bracket0341 : MeanBracket := meanBracketOfMoments (1247/10000) lo0341 hi0341 accepted0341
def lo0342b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨28,by decide⟩
def lo0342b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨29,by decide⟩
def lo0342 : CheckedMoment :=
  CheckedMoment.ofBessel lo0342b1 lo0342b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0342b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨33,by decide⟩
def hi0342b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨34,by decide⟩
def hi0342 : CheckedMoment :=
  CheckedMoment.ofBessel hi0342b1 hi0342b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0342 : meanBracketCheck (1249/10000) lo0342 hi0342=true := by decide +kernel
def bracket0342 : MeanBracket := meanBracketOfMoments (1249/10000) lo0342 hi0342 accepted0342
def lo0343b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨38,by decide⟩
def lo0343b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨39,by decide⟩
def lo0343 : CheckedMoment :=
  CheckedMoment.ofBessel lo0343b1 lo0343b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0343b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨43,by decide⟩
def hi0343b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨44,by decide⟩
def hi0343 : CheckedMoment :=
  CheckedMoment.ofBessel hi0343b1 hi0343b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0343 : meanBracketCheck (1251/10000) lo0343 hi0343=true := by decide +kernel
def bracket0343 : MeanBracket := meanBracketOfMoments (1251/10000) lo0343 hi0343 accepted0343
def lo0344b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨48,by decide⟩
def lo0344b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨49,by decide⟩
def lo0344 : CheckedMoment :=
  CheckedMoment.ofBessel lo0344b1 lo0344b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0344b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨53,by decide⟩
def hi0344b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨54,by decide⟩
def hi0344 : CheckedMoment :=
  CheckedMoment.ofBessel hi0344b1 hi0344b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0344 : meanBracketCheck (1253/10000) lo0344 hi0344=true := by decide +kernel
def bracket0344 : MeanBracket := meanBracketOfMoments (1253/10000) lo0344 hi0344 accepted0344
def lo0345b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨58,by decide⟩
def lo0345b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨59,by decide⟩
def lo0345 : CheckedMoment :=
  CheckedMoment.ofBessel lo0345b1 lo0345b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0345b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨63,by decide⟩
def hi0345b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨0,by decide⟩
def hi0345 : CheckedMoment :=
  CheckedMoment.ofBessel hi0345b1 hi0345b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0345 : meanBracketCheck (251/2000) lo0345 hi0345=true := by decide +kernel
def bracket0345 : MeanBracket := meanBracketOfMoments (251/2000) lo0345 hi0345 accepted0345
def lo0346b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨4,by decide⟩
def lo0346b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨5,by decide⟩
def lo0346 : CheckedMoment :=
  CheckedMoment.ofBessel lo0346b1 lo0346b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0346b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨9,by decide⟩
def hi0346b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨10,by decide⟩
def hi0346 : CheckedMoment :=
  CheckedMoment.ofBessel hi0346b1 hi0346b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0346 : meanBracketCheck (1257/10000) lo0346 hi0346=true := by decide +kernel
def bracket0346 : MeanBracket := meanBracketOfMoments (1257/10000) lo0346 hi0346 accepted0346
def lo0347b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨14,by decide⟩
def lo0347b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨15,by decide⟩
def lo0347 : CheckedMoment :=
  CheckedMoment.ofBessel lo0347b1 lo0347b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0347b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨19,by decide⟩
def hi0347b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨20,by decide⟩
def hi0347 : CheckedMoment :=
  CheckedMoment.ofBessel hi0347b1 hi0347b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0347 : meanBracketCheck (1259/10000) lo0347 hi0347=true := by decide +kernel
def bracket0347 : MeanBracket := meanBracketOfMoments (1259/10000) lo0347 hi0347 accepted0347
def lo0348b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨24,by decide⟩
def lo0348b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨25,by decide⟩
def lo0348 : CheckedMoment :=
  CheckedMoment.ofBessel lo0348b1 lo0348b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0348b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨29,by decide⟩
def hi0348b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨30,by decide⟩
def hi0348 : CheckedMoment :=
  CheckedMoment.ofBessel hi0348b1 hi0348b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0348 : meanBracketCheck (1261/10000) lo0348 hi0348=true := by decide +kernel
def bracket0348 : MeanBracket := meanBracketOfMoments (1261/10000) lo0348 hi0348 accepted0348
def lo0349b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨34,by decide⟩
def lo0349b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨35,by decide⟩
def lo0349 : CheckedMoment :=
  CheckedMoment.ofBessel lo0349b1 lo0349b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0349b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨39,by decide⟩
def hi0349b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨40,by decide⟩
def hi0349 : CheckedMoment :=
  CheckedMoment.ofBessel hi0349b1 hi0349b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0349 : meanBracketCheck (1263/10000) lo0349 hi0349=true := by decide +kernel
def bracket0349 : MeanBracket := meanBracketOfMoments (1263/10000) lo0349 hi0349 accepted0349
def lo0350b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨44,by decide⟩
def lo0350b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨45,by decide⟩
def lo0350 : CheckedMoment :=
  CheckedMoment.ofBessel lo0350b1 lo0350b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0350b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨49,by decide⟩
def hi0350b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨50,by decide⟩
def hi0350 : CheckedMoment :=
  CheckedMoment.ofBessel hi0350b1 hi0350b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0350 : meanBracketCheck (253/2000) lo0350 hi0350=true := by decide +kernel
def bracket0350 : MeanBracket := meanBracketOfMoments (253/2000) lo0350 hi0350 accepted0350
def lo0351b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨54,by decide⟩
def lo0351b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨55,by decide⟩
def lo0351 : CheckedMoment :=
  CheckedMoment.ofBessel lo0351b1 lo0351b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0351b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨59,by decide⟩
def hi0351b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨60,by decide⟩
def hi0351 : CheckedMoment :=
  CheckedMoment.ofBessel hi0351b1 hi0351b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0351 : meanBracketCheck (1267/10000) lo0351 hi0351=true := by decide +kernel
def bracket0351 : MeanBracket := meanBracketOfMoments (1267/10000) lo0351 hi0351 accepted0351
#print axioms bracket0336
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0021
