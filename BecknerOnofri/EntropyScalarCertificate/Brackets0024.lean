module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0060
public import BecknerOnofri.EntropyScalarCertificate.Bessel0061
public import BecknerOnofri.EntropyScalarCertificate.Bessel0062

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0024
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0384b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨0,by decide⟩
def lo0384b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨1,by decide⟩
def lo0384 : CheckedMoment :=
  CheckedMoment.ofBessel lo0384b1 lo0384b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0384b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨5,by decide⟩
def hi0384b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨6,by decide⟩
def hi0384 : CheckedMoment :=
  CheckedMoment.ofBessel hi0384b1 hi0384b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0384 : meanBracketCheck (1333/10000) lo0384 hi0384=true := by decide +kernel
def bracket0384 : MeanBracket := meanBracketOfMoments (1333/10000) lo0384 hi0384 accepted0384
def lo0385b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨10,by decide⟩
def lo0385b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨11,by decide⟩
def lo0385 : CheckedMoment :=
  CheckedMoment.ofBessel lo0385b1 lo0385b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0385b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨15,by decide⟩
def hi0385b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨16,by decide⟩
def hi0385 : CheckedMoment :=
  CheckedMoment.ofBessel hi0385b1 hi0385b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0385 : meanBracketCheck (267/2000) lo0385 hi0385=true := by decide +kernel
def bracket0385 : MeanBracket := meanBracketOfMoments (267/2000) lo0385 hi0385 accepted0385
def lo0386b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨20,by decide⟩
def lo0386b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨21,by decide⟩
def lo0386 : CheckedMoment :=
  CheckedMoment.ofBessel lo0386b1 lo0386b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0386b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨25,by decide⟩
def hi0386b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨26,by decide⟩
def hi0386 : CheckedMoment :=
  CheckedMoment.ofBessel hi0386b1 hi0386b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0386 : meanBracketCheck (1337/10000) lo0386 hi0386=true := by decide +kernel
def bracket0386 : MeanBracket := meanBracketOfMoments (1337/10000) lo0386 hi0386 accepted0386
def lo0387b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨30,by decide⟩
def lo0387b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨31,by decide⟩
def lo0387 : CheckedMoment :=
  CheckedMoment.ofBessel lo0387b1 lo0387b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0387b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨35,by decide⟩
def hi0387b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨36,by decide⟩
def hi0387 : CheckedMoment :=
  CheckedMoment.ofBessel hi0387b1 hi0387b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0387 : meanBracketCheck (1339/10000) lo0387 hi0387=true := by decide +kernel
def bracket0387 : MeanBracket := meanBracketOfMoments (1339/10000) lo0387 hi0387 accepted0387
def lo0388b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨40,by decide⟩
def lo0388b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨41,by decide⟩
def lo0388 : CheckedMoment :=
  CheckedMoment.ofBessel lo0388b1 lo0388b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0388b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨45,by decide⟩
def hi0388b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨46,by decide⟩
def hi0388 : CheckedMoment :=
  CheckedMoment.ofBessel hi0388b1 hi0388b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0388 : meanBracketCheck (1341/10000) lo0388 hi0388=true := by decide +kernel
def bracket0388 : MeanBracket := meanBracketOfMoments (1341/10000) lo0388 hi0388 accepted0388
def lo0389b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨50,by decide⟩
def lo0389b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨51,by decide⟩
def lo0389 : CheckedMoment :=
  CheckedMoment.ofBessel lo0389b1 lo0389b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0389b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨55,by decide⟩
def hi0389b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨56,by decide⟩
def hi0389 : CheckedMoment :=
  CheckedMoment.ofBessel hi0389b1 hi0389b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0389 : meanBracketCheck (1343/10000) lo0389 hi0389=true := by decide +kernel
def bracket0389 : MeanBracket := meanBracketOfMoments (1343/10000) lo0389 hi0389 accepted0389
def lo0390b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨60,by decide⟩
def lo0390b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨61,by decide⟩
def lo0390 : CheckedMoment :=
  CheckedMoment.ofBessel lo0390b1 lo0390b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0390b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨1,by decide⟩
def hi0390b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨2,by decide⟩
def hi0390 : CheckedMoment :=
  CheckedMoment.ofBessel hi0390b1 hi0390b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0390 : meanBracketCheck (269/2000) lo0390 hi0390=true := by decide +kernel
def bracket0390 : MeanBracket := meanBracketOfMoments (269/2000) lo0390 hi0390 accepted0390
def lo0391b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨6,by decide⟩
def lo0391b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨7,by decide⟩
def lo0391 : CheckedMoment :=
  CheckedMoment.ofBessel lo0391b1 lo0391b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0391b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨11,by decide⟩
def hi0391b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨12,by decide⟩
def hi0391 : CheckedMoment :=
  CheckedMoment.ofBessel hi0391b1 hi0391b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0391 : meanBracketCheck (1347/10000) lo0391 hi0391=true := by decide +kernel
def bracket0391 : MeanBracket := meanBracketOfMoments (1347/10000) lo0391 hi0391 accepted0391
def lo0392b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨16,by decide⟩
def lo0392b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨17,by decide⟩
def lo0392 : CheckedMoment :=
  CheckedMoment.ofBessel lo0392b1 lo0392b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0392b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨21,by decide⟩
def hi0392b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨22,by decide⟩
def hi0392 : CheckedMoment :=
  CheckedMoment.ofBessel hi0392b1 hi0392b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0392 : meanBracketCheck (1349/10000) lo0392 hi0392=true := by decide +kernel
def bracket0392 : MeanBracket := meanBracketOfMoments (1349/10000) lo0392 hi0392 accepted0392
def lo0393b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨26,by decide⟩
def lo0393b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨27,by decide⟩
def lo0393 : CheckedMoment :=
  CheckedMoment.ofBessel lo0393b1 lo0393b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0393b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨31,by decide⟩
def hi0393b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨32,by decide⟩
def hi0393 : CheckedMoment :=
  CheckedMoment.ofBessel hi0393b1 hi0393b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0393 : meanBracketCheck (1351/10000) lo0393 hi0393=true := by decide +kernel
def bracket0393 : MeanBracket := meanBracketOfMoments (1351/10000) lo0393 hi0393 accepted0393
def lo0394b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨36,by decide⟩
def lo0394b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨37,by decide⟩
def lo0394 : CheckedMoment :=
  CheckedMoment.ofBessel lo0394b1 lo0394b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0394b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨41,by decide⟩
def hi0394b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨42,by decide⟩
def hi0394 : CheckedMoment :=
  CheckedMoment.ofBessel hi0394b1 hi0394b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0394 : meanBracketCheck (1353/10000) lo0394 hi0394=true := by decide +kernel
def bracket0394 : MeanBracket := meanBracketOfMoments (1353/10000) lo0394 hi0394 accepted0394
def lo0395b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨46,by decide⟩
def lo0395b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨47,by decide⟩
def lo0395 : CheckedMoment :=
  CheckedMoment.ofBessel lo0395b1 lo0395b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0395b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨51,by decide⟩
def hi0395b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨52,by decide⟩
def hi0395 : CheckedMoment :=
  CheckedMoment.ofBessel hi0395b1 hi0395b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0395 : meanBracketCheck (271/2000) lo0395 hi0395=true := by decide +kernel
def bracket0395 : MeanBracket := meanBracketOfMoments (271/2000) lo0395 hi0395 accepted0395
def lo0396b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨56,by decide⟩
def lo0396b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨57,by decide⟩
def lo0396 : CheckedMoment :=
  CheckedMoment.ofBessel lo0396b1 lo0396b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0396b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨61,by decide⟩
def hi0396b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨62,by decide⟩
def hi0396 : CheckedMoment :=
  CheckedMoment.ofBessel hi0396b1 hi0396b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0396 : meanBracketCheck (1357/10000) lo0396 hi0396=true := by decide +kernel
def bracket0396 : MeanBracket := meanBracketOfMoments (1357/10000) lo0396 hi0396 accepted0396
def lo0397b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨2,by decide⟩
def lo0397b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨3,by decide⟩
def lo0397 : CheckedMoment :=
  CheckedMoment.ofBessel lo0397b1 lo0397b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0397b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨7,by decide⟩
def hi0397b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨8,by decide⟩
def hi0397 : CheckedMoment :=
  CheckedMoment.ofBessel hi0397b1 hi0397b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0397 : meanBracketCheck (1359/10000) lo0397 hi0397=true := by decide +kernel
def bracket0397 : MeanBracket := meanBracketOfMoments (1359/10000) lo0397 hi0397 accepted0397
def lo0398b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨12,by decide⟩
def lo0398b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨13,by decide⟩
def lo0398 : CheckedMoment :=
  CheckedMoment.ofBessel lo0398b1 lo0398b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0398b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨17,by decide⟩
def hi0398b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨18,by decide⟩
def hi0398 : CheckedMoment :=
  CheckedMoment.ofBessel hi0398b1 hi0398b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0398 : meanBracketCheck (1361/10000) lo0398 hi0398=true := by decide +kernel
def bracket0398 : MeanBracket := meanBracketOfMoments (1361/10000) lo0398 hi0398 accepted0398
def lo0399b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨22,by decide⟩
def lo0399b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨23,by decide⟩
def lo0399 : CheckedMoment :=
  CheckedMoment.ofBessel lo0399b1 lo0399b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0399b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨27,by decide⟩
def hi0399b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨28,by decide⟩
def hi0399 : CheckedMoment :=
  CheckedMoment.ofBessel hi0399b1 hi0399b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0399 : meanBracketCheck (1363/10000) lo0399 hi0399=true := by decide +kernel
def bracket0399 : MeanBracket := meanBracketOfMoments (1363/10000) lo0399 hi0399 accepted0399
#print axioms bracket0384
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0024
