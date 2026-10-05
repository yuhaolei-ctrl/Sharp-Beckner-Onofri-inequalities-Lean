module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0235
public import BecknerOnofri.EntropyScalarCertificate.Bessel0236
public import BecknerOnofri.EntropyScalarCertificate.Bessel0237

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0094
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1504b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨0,by decide⟩
def lo1504b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨1,by decide⟩
def lo1504 : CheckedMoment :=
  CheckedMoment.ofBessel lo1504b1 lo1504b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1504b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨5,by decide⟩
def hi1504b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨6,by decide⟩
def hi1504 : CheckedMoment :=
  CheckedMoment.ofBessel hi1504b1 hi1504b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1504 : meanBracketCheck (4213/5000) lo1504 hi1504=true := by decide +kernel
def bracket1504 : MeanBracket := meanBracketOfMoments (4213/5000) lo1504 hi1504 accepted1504
def lo1505b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨10,by decide⟩
def lo1505b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨11,by decide⟩
def lo1505 : CheckedMoment :=
  CheckedMoment.ofBessel lo1505b1 lo1505b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1505b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨15,by decide⟩
def hi1505b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨16,by decide⟩
def hi1505 : CheckedMoment :=
  CheckedMoment.ofBessel hi1505b1 hi1505b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1505 : meanBracketCheck (8427/10000) lo1505 hi1505=true := by decide +kernel
def bracket1505 : MeanBracket := meanBracketOfMoments (8427/10000) lo1505 hi1505 accepted1505
def lo1506b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨20,by decide⟩
def lo1506b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨21,by decide⟩
def lo1506 : CheckedMoment :=
  CheckedMoment.ofBessel lo1506b1 lo1506b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1506b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨25,by decide⟩
def hi1506b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨26,by decide⟩
def hi1506 : CheckedMoment :=
  CheckedMoment.ofBessel hi1506b1 hi1506b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1506 : meanBracketCheck (2107/2500) lo1506 hi1506=true := by decide +kernel
def bracket1506 : MeanBracket := meanBracketOfMoments (2107/2500) lo1506 hi1506 accepted1506
def lo1507b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨30,by decide⟩
def lo1507b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨31,by decide⟩
def lo1507 : CheckedMoment :=
  CheckedMoment.ofBessel lo1507b1 lo1507b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1507b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨35,by decide⟩
def hi1507b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨36,by decide⟩
def hi1507 : CheckedMoment :=
  CheckedMoment.ofBessel hi1507b1 hi1507b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1507 : meanBracketCheck (8429/10000) lo1507 hi1507=true := by decide +kernel
def bracket1507 : MeanBracket := meanBracketOfMoments (8429/10000) lo1507 hi1507 accepted1507
def lo1508b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨40,by decide⟩
def lo1508b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨41,by decide⟩
def lo1508 : CheckedMoment :=
  CheckedMoment.ofBessel lo1508b1 lo1508b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1508b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨45,by decide⟩
def hi1508b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨46,by decide⟩
def hi1508 : CheckedMoment :=
  CheckedMoment.ofBessel hi1508b1 hi1508b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1508 : meanBracketCheck (843/1000) lo1508 hi1508=true := by decide +kernel
def bracket1508 : MeanBracket := meanBracketOfMoments (843/1000) lo1508 hi1508 accepted1508
def lo1509b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨50,by decide⟩
def lo1509b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨51,by decide⟩
def lo1509 : CheckedMoment :=
  CheckedMoment.ofBessel lo1509b1 lo1509b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1509b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨55,by decide⟩
def hi1509b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨56,by decide⟩
def hi1509 : CheckedMoment :=
  CheckedMoment.ofBessel hi1509b1 hi1509b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1509 : meanBracketCheck (8431/10000) lo1509 hi1509=true := by decide +kernel
def bracket1509 : MeanBracket := meanBracketOfMoments (8431/10000) lo1509 hi1509 accepted1509
def lo1510b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨60,by decide⟩
def lo1510b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨61,by decide⟩
def lo1510 : CheckedMoment :=
  CheckedMoment.ofBessel lo1510b1 lo1510b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1510b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨1,by decide⟩
def hi1510b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨2,by decide⟩
def hi1510 : CheckedMoment :=
  CheckedMoment.ofBessel hi1510b1 hi1510b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1510 : meanBracketCheck (527/625) lo1510 hi1510=true := by decide +kernel
def bracket1510 : MeanBracket := meanBracketOfMoments (527/625) lo1510 hi1510 accepted1510
def lo1511b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨6,by decide⟩
def lo1511b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨7,by decide⟩
def lo1511 : CheckedMoment :=
  CheckedMoment.ofBessel lo1511b1 lo1511b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1511b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨11,by decide⟩
def hi1511b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨12,by decide⟩
def hi1511 : CheckedMoment :=
  CheckedMoment.ofBessel hi1511b1 hi1511b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1511 : meanBracketCheck (8433/10000) lo1511 hi1511=true := by decide +kernel
def bracket1511 : MeanBracket := meanBracketOfMoments (8433/10000) lo1511 hi1511 accepted1511
def lo1512b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨16,by decide⟩
def lo1512b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨17,by decide⟩
def lo1512 : CheckedMoment :=
  CheckedMoment.ofBessel lo1512b1 lo1512b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1512b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨21,by decide⟩
def hi1512b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨22,by decide⟩
def hi1512 : CheckedMoment :=
  CheckedMoment.ofBessel hi1512b1 hi1512b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1512 : meanBracketCheck (4217/5000) lo1512 hi1512=true := by decide +kernel
def bracket1512 : MeanBracket := meanBracketOfMoments (4217/5000) lo1512 hi1512 accepted1512
def lo1513b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨26,by decide⟩
def lo1513b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨27,by decide⟩
def lo1513 : CheckedMoment :=
  CheckedMoment.ofBessel lo1513b1 lo1513b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1513b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨31,by decide⟩
def hi1513b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨32,by decide⟩
def hi1513 : CheckedMoment :=
  CheckedMoment.ofBessel hi1513b1 hi1513b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1513 : meanBracketCheck (1687/2000) lo1513 hi1513=true := by decide +kernel
def bracket1513 : MeanBracket := meanBracketOfMoments (1687/2000) lo1513 hi1513 accepted1513
def lo1514b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨36,by decide⟩
def lo1514b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨37,by decide⟩
def lo1514 : CheckedMoment :=
  CheckedMoment.ofBessel lo1514b1 lo1514b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1514b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨41,by decide⟩
def hi1514b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨42,by decide⟩
def hi1514 : CheckedMoment :=
  CheckedMoment.ofBessel hi1514b1 hi1514b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1514 : meanBracketCheck (2109/2500) lo1514 hi1514=true := by decide +kernel
def bracket1514 : MeanBracket := meanBracketOfMoments (2109/2500) lo1514 hi1514 accepted1514
def lo1515b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨46,by decide⟩
def lo1515b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨47,by decide⟩
def lo1515 : CheckedMoment :=
  CheckedMoment.ofBessel lo1515b1 lo1515b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1515b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨51,by decide⟩
def hi1515b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨52,by decide⟩
def hi1515 : CheckedMoment :=
  CheckedMoment.ofBessel hi1515b1 hi1515b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1515 : meanBracketCheck (8437/10000) lo1515 hi1515=true := by decide +kernel
def bracket1515 : MeanBracket := meanBracketOfMoments (8437/10000) lo1515 hi1515 accepted1515
def lo1516b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨56,by decide⟩
def lo1516b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨57,by decide⟩
def lo1516 : CheckedMoment :=
  CheckedMoment.ofBessel lo1516b1 lo1516b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1516b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨61,by decide⟩
def hi1516b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨62,by decide⟩
def hi1516 : CheckedMoment :=
  CheckedMoment.ofBessel hi1516b1 hi1516b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1516 : meanBracketCheck (4219/5000) lo1516 hi1516=true := by decide +kernel
def bracket1516 : MeanBracket := meanBracketOfMoments (4219/5000) lo1516 hi1516 accepted1516
def lo1517b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨2,by decide⟩
def lo1517b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨3,by decide⟩
def lo1517 : CheckedMoment :=
  CheckedMoment.ofBessel lo1517b1 lo1517b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1517b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨7,by decide⟩
def hi1517b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨8,by decide⟩
def hi1517 : CheckedMoment :=
  CheckedMoment.ofBessel hi1517b1 hi1517b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1517 : meanBracketCheck (8439/10000) lo1517 hi1517=true := by decide +kernel
def bracket1517 : MeanBracket := meanBracketOfMoments (8439/10000) lo1517 hi1517 accepted1517
def lo1518b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨12,by decide⟩
def lo1518b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨13,by decide⟩
def lo1518 : CheckedMoment :=
  CheckedMoment.ofBessel lo1518b1 lo1518b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1518b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨17,by decide⟩
def hi1518b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨18,by decide⟩
def hi1518 : CheckedMoment :=
  CheckedMoment.ofBessel hi1518b1 hi1518b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1518 : meanBracketCheck (211/250) lo1518 hi1518=true := by decide +kernel
def bracket1518 : MeanBracket := meanBracketOfMoments (211/250) lo1518 hi1518 accepted1518
def lo1519b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨22,by decide⟩
def lo1519b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨23,by decide⟩
def lo1519 : CheckedMoment :=
  CheckedMoment.ofBessel lo1519b1 lo1519b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1519b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨27,by decide⟩
def hi1519b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨28,by decide⟩
def hi1519 : CheckedMoment :=
  CheckedMoment.ofBessel hi1519b1 hi1519b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1519 : meanBracketCheck (8441/10000) lo1519 hi1519=true := by decide +kernel
def bracket1519 : MeanBracket := meanBracketOfMoments (8441/10000) lo1519 hi1519 accepted1519
#print axioms bracket1504
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0094
