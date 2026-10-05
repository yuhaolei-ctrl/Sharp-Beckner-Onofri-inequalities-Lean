module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0265
public import BecknerOnofri.EntropyScalarCertificate.Bessel0266
public import BecknerOnofri.EntropyScalarCertificate.Bessel0267

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0106
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1696b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨0,by decide⟩
def lo1696b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨1,by decide⟩
def lo1696 : CheckedMoment :=
  CheckedMoment.ofBessel lo1696b1 lo1696b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1696b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨5,by decide⟩
def hi1696b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨6,by decide⟩
def hi1696 : CheckedMoment :=
  CheckedMoment.ofBessel hi1696b1 hi1696b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1696 : meanBracketCheck (4309/5000) lo1696 hi1696=true := by decide +kernel
def bracket1696 : MeanBracket := meanBracketOfMoments (4309/5000) lo1696 hi1696 accepted1696
def lo1697b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨10,by decide⟩
def lo1697b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨11,by decide⟩
def lo1697 : CheckedMoment :=
  CheckedMoment.ofBessel lo1697b1 lo1697b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1697b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨15,by decide⟩
def hi1697b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨16,by decide⟩
def hi1697 : CheckedMoment :=
  CheckedMoment.ofBessel hi1697b1 hi1697b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1697 : meanBracketCheck (8619/10000) lo1697 hi1697=true := by decide +kernel
def bracket1697 : MeanBracket := meanBracketOfMoments (8619/10000) lo1697 hi1697 accepted1697
def lo1698b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨20,by decide⟩
def lo1698b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨21,by decide⟩
def lo1698 : CheckedMoment :=
  CheckedMoment.ofBessel lo1698b1 lo1698b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1698b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨25,by decide⟩
def hi1698b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨26,by decide⟩
def hi1698 : CheckedMoment :=
  CheckedMoment.ofBessel hi1698b1 hi1698b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1698 : meanBracketCheck (431/500) lo1698 hi1698=true := by decide +kernel
def bracket1698 : MeanBracket := meanBracketOfMoments (431/500) lo1698 hi1698 accepted1698
def lo1699b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨30,by decide⟩
def lo1699b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨31,by decide⟩
def lo1699 : CheckedMoment :=
  CheckedMoment.ofBessel lo1699b1 lo1699b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1699b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨35,by decide⟩
def hi1699b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨36,by decide⟩
def hi1699 : CheckedMoment :=
  CheckedMoment.ofBessel hi1699b1 hi1699b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1699 : meanBracketCheck (8621/10000) lo1699 hi1699=true := by decide +kernel
def bracket1699 : MeanBracket := meanBracketOfMoments (8621/10000) lo1699 hi1699 accepted1699
def lo1700b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨40,by decide⟩
def lo1700b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨41,by decide⟩
def lo1700 : CheckedMoment :=
  CheckedMoment.ofBessel lo1700b1 lo1700b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1700b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨45,by decide⟩
def hi1700b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨46,by decide⟩
def hi1700 : CheckedMoment :=
  CheckedMoment.ofBessel hi1700b1 hi1700b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1700 : meanBracketCheck (4311/5000) lo1700 hi1700=true := by decide +kernel
def bracket1700 : MeanBracket := meanBracketOfMoments (4311/5000) lo1700 hi1700 accepted1700
def lo1701b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨50,by decide⟩
def lo1701b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨51,by decide⟩
def lo1701 : CheckedMoment :=
  CheckedMoment.ofBessel lo1701b1 lo1701b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1701b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨55,by decide⟩
def hi1701b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨56,by decide⟩
def hi1701 : CheckedMoment :=
  CheckedMoment.ofBessel hi1701b1 hi1701b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1701 : meanBracketCheck (8623/10000) lo1701 hi1701=true := by decide +kernel
def bracket1701 : MeanBracket := meanBracketOfMoments (8623/10000) lo1701 hi1701 accepted1701
def lo1702b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨60,by decide⟩
def lo1702b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨61,by decide⟩
def lo1702 : CheckedMoment :=
  CheckedMoment.ofBessel lo1702b1 lo1702b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1702b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨1,by decide⟩
def hi1702b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨2,by decide⟩
def hi1702 : CheckedMoment :=
  CheckedMoment.ofBessel hi1702b1 hi1702b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1702 : meanBracketCheck (539/625) lo1702 hi1702=true := by decide +kernel
def bracket1702 : MeanBracket := meanBracketOfMoments (539/625) lo1702 hi1702 accepted1702
def lo1703b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨6,by decide⟩
def lo1703b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨7,by decide⟩
def lo1703 : CheckedMoment :=
  CheckedMoment.ofBessel lo1703b1 lo1703b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1703b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨11,by decide⟩
def hi1703b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨12,by decide⟩
def hi1703 : CheckedMoment :=
  CheckedMoment.ofBessel hi1703b1 hi1703b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1703 : meanBracketCheck (69/80) lo1703 hi1703=true := by decide +kernel
def bracket1703 : MeanBracket := meanBracketOfMoments (69/80) lo1703 hi1703 accepted1703
def lo1704b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨16,by decide⟩
def lo1704b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨17,by decide⟩
def lo1704 : CheckedMoment :=
  CheckedMoment.ofBessel lo1704b1 lo1704b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1704b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨21,by decide⟩
def hi1704b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨22,by decide⟩
def hi1704 : CheckedMoment :=
  CheckedMoment.ofBessel hi1704b1 hi1704b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1704 : meanBracketCheck (4313/5000) lo1704 hi1704=true := by decide +kernel
def bracket1704 : MeanBracket := meanBracketOfMoments (4313/5000) lo1704 hi1704 accepted1704
def lo1705b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨26,by decide⟩
def lo1705b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨27,by decide⟩
def lo1705 : CheckedMoment :=
  CheckedMoment.ofBessel lo1705b1 lo1705b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1705b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨31,by decide⟩
def hi1705b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨32,by decide⟩
def hi1705 : CheckedMoment :=
  CheckedMoment.ofBessel hi1705b1 hi1705b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1705 : meanBracketCheck (8627/10000) lo1705 hi1705=true := by decide +kernel
def bracket1705 : MeanBracket := meanBracketOfMoments (8627/10000) lo1705 hi1705 accepted1705
def lo1706b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨36,by decide⟩
def lo1706b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨37,by decide⟩
def lo1706 : CheckedMoment :=
  CheckedMoment.ofBessel lo1706b1 lo1706b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1706b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨41,by decide⟩
def hi1706b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨42,by decide⟩
def hi1706 : CheckedMoment :=
  CheckedMoment.ofBessel hi1706b1 hi1706b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1706 : meanBracketCheck (2157/2500) lo1706 hi1706=true := by decide +kernel
def bracket1706 : MeanBracket := meanBracketOfMoments (2157/2500) lo1706 hi1706 accepted1706
def lo1707b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨46,by decide⟩
def lo1707b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨47,by decide⟩
def lo1707 : CheckedMoment :=
  CheckedMoment.ofBessel lo1707b1 lo1707b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1707b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨51,by decide⟩
def hi1707b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨52,by decide⟩
def hi1707 : CheckedMoment :=
  CheckedMoment.ofBessel hi1707b1 hi1707b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1707 : meanBracketCheck (8629/10000) lo1707 hi1707=true := by decide +kernel
def bracket1707 : MeanBracket := meanBracketOfMoments (8629/10000) lo1707 hi1707 accepted1707
def lo1708b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨56,by decide⟩
def lo1708b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨57,by decide⟩
def lo1708 : CheckedMoment :=
  CheckedMoment.ofBessel lo1708b1 lo1708b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1708b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨61,by decide⟩
def hi1708b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨62,by decide⟩
def hi1708 : CheckedMoment :=
  CheckedMoment.ofBessel hi1708b1 hi1708b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1708 : meanBracketCheck (863/1000) lo1708 hi1708=true := by decide +kernel
def bracket1708 : MeanBracket := meanBracketOfMoments (863/1000) lo1708 hi1708 accepted1708
def lo1709b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨2,by decide⟩
def lo1709b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨3,by decide⟩
def lo1709 : CheckedMoment :=
  CheckedMoment.ofBessel lo1709b1 lo1709b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1709b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨7,by decide⟩
def hi1709b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨8,by decide⟩
def hi1709 : CheckedMoment :=
  CheckedMoment.ofBessel hi1709b1 hi1709b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1709 : meanBracketCheck (8631/10000) lo1709 hi1709=true := by decide +kernel
def bracket1709 : MeanBracket := meanBracketOfMoments (8631/10000) lo1709 hi1709 accepted1709
def lo1710b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨12,by decide⟩
def lo1710b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨13,by decide⟩
def lo1710 : CheckedMoment :=
  CheckedMoment.ofBessel lo1710b1 lo1710b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1710b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨17,by decide⟩
def hi1710b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨18,by decide⟩
def hi1710 : CheckedMoment :=
  CheckedMoment.ofBessel hi1710b1 hi1710b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1710 : meanBracketCheck (1079/1250) lo1710 hi1710=true := by decide +kernel
def bracket1710 : MeanBracket := meanBracketOfMoments (1079/1250) lo1710 hi1710 accepted1710
def lo1711b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨22,by decide⟩
def lo1711b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨23,by decide⟩
def lo1711 : CheckedMoment :=
  CheckedMoment.ofBessel lo1711b1 lo1711b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1711b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨27,by decide⟩
def hi1711b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨28,by decide⟩
def hi1711 : CheckedMoment :=
  CheckedMoment.ofBessel hi1711b1 hi1711b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1711 : meanBracketCheck (8633/10000) lo1711 hi1711=true := by decide +kernel
def bracket1711 : MeanBracket := meanBracketOfMoments (8633/10000) lo1711 hi1711 accepted1711
#print axioms bracket1696
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0106
