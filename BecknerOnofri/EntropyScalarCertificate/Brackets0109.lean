import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0272
import BecknerOnofri.EntropyScalarCertificate.Bessel0273
import BecknerOnofri.EntropyScalarCertificate.Bessel0274
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0109
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1744b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨32,by decide⟩
def lo1744b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨33,by decide⟩
def lo1744 : CheckedMoment :=
  CheckedMoment.ofBessel lo1744b1 lo1744b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1744b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨37,by decide⟩
def hi1744b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨38,by decide⟩
def hi1744 : CheckedMoment :=
  CheckedMoment.ofBessel hi1744b1 hi1744b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1744 : meanBracketCheck (4333/5000) lo1744 hi1744=true := by decide +kernel
def bracket1744 : MeanBracket := meanBracketOfMoments (4333/5000) lo1744 hi1744 accepted1744
def lo1745b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨42,by decide⟩
def lo1745b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨43,by decide⟩
def lo1745 : CheckedMoment :=
  CheckedMoment.ofBessel lo1745b1 lo1745b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1745b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨47,by decide⟩
def hi1745b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨48,by decide⟩
def hi1745 : CheckedMoment :=
  CheckedMoment.ofBessel hi1745b1 hi1745b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1745 : meanBracketCheck (8667/10000) lo1745 hi1745=true := by decide +kernel
def bracket1745 : MeanBracket := meanBracketOfMoments (8667/10000) lo1745 hi1745 accepted1745
def lo1746b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨52,by decide⟩
def lo1746b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨53,by decide⟩
def lo1746 : CheckedMoment :=
  CheckedMoment.ofBessel lo1746b1 lo1746b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1746b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨57,by decide⟩
def hi1746b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨58,by decide⟩
def hi1746 : CheckedMoment :=
  CheckedMoment.ofBessel hi1746b1 hi1746b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1746 : meanBracketCheck (2167/2500) lo1746 hi1746=true := by decide +kernel
def bracket1746 : MeanBracket := meanBracketOfMoments (2167/2500) lo1746 hi1746 accepted1746
def lo1747b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨62,by decide⟩
def lo1747b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨63,by decide⟩
def lo1747 : CheckedMoment :=
  CheckedMoment.ofBessel lo1747b1 lo1747b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1747b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨3,by decide⟩
def hi1747b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨4,by decide⟩
def hi1747 : CheckedMoment :=
  CheckedMoment.ofBessel hi1747b1 hi1747b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1747 : meanBracketCheck (8669/10000) lo1747 hi1747=true := by decide +kernel
def bracket1747 : MeanBracket := meanBracketOfMoments (8669/10000) lo1747 hi1747 accepted1747
def lo1748b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨8,by decide⟩
def lo1748b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨9,by decide⟩
def lo1748 : CheckedMoment :=
  CheckedMoment.ofBessel lo1748b1 lo1748b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1748b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨13,by decide⟩
def hi1748b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨14,by decide⟩
def hi1748 : CheckedMoment :=
  CheckedMoment.ofBessel hi1748b1 hi1748b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1748 : meanBracketCheck (867/1000) lo1748 hi1748=true := by decide +kernel
def bracket1748 : MeanBracket := meanBracketOfMoments (867/1000) lo1748 hi1748 accepted1748
def lo1749b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨18,by decide⟩
def lo1749b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨19,by decide⟩
def lo1749 : CheckedMoment :=
  CheckedMoment.ofBessel lo1749b1 lo1749b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1749b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨23,by decide⟩
def hi1749b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨24,by decide⟩
def hi1749 : CheckedMoment :=
  CheckedMoment.ofBessel hi1749b1 hi1749b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1749 : meanBracketCheck (8671/10000) lo1749 hi1749=true := by decide +kernel
def bracket1749 : MeanBracket := meanBracketOfMoments (8671/10000) lo1749 hi1749 accepted1749
def lo1750b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨28,by decide⟩
def lo1750b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨29,by decide⟩
def lo1750 : CheckedMoment :=
  CheckedMoment.ofBessel lo1750b1 lo1750b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1750b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨33,by decide⟩
def hi1750b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨34,by decide⟩
def hi1750 : CheckedMoment :=
  CheckedMoment.ofBessel hi1750b1 hi1750b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1750 : meanBracketCheck (542/625) lo1750 hi1750=true := by decide +kernel
def bracket1750 : MeanBracket := meanBracketOfMoments (542/625) lo1750 hi1750 accepted1750
def lo1751b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨38,by decide⟩
def lo1751b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨39,by decide⟩
def lo1751 : CheckedMoment :=
  CheckedMoment.ofBessel lo1751b1 lo1751b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1751b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨43,by decide⟩
def hi1751b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨44,by decide⟩
def hi1751 : CheckedMoment :=
  CheckedMoment.ofBessel hi1751b1 hi1751b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1751 : meanBracketCheck (8673/10000) lo1751 hi1751=true := by decide +kernel
def bracket1751 : MeanBracket := meanBracketOfMoments (8673/10000) lo1751 hi1751 accepted1751
def lo1752b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨48,by decide⟩
def lo1752b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨49,by decide⟩
def lo1752 : CheckedMoment :=
  CheckedMoment.ofBessel lo1752b1 lo1752b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1752b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨53,by decide⟩
def hi1752b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨54,by decide⟩
def hi1752 : CheckedMoment :=
  CheckedMoment.ofBessel hi1752b1 hi1752b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1752 : meanBracketCheck (4337/5000) lo1752 hi1752=true := by decide +kernel
def bracket1752 : MeanBracket := meanBracketOfMoments (4337/5000) lo1752 hi1752 accepted1752
def lo1753b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨58,by decide⟩
def lo1753b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨59,by decide⟩
def lo1753 : CheckedMoment :=
  CheckedMoment.ofBessel lo1753b1 lo1753b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1753b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨63,by decide⟩
def hi1753b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨0,by decide⟩
def hi1753 : CheckedMoment :=
  CheckedMoment.ofBessel hi1753b1 hi1753b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1753 : meanBracketCheck (347/400) lo1753 hi1753=true := by decide +kernel
def bracket1753 : MeanBracket := meanBracketOfMoments (347/400) lo1753 hi1753 accepted1753
def lo1754b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨4,by decide⟩
def lo1754b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨5,by decide⟩
def lo1754 : CheckedMoment :=
  CheckedMoment.ofBessel lo1754b1 lo1754b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1754b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨9,by decide⟩
def hi1754b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨10,by decide⟩
def hi1754 : CheckedMoment :=
  CheckedMoment.ofBessel hi1754b1 hi1754b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1754 : meanBracketCheck (2169/2500) lo1754 hi1754=true := by decide +kernel
def bracket1754 : MeanBracket := meanBracketOfMoments (2169/2500) lo1754 hi1754 accepted1754
def lo1755b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨14,by decide⟩
def lo1755b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨15,by decide⟩
def lo1755 : CheckedMoment :=
  CheckedMoment.ofBessel lo1755b1 lo1755b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1755b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨19,by decide⟩
def hi1755b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨20,by decide⟩
def hi1755 : CheckedMoment :=
  CheckedMoment.ofBessel hi1755b1 hi1755b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1755 : meanBracketCheck (8677/10000) lo1755 hi1755=true := by decide +kernel
def bracket1755 : MeanBracket := meanBracketOfMoments (8677/10000) lo1755 hi1755 accepted1755
def lo1756b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨24,by decide⟩
def lo1756b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨25,by decide⟩
def lo1756 : CheckedMoment :=
  CheckedMoment.ofBessel lo1756b1 lo1756b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1756b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨29,by decide⟩
def hi1756b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨30,by decide⟩
def hi1756 : CheckedMoment :=
  CheckedMoment.ofBessel hi1756b1 hi1756b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1756 : meanBracketCheck (4339/5000) lo1756 hi1756=true := by decide +kernel
def bracket1756 : MeanBracket := meanBracketOfMoments (4339/5000) lo1756 hi1756 accepted1756
def lo1757b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨34,by decide⟩
def lo1757b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨35,by decide⟩
def lo1757 : CheckedMoment :=
  CheckedMoment.ofBessel lo1757b1 lo1757b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1757b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨39,by decide⟩
def hi1757b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨40,by decide⟩
def hi1757 : CheckedMoment :=
  CheckedMoment.ofBessel hi1757b1 hi1757b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1757 : meanBracketCheck (8679/10000) lo1757 hi1757=true := by decide +kernel
def bracket1757 : MeanBracket := meanBracketOfMoments (8679/10000) lo1757 hi1757 accepted1757
def lo1758b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨44,by decide⟩
def lo1758b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨45,by decide⟩
def lo1758 : CheckedMoment :=
  CheckedMoment.ofBessel lo1758b1 lo1758b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1758b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨49,by decide⟩
def hi1758b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨50,by decide⟩
def hi1758 : CheckedMoment :=
  CheckedMoment.ofBessel hi1758b1 hi1758b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1758 : meanBracketCheck (217/250) lo1758 hi1758=true := by decide +kernel
def bracket1758 : MeanBracket := meanBracketOfMoments (217/250) lo1758 hi1758 accepted1758
def lo1759b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨54,by decide⟩
def lo1759b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨55,by decide⟩
def lo1759 : CheckedMoment :=
  CheckedMoment.ofBessel lo1759b1 lo1759b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1759b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨59,by decide⟩
def hi1759b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨60,by decide⟩
def hi1759 : CheckedMoment :=
  CheckedMoment.ofBessel hi1759b1 hi1759b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1759 : meanBracketCheck (8681/10000) lo1759 hi1759=true := by decide +kernel
def bracket1759 : MeanBracket := meanBracketOfMoments (8681/10000) lo1759 hi1759 accepted1759
#print axioms bracket1744
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0109
