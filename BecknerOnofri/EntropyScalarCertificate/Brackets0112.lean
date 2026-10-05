module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0280
public import BecknerOnofri.EntropyScalarCertificate.Bessel0281
public import BecknerOnofri.EntropyScalarCertificate.Bessel0282

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0112
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1792b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨0,by decide⟩
def lo1792b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨1,by decide⟩
def lo1792 : CheckedMoment :=
  CheckedMoment.ofBessel lo1792b1 lo1792b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1792b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨5,by decide⟩
def hi1792b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨6,by decide⟩
def hi1792 : CheckedMoment :=
  CheckedMoment.ofBessel hi1792b1 hi1792b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1792 : meanBracketCheck (4357/5000) lo1792 hi1792=true := by decide +kernel
def bracket1792 : MeanBracket := meanBracketOfMoments (4357/5000) lo1792 hi1792 accepted1792
def lo1793b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨10,by decide⟩
def lo1793b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨11,by decide⟩
def lo1793 : CheckedMoment :=
  CheckedMoment.ofBessel lo1793b1 lo1793b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1793b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨15,by decide⟩
def hi1793b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨16,by decide⟩
def hi1793 : CheckedMoment :=
  CheckedMoment.ofBessel hi1793b1 hi1793b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1793 : meanBracketCheck (1743/2000) lo1793 hi1793=true := by decide +kernel
def bracket1793 : MeanBracket := meanBracketOfMoments (1743/2000) lo1793 hi1793 accepted1793
def lo1794b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨20,by decide⟩
def lo1794b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨21,by decide⟩
def lo1794 : CheckedMoment :=
  CheckedMoment.ofBessel lo1794b1 lo1794b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1794b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨25,by decide⟩
def hi1794b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨26,by decide⟩
def hi1794 : CheckedMoment :=
  CheckedMoment.ofBessel hi1794b1 hi1794b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1794 : meanBracketCheck (2179/2500) lo1794 hi1794=true := by decide +kernel
def bracket1794 : MeanBracket := meanBracketOfMoments (2179/2500) lo1794 hi1794 accepted1794
def lo1795b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨30,by decide⟩
def lo1795b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨31,by decide⟩
def lo1795 : CheckedMoment :=
  CheckedMoment.ofBessel lo1795b1 lo1795b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1795b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨35,by decide⟩
def hi1795b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨36,by decide⟩
def hi1795 : CheckedMoment :=
  CheckedMoment.ofBessel hi1795b1 hi1795b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1795 : meanBracketCheck (8717/10000) lo1795 hi1795=true := by decide +kernel
def bracket1795 : MeanBracket := meanBracketOfMoments (8717/10000) lo1795 hi1795 accepted1795
def lo1796b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨40,by decide⟩
def lo1796b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨41,by decide⟩
def lo1796 : CheckedMoment :=
  CheckedMoment.ofBessel lo1796b1 lo1796b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1796b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨45,by decide⟩
def hi1796b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨46,by decide⟩
def hi1796 : CheckedMoment :=
  CheckedMoment.ofBessel hi1796b1 hi1796b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1796 : meanBracketCheck (4359/5000) lo1796 hi1796=true := by decide +kernel
def bracket1796 : MeanBracket := meanBracketOfMoments (4359/5000) lo1796 hi1796 accepted1796
def lo1797b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨50,by decide⟩
def lo1797b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨51,by decide⟩
def lo1797 : CheckedMoment :=
  CheckedMoment.ofBessel lo1797b1 lo1797b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1797b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨55,by decide⟩
def hi1797b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨56,by decide⟩
def hi1797 : CheckedMoment :=
  CheckedMoment.ofBessel hi1797b1 hi1797b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1797 : meanBracketCheck (8719/10000) lo1797 hi1797=true := by decide +kernel
def bracket1797 : MeanBracket := meanBracketOfMoments (8719/10000) lo1797 hi1797 accepted1797
def lo1798b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨60,by decide⟩
def lo1798b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨61,by decide⟩
def lo1798 : CheckedMoment :=
  CheckedMoment.ofBessel lo1798b1 lo1798b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1798b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨1,by decide⟩
def hi1798b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨2,by decide⟩
def hi1798 : CheckedMoment :=
  CheckedMoment.ofBessel hi1798b1 hi1798b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1798 : meanBracketCheck (109/125) lo1798 hi1798=true := by decide +kernel
def bracket1798 : MeanBracket := meanBracketOfMoments (109/125) lo1798 hi1798 accepted1798
def lo1799b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨6,by decide⟩
def lo1799b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨7,by decide⟩
def lo1799 : CheckedMoment :=
  CheckedMoment.ofBessel lo1799b1 lo1799b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1799b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨11,by decide⟩
def hi1799b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨12,by decide⟩
def hi1799 : CheckedMoment :=
  CheckedMoment.ofBessel hi1799b1 hi1799b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1799 : meanBracketCheck (8721/10000) lo1799 hi1799=true := by decide +kernel
def bracket1799 : MeanBracket := meanBracketOfMoments (8721/10000) lo1799 hi1799 accepted1799
def lo1800b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨16,by decide⟩
def lo1800b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨17,by decide⟩
def lo1800 : CheckedMoment :=
  CheckedMoment.ofBessel lo1800b1 lo1800b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1800b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨21,by decide⟩
def hi1800b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨22,by decide⟩
def hi1800 : CheckedMoment :=
  CheckedMoment.ofBessel hi1800b1 hi1800b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1800 : meanBracketCheck (4361/5000) lo1800 hi1800=true := by decide +kernel
def bracket1800 : MeanBracket := meanBracketOfMoments (4361/5000) lo1800 hi1800 accepted1800
def lo1801b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨26,by decide⟩
def lo1801b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨27,by decide⟩
def lo1801 : CheckedMoment :=
  CheckedMoment.ofBessel lo1801b1 lo1801b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1801b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨31,by decide⟩
def hi1801b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨32,by decide⟩
def hi1801 : CheckedMoment :=
  CheckedMoment.ofBessel hi1801b1 hi1801b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1801 : meanBracketCheck (8723/10000) lo1801 hi1801=true := by decide +kernel
def bracket1801 : MeanBracket := meanBracketOfMoments (8723/10000) lo1801 hi1801 accepted1801
def lo1802b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨36,by decide⟩
def lo1802b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨37,by decide⟩
def lo1802 : CheckedMoment :=
  CheckedMoment.ofBessel lo1802b1 lo1802b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1802b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨41,by decide⟩
def hi1802b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨42,by decide⟩
def hi1802 : CheckedMoment :=
  CheckedMoment.ofBessel hi1802b1 hi1802b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1802 : meanBracketCheck (2181/2500) lo1802 hi1802=true := by decide +kernel
def bracket1802 : MeanBracket := meanBracketOfMoments (2181/2500) lo1802 hi1802 accepted1802
def lo1803b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨46,by decide⟩
def lo1803b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨47,by decide⟩
def lo1803 : CheckedMoment :=
  CheckedMoment.ofBessel lo1803b1 lo1803b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1803b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨51,by decide⟩
def hi1803b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨52,by decide⟩
def hi1803 : CheckedMoment :=
  CheckedMoment.ofBessel hi1803b1 hi1803b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1803 : meanBracketCheck (349/400) lo1803 hi1803=true := by decide +kernel
def bracket1803 : MeanBracket := meanBracketOfMoments (349/400) lo1803 hi1803 accepted1803
def lo1804b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨56,by decide⟩
def lo1804b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨57,by decide⟩
def lo1804 : CheckedMoment :=
  CheckedMoment.ofBessel lo1804b1 lo1804b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1804b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨61,by decide⟩
def hi1804b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨62,by decide⟩
def hi1804 : CheckedMoment :=
  CheckedMoment.ofBessel hi1804b1 hi1804b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1804 : meanBracketCheck (4363/5000) lo1804 hi1804=true := by decide +kernel
def bracket1804 : MeanBracket := meanBracketOfMoments (4363/5000) lo1804 hi1804 accepted1804
def lo1805b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨2,by decide⟩
def lo1805b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨3,by decide⟩
def lo1805 : CheckedMoment :=
  CheckedMoment.ofBessel lo1805b1 lo1805b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1805b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨7,by decide⟩
def hi1805b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨8,by decide⟩
def hi1805 : CheckedMoment :=
  CheckedMoment.ofBessel hi1805b1 hi1805b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1805 : meanBracketCheck (8727/10000) lo1805 hi1805=true := by decide +kernel
def bracket1805 : MeanBracket := meanBracketOfMoments (8727/10000) lo1805 hi1805 accepted1805
def lo1806b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨12,by decide⟩
def lo1806b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨13,by decide⟩
def lo1806 : CheckedMoment :=
  CheckedMoment.ofBessel lo1806b1 lo1806b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1806b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨17,by decide⟩
def hi1806b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨18,by decide⟩
def hi1806 : CheckedMoment :=
  CheckedMoment.ofBessel hi1806b1 hi1806b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1806 : meanBracketCheck (1091/1250) lo1806 hi1806=true := by decide +kernel
def bracket1806 : MeanBracket := meanBracketOfMoments (1091/1250) lo1806 hi1806 accepted1806
def lo1807b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨22,by decide⟩
def lo1807b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨23,by decide⟩
def lo1807 : CheckedMoment :=
  CheckedMoment.ofBessel lo1807b1 lo1807b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1807b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨27,by decide⟩
def hi1807b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨28,by decide⟩
def hi1807 : CheckedMoment :=
  CheckedMoment.ofBessel hi1807b1 hi1807b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1807 : meanBracketCheck (8729/10000) lo1807 hi1807=true := by decide +kernel
def bracket1807 : MeanBracket := meanBracketOfMoments (8729/10000) lo1807 hi1807 accepted1807
#print axioms bracket1792
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0112
