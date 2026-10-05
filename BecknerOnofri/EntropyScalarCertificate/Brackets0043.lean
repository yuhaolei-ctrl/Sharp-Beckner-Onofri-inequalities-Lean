module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0107
public import BecknerOnofri.EntropyScalarCertificate.Bessel0108
public import BecknerOnofri.EntropyScalarCertificate.Bessel0109

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0043
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0688b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨32,by decide⟩
def lo0688b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨33,by decide⟩
def lo0688 : CheckedMoment :=
  CheckedMoment.ofBessel lo0688b1 lo0688b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0688b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨37,by decide⟩
def hi0688b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨38,by decide⟩
def hi0688 : CheckedMoment :=
  CheckedMoment.ofBessel hi0688b1 hi0688b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0688 : meanBracketCheck (1941/10000) lo0688 hi0688=true := by decide +kernel
def bracket0688 : MeanBracket := meanBracketOfMoments (1941/10000) lo0688 hi0688 accepted0688
def lo0689b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨42,by decide⟩
def lo0689b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨43,by decide⟩
def lo0689 : CheckedMoment :=
  CheckedMoment.ofBessel lo0689b1 lo0689b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0689b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨47,by decide⟩
def hi0689b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨48,by decide⟩
def hi0689 : CheckedMoment :=
  CheckedMoment.ofBessel hi0689b1 hi0689b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0689 : meanBracketCheck (1943/10000) lo0689 hi0689=true := by decide +kernel
def bracket0689 : MeanBracket := meanBracketOfMoments (1943/10000) lo0689 hi0689 accepted0689
def lo0690b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨52,by decide⟩
def lo0690b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨53,by decide⟩
def lo0690 : CheckedMoment :=
  CheckedMoment.ofBessel lo0690b1 lo0690b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0690b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨57,by decide⟩
def hi0690b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨58,by decide⟩
def hi0690 : CheckedMoment :=
  CheckedMoment.ofBessel hi0690b1 hi0690b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0690 : meanBracketCheck (389/2000) lo0690 hi0690=true := by decide +kernel
def bracket0690 : MeanBracket := meanBracketOfMoments (389/2000) lo0690 hi0690 accepted0690
def lo0691b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨62,by decide⟩
def lo0691b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨63,by decide⟩
def lo0691 : CheckedMoment :=
  CheckedMoment.ofBessel lo0691b1 lo0691b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0691b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨3,by decide⟩
def hi0691b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨4,by decide⟩
def hi0691 : CheckedMoment :=
  CheckedMoment.ofBessel hi0691b1 hi0691b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0691 : meanBracketCheck (1947/10000) lo0691 hi0691=true := by decide +kernel
def bracket0691 : MeanBracket := meanBracketOfMoments (1947/10000) lo0691 hi0691 accepted0691
def lo0692b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨8,by decide⟩
def lo0692b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨9,by decide⟩
def lo0692 : CheckedMoment :=
  CheckedMoment.ofBessel lo0692b1 lo0692b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0692b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨13,by decide⟩
def hi0692b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨14,by decide⟩
def hi0692 : CheckedMoment :=
  CheckedMoment.ofBessel hi0692b1 hi0692b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0692 : meanBracketCheck (1949/10000) lo0692 hi0692=true := by decide +kernel
def bracket0692 : MeanBracket := meanBracketOfMoments (1949/10000) lo0692 hi0692 accepted0692
def lo0693b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨18,by decide⟩
def lo0693b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨19,by decide⟩
def lo0693 : CheckedMoment :=
  CheckedMoment.ofBessel lo0693b1 lo0693b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0693b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨23,by decide⟩
def hi0693b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨24,by decide⟩
def hi0693 : CheckedMoment :=
  CheckedMoment.ofBessel hi0693b1 hi0693b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0693 : meanBracketCheck (1951/10000) lo0693 hi0693=true := by decide +kernel
def bracket0693 : MeanBracket := meanBracketOfMoments (1951/10000) lo0693 hi0693 accepted0693
def lo0694b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨28,by decide⟩
def lo0694b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨29,by decide⟩
def lo0694 : CheckedMoment :=
  CheckedMoment.ofBessel lo0694b1 lo0694b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0694b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨33,by decide⟩
def hi0694b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨34,by decide⟩
def hi0694 : CheckedMoment :=
  CheckedMoment.ofBessel hi0694b1 hi0694b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0694 : meanBracketCheck (1953/10000) lo0694 hi0694=true := by decide +kernel
def bracket0694 : MeanBracket := meanBracketOfMoments (1953/10000) lo0694 hi0694 accepted0694
def lo0695b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨38,by decide⟩
def lo0695b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨39,by decide⟩
def lo0695 : CheckedMoment :=
  CheckedMoment.ofBessel lo0695b1 lo0695b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0695b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨43,by decide⟩
def hi0695b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨44,by decide⟩
def hi0695 : CheckedMoment :=
  CheckedMoment.ofBessel hi0695b1 hi0695b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0695 : meanBracketCheck (391/2000) lo0695 hi0695=true := by decide +kernel
def bracket0695 : MeanBracket := meanBracketOfMoments (391/2000) lo0695 hi0695 accepted0695
def lo0696b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨48,by decide⟩
def lo0696b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨49,by decide⟩
def lo0696 : CheckedMoment :=
  CheckedMoment.ofBessel lo0696b1 lo0696b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0696b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨53,by decide⟩
def hi0696b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨54,by decide⟩
def hi0696 : CheckedMoment :=
  CheckedMoment.ofBessel hi0696b1 hi0696b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0696 : meanBracketCheck (1957/10000) lo0696 hi0696=true := by decide +kernel
def bracket0696 : MeanBracket := meanBracketOfMoments (1957/10000) lo0696 hi0696 accepted0696
def lo0697b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨58,by decide⟩
def lo0697b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨59,by decide⟩
def lo0697 : CheckedMoment :=
  CheckedMoment.ofBessel lo0697b1 lo0697b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0697b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨63,by decide⟩
def hi0697b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨0,by decide⟩
def hi0697 : CheckedMoment :=
  CheckedMoment.ofBessel hi0697b1 hi0697b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0697 : meanBracketCheck (1959/10000) lo0697 hi0697=true := by decide +kernel
def bracket0697 : MeanBracket := meanBracketOfMoments (1959/10000) lo0697 hi0697 accepted0697
def lo0698b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨4,by decide⟩
def lo0698b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨5,by decide⟩
def lo0698 : CheckedMoment :=
  CheckedMoment.ofBessel lo0698b1 lo0698b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0698b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨9,by decide⟩
def hi0698b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨10,by decide⟩
def hi0698 : CheckedMoment :=
  CheckedMoment.ofBessel hi0698b1 hi0698b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0698 : meanBracketCheck (1961/10000) lo0698 hi0698=true := by decide +kernel
def bracket0698 : MeanBracket := meanBracketOfMoments (1961/10000) lo0698 hi0698 accepted0698
def lo0699b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨14,by decide⟩
def lo0699b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨15,by decide⟩
def lo0699 : CheckedMoment :=
  CheckedMoment.ofBessel lo0699b1 lo0699b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0699b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨19,by decide⟩
def hi0699b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨20,by decide⟩
def hi0699 : CheckedMoment :=
  CheckedMoment.ofBessel hi0699b1 hi0699b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0699 : meanBracketCheck (1963/10000) lo0699 hi0699=true := by decide +kernel
def bracket0699 : MeanBracket := meanBracketOfMoments (1963/10000) lo0699 hi0699 accepted0699
def lo0700b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨24,by decide⟩
def lo0700b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨25,by decide⟩
def lo0700 : CheckedMoment :=
  CheckedMoment.ofBessel lo0700b1 lo0700b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0700b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨29,by decide⟩
def hi0700b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨30,by decide⟩
def hi0700 : CheckedMoment :=
  CheckedMoment.ofBessel hi0700b1 hi0700b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0700 : meanBracketCheck (393/2000) lo0700 hi0700=true := by decide +kernel
def bracket0700 : MeanBracket := meanBracketOfMoments (393/2000) lo0700 hi0700 accepted0700
def lo0701b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨34,by decide⟩
def lo0701b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨35,by decide⟩
def lo0701 : CheckedMoment :=
  CheckedMoment.ofBessel lo0701b1 lo0701b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0701b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨39,by decide⟩
def hi0701b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨40,by decide⟩
def hi0701 : CheckedMoment :=
  CheckedMoment.ofBessel hi0701b1 hi0701b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0701 : meanBracketCheck (1967/10000) lo0701 hi0701=true := by decide +kernel
def bracket0701 : MeanBracket := meanBracketOfMoments (1967/10000) lo0701 hi0701 accepted0701
def lo0702b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨44,by decide⟩
def lo0702b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨45,by decide⟩
def lo0702 : CheckedMoment :=
  CheckedMoment.ofBessel lo0702b1 lo0702b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0702b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨49,by decide⟩
def hi0702b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨50,by decide⟩
def hi0702 : CheckedMoment :=
  CheckedMoment.ofBessel hi0702b1 hi0702b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0702 : meanBracketCheck (1969/10000) lo0702 hi0702=true := by decide +kernel
def bracket0702 : MeanBracket := meanBracketOfMoments (1969/10000) lo0702 hi0702 accepted0702
def lo0703b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨54,by decide⟩
def lo0703b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨55,by decide⟩
def lo0703 : CheckedMoment :=
  CheckedMoment.ofBessel lo0703b1 lo0703b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0703b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨59,by decide⟩
def hi0703b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨60,by decide⟩
def hi0703 : CheckedMoment :=
  CheckedMoment.ofBessel hi0703b1 hi0703b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0703 : meanBracketCheck (1971/10000) lo0703 hi0703=true := by decide +kernel
def bracket0703 : MeanBracket := meanBracketOfMoments (1971/10000) lo0703 hi0703 accepted0703
#print axioms bracket0688
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0043
