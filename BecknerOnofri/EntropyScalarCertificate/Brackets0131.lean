module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0327
public import BecknerOnofri.EntropyScalarCertificate.Bessel0328
public import BecknerOnofri.EntropyScalarCertificate.Bessel0329

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0131
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2096b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨32,by decide⟩
def lo2096b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨33,by decide⟩
def lo2096 : CheckedMoment :=
  CheckedMoment.ofBessel lo2096b1 lo2096b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2096b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨37,by decide⟩
def hi2096b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨38,by decide⟩
def hi2096 : CheckedMoment :=
  CheckedMoment.ofBessel hi2096b1 hi2096b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2096 : meanBracketCheck (4809/5000) lo2096 hi2096=true := by decide +kernel
def bracket2096 : MeanBracket := meanBracketOfMoments (4809/5000) lo2096 hi2096 accepted2096
def lo2097b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨42,by decide⟩
def lo2097b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨43,by decide⟩
def lo2097 : CheckedMoment :=
  CheckedMoment.ofBessel lo2097b1 lo2097b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2097b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨47,by decide⟩
def hi2097b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨48,by decide⟩
def hi2097 : CheckedMoment :=
  CheckedMoment.ofBessel hi2097b1 hi2097b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2097 : meanBracketCheck (9619/10000) lo2097 hi2097=true := by decide +kernel
def bracket2097 : MeanBracket := meanBracketOfMoments (9619/10000) lo2097 hi2097 accepted2097
def lo2098b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨52,by decide⟩
def lo2098b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨53,by decide⟩
def lo2098 : CheckedMoment :=
  CheckedMoment.ofBessel lo2098b1 lo2098b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2098b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨57,by decide⟩
def hi2098b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨58,by decide⟩
def hi2098 : CheckedMoment :=
  CheckedMoment.ofBessel hi2098b1 hi2098b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2098 : meanBracketCheck (481/500) lo2098 hi2098=true := by decide +kernel
def bracket2098 : MeanBracket := meanBracketOfMoments (481/500) lo2098 hi2098 accepted2098
def lo2099b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨62,by decide⟩
def lo2099b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨63,by decide⟩
def lo2099 : CheckedMoment :=
  CheckedMoment.ofBessel lo2099b1 lo2099b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2099b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨3,by decide⟩
def hi2099b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨4,by decide⟩
def hi2099 : CheckedMoment :=
  CheckedMoment.ofBessel hi2099b1 hi2099b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2099 : meanBracketCheck (9621/10000) lo2099 hi2099=true := by decide +kernel
def bracket2099 : MeanBracket := meanBracketOfMoments (9621/10000) lo2099 hi2099 accepted2099
def lo2100b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨8,by decide⟩
def lo2100b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨9,by decide⟩
def lo2100 : CheckedMoment :=
  CheckedMoment.ofBessel lo2100b1 lo2100b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2100b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨13,by decide⟩
def hi2100b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨14,by decide⟩
def hi2100 : CheckedMoment :=
  CheckedMoment.ofBessel hi2100b1 hi2100b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2100 : meanBracketCheck (4811/5000) lo2100 hi2100=true := by decide +kernel
def bracket2100 : MeanBracket := meanBracketOfMoments (4811/5000) lo2100 hi2100 accepted2100
def lo2101b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨18,by decide⟩
def lo2101b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨19,by decide⟩
def lo2101 : CheckedMoment :=
  CheckedMoment.ofBessel lo2101b1 lo2101b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2101b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨23,by decide⟩
def hi2101b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨24,by decide⟩
def hi2101 : CheckedMoment :=
  CheckedMoment.ofBessel hi2101b1 hi2101b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2101 : meanBracketCheck (9623/10000) lo2101 hi2101=true := by decide +kernel
def bracket2101 : MeanBracket := meanBracketOfMoments (9623/10000) lo2101 hi2101 accepted2101
def lo2102b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨28,by decide⟩
def lo2102b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨29,by decide⟩
def lo2102 : CheckedMoment :=
  CheckedMoment.ofBessel lo2102b1 lo2102b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2102b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨33,by decide⟩
def hi2102b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨34,by decide⟩
def hi2102 : CheckedMoment :=
  CheckedMoment.ofBessel hi2102b1 hi2102b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2102 : meanBracketCheck (1203/1250) lo2102 hi2102=true := by decide +kernel
def bracket2102 : MeanBracket := meanBracketOfMoments (1203/1250) lo2102 hi2102 accepted2102
def lo2103b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨38,by decide⟩
def lo2103b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨39,by decide⟩
def lo2103 : CheckedMoment :=
  CheckedMoment.ofBessel lo2103b1 lo2103b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2103b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨43,by decide⟩
def hi2103b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨44,by decide⟩
def hi2103 : CheckedMoment :=
  CheckedMoment.ofBessel hi2103b1 hi2103b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2103 : meanBracketCheck (77/80) lo2103 hi2103=true := by decide +kernel
def bracket2103 : MeanBracket := meanBracketOfMoments (77/80) lo2103 hi2103 accepted2103
def lo2104b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨48,by decide⟩
def lo2104b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨49,by decide⟩
def lo2104 : CheckedMoment :=
  CheckedMoment.ofBessel lo2104b1 lo2104b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2104b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨53,by decide⟩
def hi2104b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨54,by decide⟩
def hi2104 : CheckedMoment :=
  CheckedMoment.ofBessel hi2104b1 hi2104b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2104 : meanBracketCheck (4813/5000) lo2104 hi2104=true := by decide +kernel
def bracket2104 : MeanBracket := meanBracketOfMoments (4813/5000) lo2104 hi2104 accepted2104
def lo2105b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨58,by decide⟩
def lo2105b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨59,by decide⟩
def lo2105 : CheckedMoment :=
  CheckedMoment.ofBessel lo2105b1 lo2105b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2105b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨63,by decide⟩
def hi2105b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨0,by decide⟩
def hi2105 : CheckedMoment :=
  CheckedMoment.ofBessel hi2105b1 hi2105b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2105 : meanBracketCheck (9627/10000) lo2105 hi2105=true := by decide +kernel
def bracket2105 : MeanBracket := meanBracketOfMoments (9627/10000) lo2105 hi2105 accepted2105
def lo2106b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨4,by decide⟩
def lo2106b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨5,by decide⟩
def lo2106 : CheckedMoment :=
  CheckedMoment.ofBessel lo2106b1 lo2106b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2106b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨9,by decide⟩
def hi2106b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨10,by decide⟩
def hi2106 : CheckedMoment :=
  CheckedMoment.ofBessel hi2106b1 hi2106b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2106 : meanBracketCheck (2407/2500) lo2106 hi2106=true := by decide +kernel
def bracket2106 : MeanBracket := meanBracketOfMoments (2407/2500) lo2106 hi2106 accepted2106
def lo2107b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨14,by decide⟩
def lo2107b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨15,by decide⟩
def lo2107 : CheckedMoment :=
  CheckedMoment.ofBessel lo2107b1 lo2107b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2107b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨19,by decide⟩
def hi2107b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨20,by decide⟩
def hi2107 : CheckedMoment :=
  CheckedMoment.ofBessel hi2107b1 hi2107b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2107 : meanBracketCheck (9629/10000) lo2107 hi2107=true := by decide +kernel
def bracket2107 : MeanBracket := meanBracketOfMoments (9629/10000) lo2107 hi2107 accepted2107
def lo2108b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨24,by decide⟩
def lo2108b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨25,by decide⟩
def lo2108 : CheckedMoment :=
  CheckedMoment.ofBessel lo2108b1 lo2108b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2108b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨29,by decide⟩
def hi2108b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨30,by decide⟩
def hi2108 : CheckedMoment :=
  CheckedMoment.ofBessel hi2108b1 hi2108b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2108 : meanBracketCheck (963/1000) lo2108 hi2108=true := by decide +kernel
def bracket2108 : MeanBracket := meanBracketOfMoments (963/1000) lo2108 hi2108 accepted2108
def lo2109b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨34,by decide⟩
def lo2109b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨35,by decide⟩
def lo2109 : CheckedMoment :=
  CheckedMoment.ofBessel lo2109b1 lo2109b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2109b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨39,by decide⟩
def hi2109b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨40,by decide⟩
def hi2109 : CheckedMoment :=
  CheckedMoment.ofBessel hi2109b1 hi2109b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2109 : meanBracketCheck (9631/10000) lo2109 hi2109=true := by decide +kernel
def bracket2109 : MeanBracket := meanBracketOfMoments (9631/10000) lo2109 hi2109 accepted2109
def lo2110b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨44,by decide⟩
def lo2110b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨45,by decide⟩
def lo2110 : CheckedMoment :=
  CheckedMoment.ofBessel lo2110b1 lo2110b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2110b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨49,by decide⟩
def hi2110b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨50,by decide⟩
def hi2110 : CheckedMoment :=
  CheckedMoment.ofBessel hi2110b1 hi2110b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2110 : meanBracketCheck (602/625) lo2110 hi2110=true := by decide +kernel
def bracket2110 : MeanBracket := meanBracketOfMoments (602/625) lo2110 hi2110 accepted2110
def lo2111b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨54,by decide⟩
def lo2111b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨55,by decide⟩
def lo2111 : CheckedMoment :=
  CheckedMoment.ofBessel lo2111b1 lo2111b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2111b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨59,by decide⟩
def hi2111b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨60,by decide⟩
def hi2111 : CheckedMoment :=
  CheckedMoment.ofBessel hi2111b1 hi2111b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2111 : meanBracketCheck (9633/10000) lo2111 hi2111=true := by decide +kernel
def bracket2111 : MeanBracket := meanBracketOfMoments (9633/10000) lo2111 hi2111 accepted2111
#print axioms bracket2096
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0131
