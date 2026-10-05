module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0452
public import BecknerOnofri.EntropyScalarCertificate.Bessel0453
public import BecknerOnofri.EntropyScalarCertificate.Bessel0454

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0181
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2896b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨32,by decide⟩
def lo2896b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨33,by decide⟩
def lo2896 : CheckedMoment :=
  CheckedMoment.ofBessel lo2896b1 lo2896b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2896b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨37,by decide⟩
def hi2896b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨38,by decide⟩
def hi2896 : CheckedMoment :=
  CheckedMoment.ofBessel hi2896b1 hi2896b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2896 : meanBracketCheck (12473/12500) lo2896 hi2896=true := by decide +kernel
def bracket2896 : MeanBracket := meanBracketOfMoments (12473/12500) lo2896 hi2896 accepted2896
def lo2897b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨42,by decide⟩
def lo2897b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨43,by decide⟩
def lo2897 : CheckedMoment :=
  CheckedMoment.ofBessel lo2897b1 lo2897b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2897b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨47,by decide⟩
def hi2897b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨48,by decide⟩
def hi2897 : CheckedMoment :=
  CheckedMoment.ofBessel hi2897b1 hi2897b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2897 : meanBracketCheck (199569/200000) lo2897 hi2897=true := by decide +kernel
def bracket2897 : MeanBracket := meanBracketOfMoments (199569/200000) lo2897 hi2897 accepted2897
def lo2898b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨52,by decide⟩
def lo2898b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨53,by decide⟩
def lo2898 : CheckedMoment :=
  CheckedMoment.ofBessel lo2898b1 lo2898b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2898b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨57,by decide⟩
def hi2898b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨58,by decide⟩
def hi2898 : CheckedMoment :=
  CheckedMoment.ofBessel hi2898b1 hi2898b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2898 : meanBracketCheck (19957/20000) lo2898 hi2898=true := by decide +kernel
def bracket2898 : MeanBracket := meanBracketOfMoments (19957/20000) lo2898 hi2898 accepted2898
def lo2899b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨62,by decide⟩
def lo2899b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨63,by decide⟩
def lo2899 : CheckedMoment :=
  CheckedMoment.ofBessel lo2899b1 lo2899b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2899b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨3,by decide⟩
def hi2899b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨4,by decide⟩
def hi2899 : CheckedMoment :=
  CheckedMoment.ofBessel hi2899b1 hi2899b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2899 : meanBracketCheck (199571/200000) lo2899 hi2899=true := by decide +kernel
def bracket2899 : MeanBracket := meanBracketOfMoments (199571/200000) lo2899 hi2899 accepted2899
def lo2900b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨8,by decide⟩
def lo2900b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨9,by decide⟩
def lo2900 : CheckedMoment :=
  CheckedMoment.ofBessel lo2900b1 lo2900b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2900b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨13,by decide⟩
def hi2900b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨14,by decide⟩
def hi2900 : CheckedMoment :=
  CheckedMoment.ofBessel hi2900b1 hi2900b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2900 : meanBracketCheck (49893/50000) lo2900 hi2900=true := by decide +kernel
def bracket2900 : MeanBracket := meanBracketOfMoments (49893/50000) lo2900 hi2900 accepted2900
def lo2901b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨18,by decide⟩
def lo2901b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨19,by decide⟩
def lo2901 : CheckedMoment :=
  CheckedMoment.ofBessel lo2901b1 lo2901b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2901b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨23,by decide⟩
def hi2901b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨24,by decide⟩
def hi2901 : CheckedMoment :=
  CheckedMoment.ofBessel hi2901b1 hi2901b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2901 : meanBracketCheck (199573/200000) lo2901 hi2901=true := by decide +kernel
def bracket2901 : MeanBracket := meanBracketOfMoments (199573/200000) lo2901 hi2901 accepted2901
def lo2902b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨28,by decide⟩
def lo2902b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨29,by decide⟩
def lo2902 : CheckedMoment :=
  CheckedMoment.ofBessel lo2902b1 lo2902b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2902b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨33,by decide⟩
def hi2902b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨34,by decide⟩
def hi2902 : CheckedMoment :=
  CheckedMoment.ofBessel hi2902b1 hi2902b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2902 : meanBracketCheck (99787/100000) lo2902 hi2902=true := by decide +kernel
def bracket2902 : MeanBracket := meanBracketOfMoments (99787/100000) lo2902 hi2902 accepted2902
def lo2903b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨38,by decide⟩
def lo2903b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨39,by decide⟩
def lo2903 : CheckedMoment :=
  CheckedMoment.ofBessel lo2903b1 lo2903b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2903b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨43,by decide⟩
def hi2903b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨44,by decide⟩
def hi2903 : CheckedMoment :=
  CheckedMoment.ofBessel hi2903b1 hi2903b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2903 : meanBracketCheck (7983/8000) lo2903 hi2903=true := by decide +kernel
def bracket2903 : MeanBracket := meanBracketOfMoments (7983/8000) lo2903 hi2903 accepted2903
def lo2904b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨48,by decide⟩
def lo2904b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨49,by decide⟩
def lo2904 : CheckedMoment :=
  CheckedMoment.ofBessel lo2904b1 lo2904b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2904b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨53,by decide⟩
def hi2904b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨54,by decide⟩
def hi2904 : CheckedMoment :=
  CheckedMoment.ofBessel hi2904b1 hi2904b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2904 : meanBracketCheck (24947/25000) lo2904 hi2904=true := by decide +kernel
def bracket2904 : MeanBracket := meanBracketOfMoments (24947/25000) lo2904 hi2904 accepted2904
def lo2905b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨58,by decide⟩
def lo2905b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨59,by decide⟩
def lo2905 : CheckedMoment :=
  CheckedMoment.ofBessel lo2905b1 lo2905b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2905b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨63,by decide⟩
def hi2905b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨0,by decide⟩
def hi2905 : CheckedMoment :=
  CheckedMoment.ofBessel hi2905b1 hi2905b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2905 : meanBracketCheck (199577/200000) lo2905 hi2905=true := by decide +kernel
def bracket2905 : MeanBracket := meanBracketOfMoments (199577/200000) lo2905 hi2905 accepted2905
def lo2906b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨4,by decide⟩
def lo2906b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨5,by decide⟩
def lo2906 : CheckedMoment :=
  CheckedMoment.ofBessel lo2906b1 lo2906b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2906b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨9,by decide⟩
def hi2906b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨10,by decide⟩
def hi2906 : CheckedMoment :=
  CheckedMoment.ofBessel hi2906b1 hi2906b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2906 : meanBracketCheck (99789/100000) lo2906 hi2906=true := by decide +kernel
def bracket2906 : MeanBracket := meanBracketOfMoments (99789/100000) lo2906 hi2906 accepted2906
def lo2907b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨14,by decide⟩
def lo2907b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨15,by decide⟩
def lo2907 : CheckedMoment :=
  CheckedMoment.ofBessel lo2907b1 lo2907b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2907b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨19,by decide⟩
def hi2907b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨20,by decide⟩
def hi2907 : CheckedMoment :=
  CheckedMoment.ofBessel hi2907b1 hi2907b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2907 : meanBracketCheck (199579/200000) lo2907 hi2907=true := by decide +kernel
def bracket2907 : MeanBracket := meanBracketOfMoments (199579/200000) lo2907 hi2907 accepted2907
def lo2908b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨24,by decide⟩
def lo2908b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨25,by decide⟩
def lo2908 : CheckedMoment :=
  CheckedMoment.ofBessel lo2908b1 lo2908b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2908b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨29,by decide⟩
def hi2908b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨30,by decide⟩
def hi2908 : CheckedMoment :=
  CheckedMoment.ofBessel hi2908b1 hi2908b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2908 : meanBracketCheck (9979/10000) lo2908 hi2908=true := by decide +kernel
def bracket2908 : MeanBracket := meanBracketOfMoments (9979/10000) lo2908 hi2908 accepted2908
def lo2909b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨34,by decide⟩
def lo2909b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨35,by decide⟩
def lo2909 : CheckedMoment :=
  CheckedMoment.ofBessel lo2909b1 lo2909b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2909b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨39,by decide⟩
def hi2909b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨40,by decide⟩
def hi2909 : CheckedMoment :=
  CheckedMoment.ofBessel hi2909b1 hi2909b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2909 : meanBracketCheck (199581/200000) lo2909 hi2909=true := by decide +kernel
def bracket2909 : MeanBracket := meanBracketOfMoments (199581/200000) lo2909 hi2909 accepted2909
def lo2910b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨44,by decide⟩
def lo2910b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨45,by decide⟩
def lo2910 : CheckedMoment :=
  CheckedMoment.ofBessel lo2910b1 lo2910b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2910b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨49,by decide⟩
def hi2910b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨50,by decide⟩
def hi2910 : CheckedMoment :=
  CheckedMoment.ofBessel hi2910b1 hi2910b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2910 : meanBracketCheck (99791/100000) lo2910 hi2910=true := by decide +kernel
def bracket2910 : MeanBracket := meanBracketOfMoments (99791/100000) lo2910 hi2910 accepted2910
def lo2911b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨54,by decide⟩
def lo2911b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨55,by decide⟩
def lo2911 : CheckedMoment :=
  CheckedMoment.ofBessel lo2911b1 lo2911b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2911b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨59,by decide⟩
def hi2911b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨60,by decide⟩
def hi2911 : CheckedMoment :=
  CheckedMoment.ofBessel hi2911b1 hi2911b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2911 : meanBracketCheck (199583/200000) lo2911 hi2911=true := by decide +kernel
def bracket2911 : MeanBracket := meanBracketOfMoments (199583/200000) lo2911 hi2911 accepted2911
#print axioms bracket2896
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0181
