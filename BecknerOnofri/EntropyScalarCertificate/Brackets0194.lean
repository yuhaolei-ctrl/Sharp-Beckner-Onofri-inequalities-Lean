module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0485
public import BecknerOnofri.EntropyScalarCertificate.Bessel0486
public import BecknerOnofri.EntropyScalarCertificate.Bessel0487

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0194
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo3104b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨0,by decide⟩
def lo3104b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨1,by decide⟩
def lo3104 : CheckedMoment :=
  CheckedMoment.ofBessel lo3104b1 lo3104b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3104b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨5,by decide⟩
def hi3104b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨6,by decide⟩
def hi3104 : CheckedMoment :=
  CheckedMoment.ofBessel hi3104b1 hi3104b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3104 : meanBracketCheck (6243/6250) lo3104 hi3104=true := by decide +kernel
def bracket3104 : MeanBracket := meanBracketOfMoments (6243/6250) lo3104 hi3104 accepted3104
def lo3105b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨10,by decide⟩
def lo3105b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨11,by decide⟩
def lo3105 : CheckedMoment :=
  CheckedMoment.ofBessel lo3105b1 lo3105b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3105b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨15,by decide⟩
def hi3105b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨16,by decide⟩
def hi3105 : CheckedMoment :=
  CheckedMoment.ofBessel hi3105b1 hi3105b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3105 : meanBracketCheck (199777/200000) lo3105 hi3105=true := by decide +kernel
def bracket3105 : MeanBracket := meanBracketOfMoments (199777/200000) lo3105 hi3105 accepted3105
def lo3106b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨20,by decide⟩
def lo3106b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨21,by decide⟩
def lo3106 : CheckedMoment :=
  CheckedMoment.ofBessel lo3106b1 lo3106b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3106b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨25,by decide⟩
def hi3106b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨26,by decide⟩
def hi3106 : CheckedMoment :=
  CheckedMoment.ofBessel hi3106b1 hi3106b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3106 : meanBracketCheck (99889/100000) lo3106 hi3106=true := by decide +kernel
def bracket3106 : MeanBracket := meanBracketOfMoments (99889/100000) lo3106 hi3106 accepted3106
def lo3107b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨30,by decide⟩
def lo3107b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨31,by decide⟩
def lo3107 : CheckedMoment :=
  CheckedMoment.ofBessel lo3107b1 lo3107b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3107b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨35,by decide⟩
def hi3107b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨36,by decide⟩
def hi3107 : CheckedMoment :=
  CheckedMoment.ofBessel hi3107b1 hi3107b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3107 : meanBracketCheck (199779/200000) lo3107 hi3107=true := by decide +kernel
def bracket3107 : MeanBracket := meanBracketOfMoments (199779/200000) lo3107 hi3107 accepted3107
def lo3108b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨40,by decide⟩
def lo3108b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨41,by decide⟩
def lo3108 : CheckedMoment :=
  CheckedMoment.ofBessel lo3108b1 lo3108b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3108b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨45,by decide⟩
def hi3108b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨46,by decide⟩
def hi3108 : CheckedMoment :=
  CheckedMoment.ofBessel hi3108b1 hi3108b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3108 : meanBracketCheck (9989/10000) lo3108 hi3108=true := by decide +kernel
def bracket3108 : MeanBracket := meanBracketOfMoments (9989/10000) lo3108 hi3108 accepted3108
def lo3109b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨50,by decide⟩
def lo3109b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨51,by decide⟩
def lo3109 : CheckedMoment :=
  CheckedMoment.ofBessel lo3109b1 lo3109b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3109b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨55,by decide⟩
def hi3109b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨56,by decide⟩
def hi3109 : CheckedMoment :=
  CheckedMoment.ofBessel hi3109b1 hi3109b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3109 : meanBracketCheck (199781/200000) lo3109 hi3109=true := by decide +kernel
def bracket3109 : MeanBracket := meanBracketOfMoments (199781/200000) lo3109 hi3109 accepted3109
def lo3110b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨60,by decide⟩
def lo3110b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨61,by decide⟩
def lo3110 : CheckedMoment :=
  CheckedMoment.ofBessel lo3110b1 lo3110b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3110b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨1,by decide⟩
def hi3110b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨2,by decide⟩
def hi3110 : CheckedMoment :=
  CheckedMoment.ofBessel hi3110b1 hi3110b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3110 : meanBracketCheck (99891/100000) lo3110 hi3110=true := by decide +kernel
def bracket3110 : MeanBracket := meanBracketOfMoments (99891/100000) lo3110 hi3110 accepted3110
def lo3111b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨6,by decide⟩
def lo3111b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨7,by decide⟩
def lo3111 : CheckedMoment :=
  CheckedMoment.ofBessel lo3111b1 lo3111b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3111b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨11,by decide⟩
def hi3111b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨12,by decide⟩
def hi3111 : CheckedMoment :=
  CheckedMoment.ofBessel hi3111b1 hi3111b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3111 : meanBracketCheck (199783/200000) lo3111 hi3111=true := by decide +kernel
def bracket3111 : MeanBracket := meanBracketOfMoments (199783/200000) lo3111 hi3111 accepted3111
def lo3112b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨16,by decide⟩
def lo3112b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨17,by decide⟩
def lo3112 : CheckedMoment :=
  CheckedMoment.ofBessel lo3112b1 lo3112b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3112b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨21,by decide⟩
def hi3112b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨22,by decide⟩
def hi3112 : CheckedMoment :=
  CheckedMoment.ofBessel hi3112b1 hi3112b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3112 : meanBracketCheck (24973/25000) lo3112 hi3112=true := by decide +kernel
def bracket3112 : MeanBracket := meanBracketOfMoments (24973/25000) lo3112 hi3112 accepted3112
def lo3113b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨26,by decide⟩
def lo3113b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨27,by decide⟩
def lo3113 : CheckedMoment :=
  CheckedMoment.ofBessel lo3113b1 lo3113b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3113b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨31,by decide⟩
def hi3113b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨32,by decide⟩
def hi3113 : CheckedMoment :=
  CheckedMoment.ofBessel hi3113b1 hi3113b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3113 : meanBracketCheck (39957/40000) lo3113 hi3113=true := by decide +kernel
def bracket3113 : MeanBracket := meanBracketOfMoments (39957/40000) lo3113 hi3113 accepted3113
def lo3114b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨36,by decide⟩
def lo3114b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨37,by decide⟩
def lo3114 : CheckedMoment :=
  CheckedMoment.ofBessel lo3114b1 lo3114b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3114b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨41,by decide⟩
def hi3114b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨42,by decide⟩
def hi3114 : CheckedMoment :=
  CheckedMoment.ofBessel hi3114b1 hi3114b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3114 : meanBracketCheck (99893/100000) lo3114 hi3114=true := by decide +kernel
def bracket3114 : MeanBracket := meanBracketOfMoments (99893/100000) lo3114 hi3114 accepted3114
def lo3115b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨46,by decide⟩
def lo3115b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨47,by decide⟩
def lo3115 : CheckedMoment :=
  CheckedMoment.ofBessel lo3115b1 lo3115b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3115b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨51,by decide⟩
def hi3115b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨52,by decide⟩
def hi3115 : CheckedMoment :=
  CheckedMoment.ofBessel hi3115b1 hi3115b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3115 : meanBracketCheck (199787/200000) lo3115 hi3115=true := by decide +kernel
def bracket3115 : MeanBracket := meanBracketOfMoments (199787/200000) lo3115 hi3115 accepted3115
def lo3116b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨56,by decide⟩
def lo3116b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨57,by decide⟩
def lo3116 : CheckedMoment :=
  CheckedMoment.ofBessel lo3116b1 lo3116b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3116b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨61,by decide⟩
def hi3116b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨62,by decide⟩
def hi3116 : CheckedMoment :=
  CheckedMoment.ofBessel hi3116b1 hi3116b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3116 : meanBracketCheck (49947/50000) lo3116 hi3116=true := by decide +kernel
def bracket3116 : MeanBracket := meanBracketOfMoments (49947/50000) lo3116 hi3116 accepted3116
def lo3117b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨2,by decide⟩
def lo3117b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨3,by decide⟩
def lo3117 : CheckedMoment :=
  CheckedMoment.ofBessel lo3117b1 lo3117b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3117b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨7,by decide⟩
def hi3117b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨8,by decide⟩
def hi3117 : CheckedMoment :=
  CheckedMoment.ofBessel hi3117b1 hi3117b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3117 : meanBracketCheck (199789/200000) lo3117 hi3117=true := by decide +kernel
def bracket3117 : MeanBracket := meanBracketOfMoments (199789/200000) lo3117 hi3117 accepted3117
def lo3118b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨12,by decide⟩
def lo3118b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨13,by decide⟩
def lo3118 : CheckedMoment :=
  CheckedMoment.ofBessel lo3118b1 lo3118b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3118b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨17,by decide⟩
def hi3118b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨18,by decide⟩
def hi3118 : CheckedMoment :=
  CheckedMoment.ofBessel hi3118b1 hi3118b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3118 : meanBracketCheck (19979/20000) lo3118 hi3118=true := by decide +kernel
def bracket3118 : MeanBracket := meanBracketOfMoments (19979/20000) lo3118 hi3118 accepted3118
def lo3119b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨22,by decide⟩
def lo3119b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨23,by decide⟩
def lo3119 : CheckedMoment :=
  CheckedMoment.ofBessel lo3119b1 lo3119b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3119b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨27,by decide⟩
def hi3119b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨28,by decide⟩
def hi3119 : CheckedMoment :=
  CheckedMoment.ofBessel hi3119b1 hi3119b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3119 : meanBracketCheck (199791/200000) lo3119 hi3119=true := by decide +kernel
def bracket3119 : MeanBracket := meanBracketOfMoments (199791/200000) lo3119 hi3119 accepted3119
#print axioms bracket3104
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0194
