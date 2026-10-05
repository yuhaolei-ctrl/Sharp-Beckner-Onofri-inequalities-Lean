module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0333
public import BecknerOnofri.EntropyScalarCertificate.Bessel0334
public import BecknerOnofri.EntropyScalarCertificate.Bessel0335
public import BecknerOnofri.EntropyScalarCertificate.Bessel0655
public import BecknerOnofri.EntropyScalarCertificate.Bessel0656
public import BecknerOnofri.EntropyScalarCertificate.Brackets0133
public import BecknerOnofri.EntropyScalarCertificate.Brackets0134
public import BecknerOnofri.EntropyScalarCertificate.Logs0267
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2136
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (74419866676110564336664927224522980555853/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (74419866676110564336664927224522980555853/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (37317003500445813670540210060311050444867/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (37317003500445813670540210060311050444867/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (149053873677002191677745347345145081445587/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (149053873677002191677745347345145081445587/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2136 BracketBatch0133.bracket2137 (149053873677002191677745347345145081445587/20000000000000000000000000000000000000000) (1188445826147083039821634891679070238161/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2136 BracketBatch0133.bracket2137
  (149053873677002191677745347345145081445587/20000000000000000000000000000000000000000) (1188445826147083039821634891679070238161/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2136
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2137
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (74634007000891627341080420120622100889731/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (74634007000891627341080420120622100889731/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (37424704230286240894299385718847766545537/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (37424704230286240894299385718847766545537/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (29896683092292821825935838311663526796161/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29896683092292821825935838311663526796161/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2137 BracketBatch0133.bracket2138 (29896683092292821825935838311663526796161/4000000000000000000000000000000000000000) (2380616866342462211215839471877346992117/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2137 BracketBatch0133.bracket2138
  (29896683092292821825935838311663526796161/4000000000000000000000000000000000000000) (2380616866342462211215839471877346992117/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2137
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2138
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (74849408460572481788598771437695533091071/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (74849408460572481788598771437695533091071/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (15013216442816616765154320902763911070983/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15013216442816616765154320902763911070983/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (74957745337327782807185187975757544222993/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (74957745337327782807185187975757544222993/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2138 BracketBatch0133.bracket2139 (74957745337327782807185187975757544222993/10000000000000000000000000000000000000000) (47687081644905659816849459497948322751/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2138 BracketBatch0133.bracket2139
  (74957745337327782807185187975757544222993/10000000000000000000000000000000000000000) (47687081644905659816849459497948322751/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2138
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2139
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (2345815069190096369555362641056861104841/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2345815069190096369555362641056861104841/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (75284039552415520975891290512203435285123/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (75284039552415520975891290512203435285123/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (30070024353299720960332579005204598128007/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30070024353299720960332579005204598128007/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2139 BracketBatch0133.bracket2140 (30070024353299720960332579005204598128007/4000000000000000000000000000000000000000) (1194051686210482355709326753976691040727/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2139 BracketBatch0133.bracket2140
  (30070024353299720960332579005204598128007/4000000000000000000000000000000000000000) (1194051686210482355709326753976691040727/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2139
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2140
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (117631311800649251524830141425317867633/15625000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (117631311800649251524830141425317867633/15625000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (18875822975145843061122428061873095383663/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18875822975145843061122428061873095383663/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (37696832863249723305095250689923954204943/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37696832863249723305095250689923954204943/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2140 BracketBatch0133.bracket2141 (37696832863249723305095250689923954204943/5000000000000000000000000000000000000000) (2391864809937983310992057986801070570261/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2140 BracketBatch0133.bracket2141
  (37696832863249723305095250689923954204943/5000000000000000000000000000000000000000) (2391864809937983310992057986801070570261/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2140
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2141
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (75503291900583372244489712247492381534649/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (75503291900583372244489712247492381534649/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (4732740676226003560371224872475523723031/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4732740676226003560371224872475523723031/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (30245428544039885842085862041420152220629/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30245428544039885842085862041420152220629/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2141 BracketBatch0133.bracket2142 (30245428544039885842085862041420152220629/4000000000000000000000000000000000000000) (239563846852257104992390306573242141991/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2141 BracketBatch0133.bracket2142
  (30245428544039885842085862041420152220629/4000000000000000000000000000000000000000) (239563846852257104992390306573242141991/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2141
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2142
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (75723850819616056965939597959608379568493/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (75723850819616056965939597959608379568493/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (18986432002147225874288542042480535058889/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18986432002147225874288542042480535058889/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (151669578828204960463093766129530519804049/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (151669578828204960463093766129530519804049/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2142 BracketBatch0133.bracket2143 (151669578828204960463093766129530519804049/20000000000000000000000000000000000000000) (2399424422566442939328788903326980631847/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2142 BracketBatch0133.bracket2143
  (151669578828204960463093766129530519804049/20000000000000000000000000000000000000000) (2399424422566442939328788903326980631847/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2142
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2143
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (75945728008588903497154168169922140235553/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (75945728008588903497154168169922140235553/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (76168935306689686375914400806601995549417/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (76168935306689686375914400806601995549417/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (15211466331527858987306856897652413578497/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15211466331527858987306856897652413578497/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0267.rows ScalarLogs0267.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2143 BracketBatch0134.bracket2144 (15211466331527858987306856897652413578497/2000000000000000000000000000000000000000) (2403222747134634790729651732555362542371/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2143 BracketBatch0134.bracket2144
  (15211466331527858987306856897652413578497/2000000000000000000000000000000000000000) (2403222747134634790729651732555362542371/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2143
