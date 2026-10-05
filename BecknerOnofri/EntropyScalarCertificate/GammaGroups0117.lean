module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0146
public import BecknerOnofri.EntropyScalarCertificate.Bessel0147
public import BecknerOnofri.EntropyScalarCertificate.Bessel0562
public import BecknerOnofri.EntropyScalarCertificate.Brackets0058
public import BecknerOnofri.EntropyScalarCertificate.Brackets0059
public import BecknerOnofri.EntropyScalarCertificate.Logs0117
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0936
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (2304528898915301441681181470076807683969/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2304528898915301441681181470076807683969/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (4622515956042367142685474674599669770763/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4622515956042367142685474674599669770763/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (9231573753872970026047837614753285138701/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9231573753872970026047837614753285138701/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0936 BracketBatch0058.bracket0937 (9231573753872970026047837614753285138701/20000000000000000000000000000000000000000) (12817787004584291180383695685422790371/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0936 BracketBatch0058.bracket0937
  (9231573753872970026047837614753285138701/20000000000000000000000000000000000000000) (12817787004584291180383695685422790371/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0936
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0937
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (115562898901059178567136866864991744269/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (115562898901059178567136866864991744269/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (579499481365121160833810481249583798391/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (579499481365121160833810481249583798391/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (144664246983802131708686851946817814967/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (144664246983802131708686851946817814967/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0937 BracketBatch0058.bracket0938 (144664246983802131708686851946817814967/312500000000000000000000000000000000000) (12946166932117996033965287853723164079/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0937 BracketBatch0058.bracket0938
  (144664246983802131708686851946817814967/312500000000000000000000000000000000000) (12946166932117996033965287853723164079/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0937
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0938
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (37087966807367754293363870799973363097/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (37087966807367754293363870799973363097/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (4649497598745964403746945211394538169367/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4649497598745964403746945211394538169367/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (2321373362416733422604357265347802139123/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2321373362416733422604357265347802139123/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0938 BracketBatch0058.bracket0939 (2321373362416733422604357265347802139123/5000000000000000000000000000000000000000) (1046044180601100290231489410738465353/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0938 BracketBatch0058.bracket0939
  (2321373362416733422604357265347802139123/5000000000000000000000000000000000000000) (1046044180601100290231489410738465353/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0938
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0939
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1162374399686491100936736302848634542341/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1162374399686491100936736302848634542341/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (2331510658265173492487665712966497336501/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2331510658265173492487665712966497336501/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (4656259457638155694361138318663766421183/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4656259457638155694361138318663766421183/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0939 BracketBatch0058.bracket0940 (4656259457638155694361138318663766421183/10000000000000000000000000000000000000000) (13205948945047821943643401262796022739/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0939 BracketBatch0058.bracket0940
  (4656259457638155694361138318663766421183/10000000000000000000000000000000000000000) (13205948945047821943643401262796022739/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0939
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0940
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (4663021316530346984975331425932994672999/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4663021316530346984975331425932994672999/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (292285445126689842011069896686716644233/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (292285445126689842011069896686716644233/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (9339588438557384457152449772920460980727/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9339588438557384457152449772920460980727/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0940 BracketBatch0058.bracket0941 (9339588438557384457152449772920460980727/20000000000000000000000000000000000000000) (26674725975416007413834981016389336287/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0940 BracketBatch0058.bracket0941
  (9339588438557384457152449772920460980727/20000000000000000000000000000000000000000) (26674725975416007413834981016389336287/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0940
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0941
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (187062684881081498887084733879498652309/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (187062684881081498887084733879498652309/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (2345067566867718697956362095530042358803/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2345067566867718697956362095530042358803/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (9366702255762474868089842538047551025331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9366702255762474868089842538047551025331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0941 BracketBatch0058.bracket0942 (9366702255762474868089842538047551025331/20000000000000000000000000000000000000000) (26939600814726239920194400548581963661/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0941 BracketBatch0058.bracket0942
  (9366702255762474868089842538047551025331/20000000000000000000000000000000000000000) (26939600814726239920194400548581963661/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0941
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0942
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (4690135133735437395912724191060084717603/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4690135133735437395912724191060084717603/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (4703725470908053969447950350680991902711/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4703725470908053969447950350680991902711/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (4696930302321745682680337270870538310157/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4696930302321745682680337270870538310157/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0942 BracketBatch0058.bracket0943 (4696930302321745682680337270870538310157/10000000000000000000000000000000000000000) (27206534509868220604856029490328413823/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0942 BracketBatch0058.bracket0943
  (4696930302321745682680337270870538310157/10000000000000000000000000000000000000000) (27206534509868220604856029490328413823/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0942
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0943
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1175931367727013492361987587670247975677/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1175931367727013492361987587670247975677/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2358669126778597508701610321358872716043/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2358669126778597508701610321358872716043/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (4710531862232624493425585496699368667397/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4710531862232624493425585496699368667397/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0117.rows ScalarLogs0117.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0943 BracketBatch0059.bracket0944 (4710531862232624493425585496699368667397/10000000000000000000000000000000000000000) (27475539221133558822535422241202247877/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0943 BracketBatch0059.bracket0944
  (4710531862232624493425585496699368667397/10000000000000000000000000000000000000000) (27475539221133558822535422241202247877/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0943
