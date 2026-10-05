module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0355
public import BecknerOnofri.EntropyScalarCertificate.Bessel0356
public import BecknerOnofri.EntropyScalarCertificate.Bessel0666
public import BecknerOnofri.EntropyScalarCertificate.Bessel0667
public import BecknerOnofri.EntropyScalarCertificate.Brackets0142
public import BecknerOnofri.EntropyScalarCertificate.Logs0284
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2272
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (122650006793099687802504077399043240434617/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (122650006793099687802504077399043240434617/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (123241793687549811790514362439322866123619/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (123241793687549811790514362439322866123619/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (61472950120162374898254609959591526639559/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (61472950120162374898254609959591526639559/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2272 BracketBatch0142.bracket2273 (61472950120162374898254609959591526639559/5000000000000000000000000000000000000000) (303550182754849558451295447687755088663/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2272 BracketBatch0142.bracket2273
  (61472950120162374898254609959591526639559/5000000000000000000000000000000000000000) (303550182754849558451295447687755088663/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2272
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2273
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (3851306052735931618453573826228839566363/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3851306052735931618453573826228839566363/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (123839384586982272745568169107715849535267/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (123839384586982272745568169107715849535267/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (247081178274532084536082531547038715658883/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (247081178274532084536082531547038715658883/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2273 BracketBatch0142.bracket2274 (247081178274532084536082531547038715658883/20000000000000000000000000000000000000000) (3041934489968952808272243090769250975221/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2273 BracketBatch0142.bracket2274
  (247081178274532084536082531547038715658883/20000000000000000000000000000000000000000) (3041934489968952808272243090769250975221/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2273
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2274
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (3869980768343196023299005284616120297977/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3869980768343196023299005284616120297977/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (124442865262923422341114137904903731884269/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (124442865262923422341114137904903731884269/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (248282249849905695086682307012619581419533/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (248282249849905695086682307012619581419533/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2274 BracketBatch0142.bracket2275 (248282249849905695086682307012619581419533/20000000000000000000000000000000000000000) (19052501004454803318202770409620671073/62500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2274 BracketBatch0142.bracket2275
  (248282249849905695086682307012619581419533/20000000000000000000000000000000000000000) (19052501004454803318202770409620671073/62500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2274
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2275
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (62221432631461711170557068952451865942133/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (62221432631461711170557068952451865942133/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (62526161592674681827474122219021381668673/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (62526161592674681827474122219021381668673/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (62373797112068196499015595585736623805403/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (62373797112068196499015595585736623805403/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2275 BracketBatch0142.bracket2276 (62373797112068196499015595585736623805403/5000000000000000000000000000000000000000) (190931196731097056488406249682353593303/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2275 BracketBatch0142.bracket2276
  (62373797112068196499015595585736623805403/5000000000000000000000000000000000000000) (190931196731097056488406249682353593303/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2275
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2276
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (125052323185349363654948244438042763337343/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (125052323185349363654948244438042763337343/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (125667847564935932615108446572699940112769/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (125667847564935932615108446572699940112769/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (122421958374162742319363618657589210669/9765625000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (122421958374162742319363618657589210669/9765625000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2276 BracketBatch0142.bracket2277 (122421958374162742319363618657589210669/9765625000000000000000000000000000000) (3061431762757604418026022471530031874847/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2276 BracketBatch0142.bracket2277
  (122421958374162742319363618657589210669/9765625000000000000000000000000000000) (3061431762757604418026022471530031874847/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2276
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2277
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (62833923782467966307554223286349970056383/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (62833923782467966307554223286349970056383/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (15786191174572022369348256714474813584089/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15786191174572022369348256714474813584089/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (125978688480756055784947250144249224392739/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (125978688480756055784947250144249224392739/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2277 BracketBatch0142.bracket2278 (125978688480756055784947250144249224392739/10000000000000000000000000000000000000000) (766999580424922733819762761430292127069/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2277 BracketBatch0142.bracket2278
  (125978688480756055784947250144249224392739/10000000000000000000000000000000000000000) (766999580424922733819762761430292127069/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2277
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2278
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (126289529396576178954786053715798508672709/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (126289529396576178954786053715798508672709/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (126917461504209932085603791066805468045093/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (126917461504209932085603791066805468045093/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (126603495450393055520194922391301988358901/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (126603495450393055520194922391301988358901/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2278 BracketBatch0142.bracket2279 (126603495450393055520194922391301988358901/10000000000000000000000000000000000000000) (1537299572179704755519520102949720347103/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2278 BracketBatch0142.bracket2279
  (126603495450393055520194922391301988358901/10000000000000000000000000000000000000000) (1537299572179704755519520102949720347103/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2278
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2279
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (12691746150420993208560379106680546804509/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12691746150420993208560379106680546804509/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (63775869293505919364648553943699850010013/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (63775869293505919364648553943699850010013/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (63617300022805442703725224738551292016279/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (63617300022805442703725224738551292016279/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0284.rows ScalarLogs0284.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2279 BracketBatch0142.bracket2280 (63617300022805442703725224738551292016279/5000000000000000000000000000000000000000) (616246910931621704932402520629057568313/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2279 BracketBatch0142.bracket2280
  (63617300022805442703725224738551292016279/5000000000000000000000000000000000000000) (616246910931621704932402520629057568313/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2279
