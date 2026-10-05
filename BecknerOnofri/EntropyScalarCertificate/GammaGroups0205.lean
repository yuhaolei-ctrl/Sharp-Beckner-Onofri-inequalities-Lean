module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0256
public import BecknerOnofri.EntropyScalarCertificate.Bessel0257
public import BecknerOnofri.EntropyScalarCertificate.Bessel0617
public import BecknerOnofri.EntropyScalarCertificate.Brackets0102
public import BecknerOnofri.EntropyScalarCertificate.Brackets0103
public import BecknerOnofri.EntropyScalarCertificate.Logs0205
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1640
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (9548475055326417717285160606073443978737/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9548475055326417717285160606073443978737/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (19108654347192564617018737586232006528229/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19108654347192564617018737586232006528229/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (38205604457845400051589058798378894485703/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38205604457845400051589058798378894485703/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1640 BracketBatch0102.bracket1641 (38205604457845400051589058798378894485703/20000000000000000000000000000000000000000) (377354903740549711351599521838720902547/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1640 BracketBatch0102.bracket1641
  (38205604457845400051589058798378894485703/20000000000000000000000000000000000000000) (377354903740549711351599521838720902547/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1640
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1641
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (9554327173596282308509368793116003264113/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9554327173596282308509368793116003264113/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (19120375070322930011998062767709855536047/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19120375070322930011998062767709855536047/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (38229029417515494629016800353941862064273/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38229029417515494629016800353941862064273/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1641 BracketBatch0102.bracket1642 (38229029417515494629016800353941862064273/20000000000000000000000000000000000000000) (377661322610078793649034398331962237367/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1641 BracketBatch0102.bracket1642
  (38229029417515494629016800353941862064273/20000000000000000000000000000000000000000) (377661322610078793649034398331962237367/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1641
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1642
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (4780093767580732502999515691927463884011/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4780093767580732502999515691927463884011/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (19132112316347089605104625307417198061679/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19132112316347089605104625307417198061679/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (38252487386670019617102688075127053597723/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38252487386670019617102688075127053597723/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1642 BracketBatch0102.bracket1643 (38252487386670019617102688075127053597723/20000000000000000000000000000000000000000) (377968080993942898955391768835748563189/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1642 BracketBatch0102.bracket1643
  (38252487386670019617102688075127053597723/20000000000000000000000000000000000000000) (377968080993942898955391768835748563189/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1642
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1643
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (4783028079086772401276156326854299515419/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4783028079086772401276156326854299515419/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (19143866121669816237468210989831035668573/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19143866121669816237468210989831035668573/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (38275978438016905842572836297248233730249/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38275978438016905842572836297248233730249/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1643 BracketBatch0102.bracket1644 (38275978438016905842572836297248233730249/20000000000000000000000000000000000000000) (756550358862210238790016021297729827847/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1643 BracketBatch0102.bracket1644
  (38275978438016905842572836297248233730249/20000000000000000000000000000000000000000) (756550358862210238790016021297729827847/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1643
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1644
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1914386612166981623746821098983103566857/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1914386612166981623746821098983103566857/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (9577818261398919761822481599242382944131/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9577818261398919761822481599242382944131/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1196859457639614242534786693384868798651/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1196859457639614242534786693384868798651/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1644 BracketBatch0102.bracket1645 (1196859457639614242534786693384868798651/625000000000000000000000000000000000000) (757165236923112260528267270216266835857/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1644 BracketBatch0102.bracket1645
  (1196859457639614242534786693384868798651/625000000000000000000000000000000000000) (757165236923112260528267270216266835857/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1644
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1645
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (19155636522797839523644963198484765888259/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19155636522797839523644963198484765888259/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (19167423556340189142851838985283795523859/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19167423556340189142851838985283795523859/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (19161530039569014333248401091884280706059/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19161530039569014333248401091884280706059/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1645 BracketBatch0102.bracket1646 (19161530039569014333248401091884280706059/10000000000000000000000000000000000000000) (378890398626316310568715826156926606087/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1645 BracketBatch0102.bracket1646
  (19161530039569014333248401091884280706059/10000000000000000000000000000000000000000) (378890398626316310568715826156926606087/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1645
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1646
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1197963972271261821428239936580237220241/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1197963972271261821428239936580237220241/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (19179227259008539510206951827668001657237/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19179227259008539510206951827668001657237/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (38346650815348728653058790812951797181093/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38346650815348728653058790812951797181093/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1646 BracketBatch0102.bracket1647 (38346650815348728653058790812951797181093/20000000000000000000000000000000000000000) (758397040934875738648760279239743602289/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1646 BracketBatch0102.bracket1647
  (38346650815348728653058790812951797181093/20000000000000000000000000000000000000000) (758397040934875738648760279239743602289/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1646
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1647
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (9589613629504269755103475913834000828617/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9589613629504269755103475913834000828617/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (767641906704702233387158996937590600591/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (767641906704702233387158996937590600591/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (38370274926626095344885926751107766672009/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38370274926626095344885926751107766672009/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0205.rows ScalarLogs0205.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1647 BracketBatch0103.bracket1648 (38370274926626095344885926751107766672009/20000000000000000000000000000000000000000) (379506984528006977649964667141290991963/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1647 BracketBatch0103.bracket1648
  (38370274926626095344885926751107766672009/20000000000000000000000000000000000000000) (379506984528006977649964667141290991963/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1647
