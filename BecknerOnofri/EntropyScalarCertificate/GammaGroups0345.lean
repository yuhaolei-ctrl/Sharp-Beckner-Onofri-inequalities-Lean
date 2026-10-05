module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0431
public import BecknerOnofri.EntropyScalarCertificate.Bessel0432
public import BecknerOnofri.EntropyScalarCertificate.Bessel0704
public import BecknerOnofri.EntropyScalarCertificate.Bessel0705
public import BecknerOnofri.EntropyScalarCertificate.Brackets0172
public import BecknerOnofri.EntropyScalarCertificate.Brackets0173
public import BecknerOnofri.EntropyScalarCertificate.Logs0345
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2760
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (176307410670257973389514376558450682741813/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (176307410670257973389514376558450682741813/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (883089568867850905822547171676643541811623/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (883089568867850905822547171676643541811623/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (110289163888696298298132440904306059720043/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (110289163888696298298132440904306059720043/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2760 BracketBatch0172.bracket2761 (110289163888696298298132440904306059720043/1250000000000000000000000000000000000000) (2959802537937108301811453229464996283383/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2760 BracketBatch0172.bracket2761
  (110289163888696298298132440904306059720043/1250000000000000000000000000000000000000) (2959802537937108301811453229464996283383/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2760
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2761
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (44154478443392545291127358583832177090581/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (44154478443392545291127358583832177090581/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (176929514067762374036042389068986144964691/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (176929514067762374036042389068986144964691/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (70709485568266511040110364680862970665403/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (70709485568266511040110364680862970665403/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2761 BracketBatch0172.bracket2762 (70709485568266511040110364680862970665403/800000000000000000000000000000000000000) (2961153870152706231051817172901740982999/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2761 BracketBatch0172.bracket2762
  (70709485568266511040110364680862970665403/800000000000000000000000000000000000000) (2961153870152706231051817172901740982999/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2761
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2762
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (221161892584702967545052986336232681205863/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (221161892584702967545052986336232681205863/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (886211086893132877028226444292414238615343/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (886211086893132877028226444292414238615343/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (354171731446388949441687677927468992687759/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (354171731446388949441687677927468992687759/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2762 BracketBatch0172.bracket2763 (354171731446388949441687677927468992687759/4000000000000000000000000000000000000000) (5925015283838907884338638242140687619881/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2762 BracketBatch0172.bracket2763
  (354171731446388949441687677927468992687759/4000000000000000000000000000000000000000) (5925015283838907884338638242140687619881/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2762
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2763
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (44310554344656643851411322214620711930767/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (44310554344656643851411322214620711930767/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (887780147866362413097461546662938589897501/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (887780147866362413097461546662938589897501/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (1773991234759495290125687990955352828512841/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1773991234759495290125687990955352828512841/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2763 BracketBatch0172.bracket2764 (1773991234759495290125687990955352828512841/20000000000000000000000000000000000000000) (740965965413735116972924394065020094081/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2763 BracketBatch0172.bracket2764
  (1773991234759495290125687990955352828512841/20000000000000000000000000000000000000000) (740965965413735116972924394065020094081/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2763
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2764
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (443890073933181206548730773331469294948749/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (443890073933181206548730773331469294948749/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (889354782802472045052671810520257712099261/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (889354782802472045052671810520257712099261/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (1777134930668834458150133357183196301996759/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1777134930668834458150133357183196301996759/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2764 BracketBatch0172.bracket2765 (1777134930668834458150133357183196301996759/20000000000000000000000000000000000000000) (593044507563875882316194113774330052123/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2764 BracketBatch0172.bracket2765
  (1777134930668834458150133357183196301996759/20000000000000000000000000000000000000000) (593044507563875882316194113774330052123/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2764
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2765
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (444677391401236022526335905260128856049629/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (444677391401236022526335905260128856049629/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (89093502145571071735666324852456422744331/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (89093502145571071735666324852456422744331/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (222536225532272845301166882380602742442821/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (222536225532272845301166882380602742442821/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2765 BracketBatch0172.bracket2766 (222536225532272845301166882380602742442821/2500000000000000000000000000000000000000) (5933167357831777794786949273993659717309/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2765 BracketBatch0172.bracket2766
  (222536225532272845301166882380602742442821/2500000000000000000000000000000000000000) (5933167357831777794786949273993659717309/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2765
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2766
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (890935021455710717356663248524564227443307/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (890935021455710717356663248524564227443307/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (178504178758495776439435895390173042748943/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (178504178758495776439435895390173042748943/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (891727957624094799776921362737714720594011/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (891727957624094799776921362737714720594011/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2766 BracketBatch0172.bracket2767 (891727957624094799776921362737714720594011/10000000000000000000000000000000000000000) (5935894586981547459997663954648236539443/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2766 BracketBatch0172.bracket2767
  (891727957624094799776921362737714720594011/10000000000000000000000000000000000000000) (5935894586981547459997663954648236539443/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2766
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2767
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (111565111724059860274647434618858151718089/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (111565111724059860274647434618858151718089/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (894112429993222709377290218727838728012037/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (894112429993222709377290218727838728012037/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (1786633323785701591574469695678703941756749/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1786633323785701591574469695678703941756749/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0345.rows ScalarLogs0345.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2767 BracketBatch0173.bracket2768 (1786633323785701591574469695678703941756749/20000000000000000000000000000000000000000) (2969313390133809783539657178453730613647/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2767 BracketBatch0173.bracket2768
  (1786633323785701591574469695678703941756749/20000000000000000000000000000000000000000) (2969313390133809783539657178453730613647/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2767
