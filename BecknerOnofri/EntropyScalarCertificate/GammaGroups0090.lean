module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0112
public import BecknerOnofri.EntropyScalarCertificate.Bessel0113
public import BecknerOnofri.EntropyScalarCertificate.Bessel0545
public import BecknerOnofri.EntropyScalarCertificate.Brackets0045
public import BecknerOnofri.EntropyScalarCertificate.Logs0090
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0720
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (103133501515214184513818700550973600873/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (103133501515214184513818700550973600873/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1036661087225118774501753512718234362363/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1036661087225118774501753512718234362363/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (2067996102377260619639940518227970371093/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2067996102377260619639940518227970371093/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0720 BracketBatch0045.bracket0721 (2067996102377260619639940518227970371093/10000000000000000000000000000000000000000) (1306927985511444484271573491973244953/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0720 BracketBatch0045.bracket0721
  (2067996102377260619639940518227970371093/10000000000000000000000000000000000000000) (1306927985511444484271573491973244953/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0720
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0721
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (2073322174450237549003507025436468724723/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2073322174450237549003507025436468724723/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (2083981167381499221500234292268413073043/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2083981167381499221500234292268413073043/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (2078651670915868385251870658852440898883/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2078651670915868385251870658852440898883/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0721 BracketBatch0045.bracket0722 (2078651670915868385251870658852440898883/10000000000000000000000000000000000000000) (1333437953178910361171079678047940027/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0721 BracketBatch0045.bracket0722
  (2078651670915868385251870658852440898883/10000000000000000000000000000000000000000) (1333437953178910361171079678047940027/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0721
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0722
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (26049764592268740268752928653355163413/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26049764592268740268752928653355163413/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (2094647051031901096942523569224151004007/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2094647051031901096942523569224151004007/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (4178628218413400318442757861492564077047/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4178628218413400318442757861492564077047/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0722 BracketBatch0045.bracket0723 (4178628218413400318442757861492564077047/20000000000000000000000000000000000000000) (680174775561934651698396772890951969/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0722 BracketBatch0045.bracket0723
  (4178628218413400318442757861492564077047/20000000000000000000000000000000000000000) (680174775561934651698396772890951969/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0722
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0723
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (523661762757975274235630892306037751001/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (523661762757975274235630892306037751001/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (2105319867470274575789456470155653274397/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2105319867470274575789456470155653274397/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (4199966918502175672731980039379804278401/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4199966918502175672731980039379804278401/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0723 BracketBatch0045.bracket0724 (4199966918502175672731980039379804278401/20000000000000000000000000000000000000000) (1387666920015533064427710876025900199/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0723 BracketBatch0045.bracket0724
  (4199966918502175672731980039379804278401/20000000000000000000000000000000000000000) (1387666920015533064427710876025900199/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0723
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0724
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1052659933735137287894728235077826637197/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1052659933735137287894728235077826637197/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1057999829450745567940654418782455616393/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1057999829450745567940654418782455616393/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (211065976318588285583538265386028225359/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (211065976318588285583538265386028225359/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0724 BracketBatch0045.bracket0725 (211065976318588285583538265386028225359/1000000000000000000000000000000000000000) (176924278056315994356096424387763557/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0724 BracketBatch0045.bracket0725
  (211065976318588285583538265386028225359/1000000000000000000000000000000000000000) (176924278056315994356096424387763557/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0724
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0725
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (2115999658901491135881308837564911232783/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2115999658901491135881308837564911232783/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (10633432338337550716987087582119082183/50000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10633432338337550716987087582119082183/50000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (4242686126569001279278726353988727669383/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4242686126569001279278726353988727669383/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0725 BracketBatch0045.bracket0726 (4242686126569001279278726353988727669383/20000000000000000000000000000000000000000) (1443535653010688687263108549237976351/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0725 BracketBatch0045.bracket0726
  (4242686126569001279278726353988727669383/20000000000000000000000000000000000000000) (1443535653010688687263108549237976351/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0725
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0726
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (2126686467667510143397417516423816436597/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2126686467667510143397417516423816436597/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (2137380336248433474531240096703440447679/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2137380336248433474531240096703440447679/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (1066016700978985904482164403281814221069/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1066016700978985904482164403281814221069/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0726 BracketBatch0045.bracket0727 (1066016700978985904482164403281814221069/5000000000000000000000000000000000000000) (1472095418321272568367129484501401527/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0726 BracketBatch0045.bracket0727
  (1066016700978985904482164403281814221069/5000000000000000000000000000000000000000) (1472095418321272568367129484501401527/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0726
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0727
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (534345084062108368632810024175860111919/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (534345084062108368632810024175860111919/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (2148081307263567014379519405720655944809/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2148081307263567014379519405720655944809/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (857092328702400097782151900484819278497/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (857092328702400097782151900484819278497/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0090.rows ScalarLogs0090.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0727 BracketBatch0045.bracket0728 (857092328702400097782151900484819278497/4000000000000000000000000000000000000000) (1501077757109596491832630869609157691/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0727 BracketBatch0045.bracket0728
  (857092328702400097782151900484819278497/4000000000000000000000000000000000000000) (1501077757109596491832630869609157691/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0727
