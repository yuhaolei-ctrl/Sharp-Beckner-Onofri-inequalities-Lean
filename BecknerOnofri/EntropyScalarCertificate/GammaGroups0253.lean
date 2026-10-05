module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0316
public import BecknerOnofri.EntropyScalarCertificate.Bessel0317
public import BecknerOnofri.EntropyScalarCertificate.Bessel0647
public import BecknerOnofri.EntropyScalarCertificate.Brackets0126
public import BecknerOnofri.EntropyScalarCertificate.Brackets0127
public import BecknerOnofri.EntropyScalarCertificate.Logs0253
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2024
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (56413009037386881302368419142397639583381/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (56413009037386881302368419142397639583381/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1130686437198452764589082698295955262423/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1130686437198452764589082698295955262423/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (112947330897309519531822554057195402704531/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (112947330897309519531822554057195402704531/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2024 BracketBatch0126.bracket2025 (112947330897309519531822554057195402704531/20000000000000000000000000000000000000000) (2021709605850428558169346658682278705067/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2024 BracketBatch0126.bracket2025
  (112947330897309519531822554057195402704531/20000000000000000000000000000000000000000) (2021709605850428558169346658682278705067/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2024
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2025
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (56534321859922638229454134914797763121147/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (56534321859922638229454134914797763121147/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (56656172735657827995048205533045103072517/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56656172735657827995048205533045103072517/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (442150369513986196189462267374386196069/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (442150369513986196189462267374386196069/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2025 BracketBatch0126.bracket2026 (442150369513986196189462267374386196069/78125000000000000000000000000000000000) (2024433191211626938334654869934991392877/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2025 BracketBatch0126.bracket2026
  (442150369513986196189462267374386196069/78125000000000000000000000000000000000) (2024433191211626938334654869934991392877/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2025
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2026
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (28328086367828913997524102766522551536257/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28328086367828913997524102766522551536257/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (28389282621022544407546595272855101163499/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (28389282621022544407546595272855101163499/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (14179342247212864601267674509844413174939/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14179342247212864601267674509844413174939/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2026 BracketBatch0126.bracket2027 (14179342247212864601267674509844413174939/2500000000000000000000000000000000000000) (50679087579391742721390585938324290031/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2026 BracketBatch0126.bracket2027
  (14179342247212864601267674509844413174939/2500000000000000000000000000000000000000) (50679087579391742721390585938324290031/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2026
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2027
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (11355713048409017763018638109142040465399/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11355713048409017763018638109142040465399/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (56901502988342127904946139496899905089657/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56901502988342127904946139496899905089657/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (28420017057596804180009832510652526854163/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28420017057596804180009832510652526854163/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2027 BracketBatch0126.bracket2028 (28420017057596804180009832510652526854163/5000000000000000000000000000000000000000) (2029900572103430148435911328374810458837/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2027 BracketBatch0126.bracket2028
  (28420017057596804180009832510652526854163/5000000000000000000000000000000000000000) (2029900572103430148435911328374810458837/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2027
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2028
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (28450751494171063952473069748449952544827/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28450751494171063952473069748449952544827/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (11404997923193172964127067490817365112227/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11404997923193172964127067490817365112227/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (113926492604307992725581476950986730650789/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (113926492604307992725581476950986730650789/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2028 BracketBatch0126.bracket2029 (113926492604307992725581476950986730650789/20000000000000000000000000000000000000000) (2032644428565108462330301663526295392767/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2028 BracketBatch0126.bracket2029
  (113926492604307992725581476950986730650789/20000000000000000000000000000000000000000) (2032644428565108462330301663526295392767/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2028
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2029
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (14256247403991466205158834363521706390283/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14256247403991466205158834363521706390283/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (5714902879885131790692464677143575762659/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5714902879885131790692464677143575762659/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (57087009207408591363779992112761291593861/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (57087009207408591363779992112761291593861/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2029 BracketBatch0126.bracket2030 (57087009207408591363779992112761291593861/10000000000000000000000000000000000000000) (7950762122430178553475634451588088847/39062500000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2029 BracketBatch0126.bracket2030
  (57087009207408591363779992112761291593861/10000000000000000000000000000000000000000) (7950762122430178553475634451588088847/39062500000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2029
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2030
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (57149028798851317906924646771435757626587/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (57149028798851317906924646771435757626587/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (715920303047691351661666451751024206999/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (715920303047691351661666451751024206999/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (114422653042666626039857962911517694186507/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (114422653042666626039857962911517694186507/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2030 BracketBatch0126.bracket2031 (114422653042666626039857962911517694186507/20000000000000000000000000000000000000000) (1019076313714519451498756941238893158313/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2030 BracketBatch0126.bracket2031
  (114422653042666626039857962911517694186507/20000000000000000000000000000000000000000) (1019076313714519451498756941238893158313/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2030
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2031
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (57273624243815308132933316140081936559917/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (57273624243815308132933316140081936559917/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (57398779690925055928355309972770956416091/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (57398779690925055928355309972770956416091/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (14334050491842545507661078264106611622001/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14334050491842545507661078264106611622001/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0253.rows ScalarLogs0253.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2031 BracketBatch0127.bracket2032 (14334050491842545507661078264106611622001/2500000000000000000000000000000000000000) (2040917032035477561923123621792303930323/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2031 BracketBatch0127.bracket2032
  (14334050491842545507661078264106611622001/2500000000000000000000000000000000000000) (2040917032035477561923123621792303930323/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2031
