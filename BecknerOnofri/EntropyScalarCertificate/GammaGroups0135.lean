module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0168
public import BecknerOnofri.EntropyScalarCertificate.Bessel0169
public import BecknerOnofri.EntropyScalarCertificate.Bessel0170
public import BecknerOnofri.EntropyScalarCertificate.Bessel0573
public import BecknerOnofri.EntropyScalarCertificate.Brackets0067
public import BecknerOnofri.EntropyScalarCertificate.Brackets0068
public import BecknerOnofri.EntropyScalarCertificate.Logs0135
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1080
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (6844238541083002557123224102448301452191/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6844238541083002557123224102448301452191/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (6862539331420898488373402080783634886611/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6862539331420898488373402080783634886611/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (6853388936251950522748313091615968169401/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6853388936251950522748313091615968169401/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1080 BracketBatch0067.bracket1081 (6853388936251950522748313091615968169401/10000000000000000000000000000000000000000) (90302188097752099725742506301111632801/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1080 BracketBatch0067.bracket1081
  (6853388936251950522748313091615968169401/10000000000000000000000000000000000000000) (90302188097752099725742506301111632801/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1080
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1081
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (428908708213806155523337630048977180413/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (428908708213806155523337630048977180413/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (6880891115597449872297056072568915966313/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6880891115597449872297056072568915966313/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (13743430447018348360670458153352550852921/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13743430447018348360670458153352550852921/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1081 BracketBatch0067.bracket1082 (13743430447018348360670458153352550852921/20000000000000000000000000000000000000000) (45503350278005791720018165154220494023/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1081 BracketBatch0067.bracket1082
  (13743430447018348360670458153352550852921/20000000000000000000000000000000000000000) (45503350278005791720018165154220494023/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1081
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1082
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (688089111559744987229705607256891596631/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (688089111559744987229705607256891596631/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (6899294240178679131529438862138755144593/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6899294240178679131529438862138755144593/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (13780185355776129003826494934707671110903/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13780185355776129003826494934707671110903/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1082 BracketBatch0067.bracket1083 (13780185355776129003826494934707671110903/20000000000000000000000000000000000000000) (91715731259636463294200941646458277789/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1082 BracketBatch0067.bracket1083
  (13780185355776129003826494934707671110903/20000000000000000000000000000000000000000) (91715731259636463294200941646458277789/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1082
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1083
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (689929424017867913152943886213875514459/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (689929424017867913152943886213875514459/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (6917749054909148912561589295107935471043/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6917749054909148912561589295107935471043/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (13817043295087828044091028157246690615633/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13817043295087828044091028157246690615633/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1083 BracketBatch0067.bracket1084 (13817043295087828044091028157246690615633/20000000000000000000000000000000000000000) (92429344196451691159153924108492552413/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1083 BracketBatch0067.bracket1084
  (13817043295087828044091028157246690615633/20000000000000000000000000000000000000000) (92429344196451691159153924108492552413/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1083
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1084
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (21617965796591090351754966547212298347/31250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21617965796591090351754966547212298347/31250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (3468127956375072832252150291064337127981/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3468127956375072832252150291064337127981/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (6927002483829647288532944938618304863501/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6927002483829647288532944938618304863501/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1084 BracketBatch0067.bracket1085 (6927002483829647288532944938618304863501/10000000000000000000000000000000000000000) (46573782843712076845809660824173988033/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1084 BracketBatch0067.bracket1085
  (6927002483829647288532944938618304863501/10000000000000000000000000000000000000000) (46573782843712076845809660824173988033/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1084
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1085
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (6936255912750145664504300582128674255959/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6936255912750145664504300582128674255959/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (6954815169918420229187930982525309300373/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6954815169918420229187930982525309300373/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (3472767770667141473423057891163495889083/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3472767770667141473423057891163495889083/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1085 BracketBatch0067.bracket1086 (3472767770667141473423057891163495889083/5000000000000000000000000000000000000000) (93870422227214787565103181465861550741/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1085 BracketBatch0067.bracket1086
  (3472767770667141473423057891163495889083/5000000000000000000000000000000000000000) (93870422227214787565103181465861550741/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1085
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1086
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (695481516991842022918793098252530930037/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (695481516991842022918793098252530930037/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1743356796481373747457845469703692982911/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1743356796481373747457845469703692982911/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (6964121177921957609509656430670040616007/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6964121177921957609509656430670040616007/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1086 BracketBatch0067.bracket1087 (6964121177921957609509656430670040616007/10000000000000000000000000000000000000000) (94597940485915278584851735368783954273/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1086 BracketBatch0067.bracket1087
  (6964121177921957609509656430670040616007/10000000000000000000000000000000000000000) (94597940485915278584851735368783954273/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1086
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1087
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0169.rows BesselBatch0169.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (6973427185925494989831381878814771931641/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6973427185925494989831381878814771931641/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (6992092323617547312700143784168992369019/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6992092323617547312700143784168992369019/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (698275975477152115126576283149188215033/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (698275975477152115126576283149188215033/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0135.rows ScalarLogs0135.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1087 BracketBatch0068.bracket1088 (698275975477152115126576283149188215033/1000000000000000000000000000000000000000) (4766507365540434810538013181043719613/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1087 BracketBatch0068.bracket1088
  (698275975477152115126576283149188215033/1000000000000000000000000000000000000000) (4766507365540434810538013181043719613/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1087
