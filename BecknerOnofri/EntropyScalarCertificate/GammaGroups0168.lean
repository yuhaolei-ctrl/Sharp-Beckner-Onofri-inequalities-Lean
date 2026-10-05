module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0210
public import BecknerOnofri.EntropyScalarCertificate.Bessel0211
public import BecknerOnofri.EntropyScalarCertificate.Bessel0593
public import BecknerOnofri.EntropyScalarCertificate.Bessel0594
public import BecknerOnofri.EntropyScalarCertificate.Brackets0084
public import BecknerOnofri.EntropyScalarCertificate.Logs0168
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1344
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1900875666034311121302347106592511084307/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1900875666034311121302347106592511084307/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (7620975994188258963282501137629680102943/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7620975994188258963282501137629680102943/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (15224478658325503448491889563999724440171/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15224478658325503448491889563999724440171/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1344 BracketBatch0084.bracket1345 (15224478658325503448491889563999724440171/10000000000000000000000000000000000000000) (540322917919875990017830860735866497829/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1344 BracketBatch0084.bracket1345
  (15224478658325503448491889563999724440171/10000000000000000000000000000000000000000) (540322917919875990017830860735866497829/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1344
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1345
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (15241951988376517926565002275259360205883/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15241951988376517926565002275259360205883/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (15277077424227052574126996583839186363481/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15277077424227052574126996583839186363481/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (7629757353150892625172999714774636642341/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7629757353150892625172999714774636642341/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1345 BracketBatch0084.bracket1346 (7629757353150892625172999714774636642341/5000000000000000000000000000000000000000) (271153364726546412462923777743456521879/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1345 BracketBatch0084.bracket1346
  (7629757353150892625172999714774636642341/5000000000000000000000000000000000000000) (271153364726546412462923777743456521879/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1345
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1346
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (7638538712113526287063498291919593181739/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7638538712113526287063498291919593181739/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (7656191596067262620146144097727660402761/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7656191596067262620146144097727660402761/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (30589460616361577814419284779294507169/20000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30589460616361577814419284779294507169/20000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1346 BracketBatch0084.bracket1347 (30589460616361577814419284779294507169/20000000000000000000000000000000000000) (136074883847803554109996237495924388123/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1346 BracketBatch0084.bracket1347
  (30589460616361577814419284779294507169/20000000000000000000000000000000000000) (136074883847803554109996237495924388123/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1346
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1347
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (15312383192134525240292288195455320805519/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15312383192134525240292288195455320805519/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (15347870866161186647193983783723230587051/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15347870866161186647193983783723230587051/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (3066025405829571188748627197917855139257/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3066025405829571188748627197917855139257/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1347 BracketBatch0084.bracket1348 (3066025405829571188748627197917855139257/2000000000000000000000000000000000000000) (109260279280612523019229272905556046919/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1347 BracketBatch0084.bracket1348
  (3066025405829571188748627197917855139257/2000000000000000000000000000000000000000) (109260279280612523019229272905556046919/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1347
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1348
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1918483858270148330899247972965403823381/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1918483858270148330899247972965403823381/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (3076708407673389555331305500327305530101/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3076708407673389555331305500327305530101/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (30731412904528134423850511285359758237553/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30731412904528134423850511285359758237553/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1348 BracketBatch0084.bracket1349 (30731412904528134423850511285359758237553/20000000000000000000000000000000000000000) (274156186853988496159679424936707658299/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1348 BracketBatch0084.bracket1349
  (30731412904528134423850511285359758237553/20000000000000000000000000000000000000000) (274156186853988496159679424936707658299/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1348
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1349
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (7691771019183473888328263750818263825251/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7691771019183473888328263750818263825251/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (15419398319057081586250454490099896729447/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15419398319057081586250454490099896729447/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (30802940357424029362906981991736424379949/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30802940357424029362906981991736424379949/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1349 BracketBatch0084.bracket1350 (30802940357424029362906981991736424379949/20000000000000000000000000000000000000000) (550332529081371746133586232700900395323/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1349 BracketBatch0084.bracket1350
  (30802940357424029362906981991736424379949/20000000000000000000000000000000000000000) (550332529081371746133586232700900395323/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1349
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1350
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (3854849579764270396562613622524974182361/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3854849579764270396562613622524974182361/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (7727720668516926894839423949919818747477/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7727720668516926894839423949919818747477/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (15437419828045467687964651194969767112199/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15437419828045467687964651194969767112199/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1350 BracketBatch0084.bracket1351 (15437419828045467687964651194969767112199/10000000000000000000000000000000000000000) (276180962430174924490827936625949723983/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1350 BracketBatch0084.bracket1351
  (15437419828045467687964651194969767112199/10000000000000000000000000000000000000000) (276180962430174924490827936625949723983/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1350
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1351
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (15455441337033853789678847899839637494951/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15455441337033853789678847899839637494951/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (15491672739852153328645854962434715001863/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15491672739852153328645854962434715001863/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (15473557038443003559162351431137176248407/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15473557038443003559162351431137176248407/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0168.rows ScalarLogs0168.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1351 BracketBatch0084.bracket1352 (15473557038443003559162351431137176248407/10000000000000000000000000000000000000000) (554400623949370666850477636886886957889/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1351 BracketBatch0084.bracket1352
  (15473557038443003559162351431137176248407/10000000000000000000000000000000000000000) (554400623949370666850477636886886957889/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1351
