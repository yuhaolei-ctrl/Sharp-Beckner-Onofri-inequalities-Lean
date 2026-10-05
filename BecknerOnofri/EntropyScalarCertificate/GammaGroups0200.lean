module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0250
public import BecknerOnofri.EntropyScalarCertificate.Bessel0251
public import BecknerOnofri.EntropyScalarCertificate.Bessel0613
public import BecknerOnofri.EntropyScalarCertificate.Bessel0614
public import BecknerOnofri.EntropyScalarCertificate.Brackets0100
public import BecknerOnofri.EntropyScalarCertificate.Logs0200
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1600
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (582559221029264939311504220341145037163/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (582559221029264939311504220341145037163/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (9326484244329336898903499407731524791107/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9326484244329336898903499407731524791107/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (3729486356159515185577513386637969077143/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3729486356159515185577513386637969077143/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1600 BracketBatch0100.bracket1601 (3729486356159515185577513386637969077143/2000000000000000000000000000000000000000) (730740975948514544994844850743111516003/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1600 BracketBatch0100.bracket1601
  (3729486356159515185577513386637969077143/2000000000000000000000000000000000000000) (730740975948514544994844850743111516003/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1600
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1601
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (18652968488658673797806998815463049582211/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18652968488658673797806998815463049582211/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (18664057018406700029686225432753342451091/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18664057018406700029686225432753342451091/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (18658512753532686913746612124108196016651/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18658512753532686913746612124108196016651/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1601 BracketBatch0100.bracket1602 (18658512753532686913746612124108196016651/10000000000000000000000000000000000000000) (731327513358292839034730982150270828247/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1601 BracketBatch0100.bracket1602
  (18658512753532686913746612124108196016651/10000000000000000000000000000000000000000) (731327513358292839034730982150270828247/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1601
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1602
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1166503563650418751855389089547083903193/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1166503563650418751855389089547083903193/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (9337580347342254757191920848226362932149/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9337580347342254757191920848226362932149/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (18669608856545604772035033564603034157693/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18669608856545604772035033564603034157693/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1602 BracketBatch0100.bracket1603 (18669608856545604772035033564603034157693/10000000000000000000000000000000000000000) (731914688317600692902088088466665701649/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1602 BracketBatch0100.bracket1603
  (18669608856545604772035033564603034157693/10000000000000000000000000000000000000000) (731914688317600692902088088466665701649/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1602
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1603
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (3735032138936901902876768339290545172859/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3735032138936901902876768339290545172859/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (18686279550085047311537356061833136332863/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18686279550085047311537356061833136332863/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (18680720122384778412960598879142931098579/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18680720122384778412960598879142931098579/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1603 BracketBatch0100.bracket1604 (18680720122384778412960598879142931098579/10000000000000000000000000000000000000000) (732502501825510240733315802991488165549/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1603 BracketBatch0100.bracket1604
  (18680720122384778412960598879142931098579/10000000000000000000000000000000000000000) (732502501825510240733315802991488165549/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1603
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1604
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (934313977504252365576867803091656816643/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (934313977504252365576867803091656816643/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (18697413617290542812901100074509003169437/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18697413617290542812901100074509003169437/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (37383693167375590124438456136342139502297/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37383693167375590124438456136342139502297/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1604 BracketBatch0100.bracket1605 (37383693167375590124438456136342139502297/20000000000000000000000000000000000000000) (733090954882987928290315796820901132949/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1604 BracketBatch0100.bracket1605
  (37383693167375590124438456136342139502297/20000000000000000000000000000000000000000) (733090954882987928290315796820901132949/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1604
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1605
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (9348706808645271406450550037254501584717/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9348706808645271406450550037254501584717/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (9354281464536401455726264652311891264847/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9354281464536401455726264652311891264847/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (4675747068295418215544203672391598212391/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4675747068295418215544203672391598212391/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1605 BracketBatch0100.bracket1606 (4675747068295418215544203672391598212391/2500000000000000000000000000000000000000) (146736009698579667829244252677214270147/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1605 BracketBatch0100.bracket1606
  (4675747068295418215544203672391598212391/2500000000000000000000000000000000000000) (146736009698579667829244252677214270147/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1605
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1606
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (18708562929072802911452529304623782529691/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18708562929072802911452529304623782529691/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (4679931879573376577912888485550479440371/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4679931879573376577912888485550479440371/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (1497131617894652368924163329873028011647/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1497131617894652368924163329873028011647/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1606 BracketBatch0100.bracket1607 (1497131617894652368924163329873028011647/800000000000000000000000000000000000000) (734269783660008030259092599129474272373/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1606 BracketBatch0100.bracket1607
  (1497131617894652368924163329873028011647/800000000000000000000000000000000000000) (734269783660008030259092599129474272373/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1606
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1607
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (18719727518293506311651553942201917761481/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18719727518293506311651553942201917761481/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (4682726854476124746546699119521865561977/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4682726854476124746546699119521865561977/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (37450634936198005297838350420289380009389/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37450634936198005297838350420289380009389/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0200.rows ScalarLogs0200.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1607 BracketBatch0100.bracket1608 (37450634936198005297838350420289380009389/20000000000000000000000000000000000000000) (367430080695494688489508421769260194089/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1607 BracketBatch0100.bracket1608
  (37450634936198005297838350420289380009389/20000000000000000000000000000000000000000) (367430080695494688489508421769260194089/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1607
