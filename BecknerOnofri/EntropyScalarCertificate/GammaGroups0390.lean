module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0487
public import BecknerOnofri.EntropyScalarCertificate.Bessel0488
public import BecknerOnofri.EntropyScalarCertificate.Bessel0732
public import BecknerOnofri.EntropyScalarCertificate.Bessel0733
public import BecknerOnofri.EntropyScalarCertificate.Brackets0195
public import BecknerOnofri.EntropyScalarCertificate.Logs0390
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3120
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (150318631808485245223963323000527348018883/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (150318631808485245223963323000527348018883/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1208355441431881468717219332851047385385941/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1208355441431881468717219332851047385385941/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (482180899179952686101785183371053233907401/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (482180899179952686101785183371053233907401/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0195.bracket3120 BracketBatch0195.bracket3121 (482180899179952686101785183371053233907401/2000000000000000000000000000000000000000) (297744801091789811606665712069918421313/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0195.bracket3120 BracketBatch0195.bracket3121
  (482180899179952686101785183371053233907401/2000000000000000000000000000000000000000) (297744801091789811606665712069918421313/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3120
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3121
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (2416710882863762937434438665702094770771879/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2416710882863762937434438665702094770771879/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (607109100565358775717205249367135935404137/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (607109100565358775717205249367135935404137/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (4845147285125198040303259663170638512388427/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4845147285125198040303259663170638512388427/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0195.bracket3121 BracketBatch0195.bracket3122 (4845147285125198040303259663170638512388427/20000000000000000000000000000000000000000) (3725268268796523858455300796828621587629/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0195.bracket3121 BracketBatch0195.bracket3122
  (4845147285125198040303259663170638512388427/20000000000000000000000000000000000000000) (3725268268796523858455300796828621587629/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3121
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3122
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (485687280452287020573764199493708748323309/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (485687280452287020573764199493708748323309/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (244027631706247947084633366813079006367443/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (244027631706247947084633366813079006367443/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (194748508772956582948606186623973352211639/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (194748508772956582948606186623973352211639/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0195.bracket3122 BracketBatch0195.bracket3123 (194748508772956582948606186623973352211639/800000000000000000000000000000000000000) (932184642942078899738120279624147288471/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0195.bracket3122 BracketBatch0195.bracket3123
  (194748508772956582948606186623973352211639/800000000000000000000000000000000000000) (932184642942078899738120279624147288471/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3122
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3123
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (2440276317062479470846333668130790063674427/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2440276317062479470846333668130790063674427/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (2452232309552236250450364861070985519892507/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2452232309552236250450364861070985519892507/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (2446254313307357860648349264600887791783467/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2446254313307357860648349264600887791783467/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0195.bracket3123 BracketBatch0195.bracket3124 (2446254313307357860648349264600887791783467/10000000000000000000000000000000000000000) (1866110472227057850685884790436865459071/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0195.bracket3123 BracketBatch0195.bracket3124
  (2446254313307357860648349264600887791783467/10000000000000000000000000000000000000000) (1866110472227057850685884790436865459071/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3123
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3124
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (306529038694029531306295607633873189986563/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (306529038694029531306295607633873189986563/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (2464306095164525261058416993429074283671071/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2464306095164525261058416993429074283671071/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (196661536188670460460351274180002392142543/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (196661536188670460460351274180002392142543/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0195.bracket3124 BracketBatch0195.bracket3125 (196661536188670460460351274180002392142543/800000000000000000000000000000000000000) (7471430813512121870127712705210326810887/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0195.bracket3124 BracketBatch0195.bracket3125
  (196661536188670460460351274180002392142543/800000000000000000000000000000000000000) (7471430813512121870127712705210326810887/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3124
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3125
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (616076523791131315264604248357268570917767/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (616076523791131315264604248357268570917767/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1238249711651076426694478874680546177348057/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1238249711651076426694478874680546177348057/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (2470402759233339057223687371395083319183591/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2470402759233339057223687371395083319183591/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0195.bracket3125 BracketBatch0195.bracket3126 (2470402759233339057223687371395083319183591/10000000000000000000000000000000000000000) (7478443952960448617183173252673440404253/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0195.bracket3125 BracketBatch0195.bracket3126
  (2470402759233339057223687371395083319183591/10000000000000000000000000000000000000000) (7478443952960448617183173252673440404253/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3125
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3126
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (2476499423302152853388957749361092354696111/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2476499423302152853388957749361092354696111/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (2488814078181911574460117418949662818479923/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2488814078181911574460117418949662818479923/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (2482656750742032213924537584155377586588017/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2482656750742032213924537584155377586588017/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0195.bracket3126 BracketBatch0195.bracket3127 (2482656750742032213924537584155377586588017/10000000000000000000000000000000000000000) (3742740669224807889187394355761628003321/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0195.bracket3126 BracketBatch0195.bracket3127
  (2482656750742032213924537584155377586588017/10000000000000000000000000000000000000000) (3742740669224807889187394355761628003321/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3126
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3127
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (31110175977273894680751467736870785230999/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31110175977273894680751467736870785230999/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (625312969926232455624286790865732935476621/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (625312969926232455624286790865732935476621/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0733.rows BesselBatch0733.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (1247516489471710349239316145603148640096601/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1247516489471710349239316145603148640096601/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0390.rows ScalarLogs0390.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0195.bracket3127 BracketBatch0195.bracket3128 (1247516489471710349239316145603148640096601/5000000000000000000000000000000000000000) (299701719861049613747860551842644551723/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0195.bracket3127 BracketBatch0195.bracket3128
  (1247516489471710349239316145603148640096601/5000000000000000000000000000000000000000) (299701719861049613747860551842644551723/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3127
