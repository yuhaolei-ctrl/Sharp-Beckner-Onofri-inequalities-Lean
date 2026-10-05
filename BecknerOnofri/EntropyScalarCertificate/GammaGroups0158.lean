module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0197
public import BecknerOnofri.EntropyScalarCertificate.Bessel0198
public import BecknerOnofri.EntropyScalarCertificate.Bessel0587
public import BecknerOnofri.EntropyScalarCertificate.Bessel0588
public import BecknerOnofri.EntropyScalarCertificate.Brackets0079
public import BecknerOnofri.EntropyScalarCertificate.Logs0158
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1264
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (11683347660211505469812701426206570971023/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11683347660211505469812701426206570971023/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (5861865116732906210144282104296363851827/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5861865116732906210144282104296363851827/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (23407077893677317890101265634799298674677/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23407077893677317890101265634799298674677/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1264 BracketBatch0079.bracket1265 (23407077893677317890101265634799298674677/20000000000000000000000000000000000000000) (336257840000469518445797742913070147391/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1264 BracketBatch0079.bracket1265
  (23407077893677317890101265634799298674677/20000000000000000000000000000000000000000) (336257840000469518445797742913070147391/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1264
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1265
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (11723730233465812420288564208592727703651/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11723730233465812420288564208592727703651/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (11764381859950534320911227098881681844051/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11764381859950534320911227098881681844051/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (11744056046708173370599895653737204773851/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11744056046708173370599895653737204773851/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1265 BracketBatch0079.bracket1266 (11744056046708173370599895653737204773851/10000000000000000000000000000000000000000) (13543061835798303912582098302311552499/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1265 BracketBatch0079.bracket1266
  (11744056046708173370599895653737204773851/10000000000000000000000000000000000000000) (13543061835798303912582098302311552499/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1265
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1266
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (735273866246908395056951693680105115253/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (735273866246908395056951693680105115253/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (5902652964299304147867623250588966857951/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5902652964299304147867623250588966857951/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (471393755770982852332929472001192311199/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (471393755770982852332929472001192311199/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1266 BracketBatch0079.bracket1267 (471393755770982852332929472001192311199/400000000000000000000000000000000000000) (85227973393276190741797543829962603801/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1266 BracketBatch0079.bracket1267
  (471393755770982852332929472001192311199/400000000000000000000000000000000000000) (85227973393276190741797543829962603801/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1266
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1267
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (11805305928598608295735246501177933715899/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11805305928598608295735246501177933715899/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (11846505886542151923501104787247597831493/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11846505886542151923501104787247597831493/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (92389889902893594606391997220412232607/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (92389889902893594606391997220412232607/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1267 BracketBatch0079.bracket1268 (92389889902893594606391997220412232607/78125000000000000000000000000000000000) (343264044146176861201815306995546409723/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1267 BracketBatch0079.bracket1268
  (92389889902893594606391997220412232607/78125000000000000000000000000000000000) (343264044146176861201815306995546409723/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1267
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1268
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1184650588654215192350110478724759783149/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1184650588654215192350110478724759783149/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (5943992620179041468003637987366761864387/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5943992620179041468003637987366761864387/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (2966811390862529357438547595247640195033/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2966811390862529357438547595247640195033/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1268 BracketBatch0079.bracket1269 (2966811390862529357438547595247640195033/2500000000000000000000000000000000000000) (13825326443044343890069921497814268973/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1268 BracketBatch0079.bracket1269
  (2966811390862529357438547595247640195033/2500000000000000000000000000000000000000) (13825326443044343890069921497814268973/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1268
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1269
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (11887985240358082936007275974733523728771/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11887985240358082936007275974733523728771/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1192974755734516537612606442451828531037/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1192974755734516537612606442451828531037/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (23817732797703248312133340399251809039141/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23817732797703248312133340399251809039141/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1269 BracketBatch0079.bracket1270 (23817732797703248312133340399251809039141/20000000000000000000000000000000000000000) (174009705109913281696427112677977242327/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1269 BracketBatch0079.bracket1270
  (23817732797703248312133340399251809039141/20000000000000000000000000000000000000000) (174009705109913281696427112677977242327/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1269
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1270
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (11929747557345165376126064424518285310367/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11929747557345165376126064424518285310367/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (149647455835417306784931720157780517719/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (149647455835417306784931720157780517719/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (23901544024178549918920602037140726727887/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23901544024178549918920602037140726727887/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1270 BracketBatch0079.bracket1271 (23901544024178549918920602037140726727887/20000000000000000000000000000000000000000) (350422959874513808122166054925212176429/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1270 BracketBatch0079.bracket1271
  (23901544024178549918920602037140726727887/20000000000000000000000000000000000000000) (350422959874513808122166054925212176429/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1270
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1271
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (11971796466833384542794537612622441417517/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11971796466833384542794537612622441417517/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (600706783076329091387296409213757587473/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (600706783076329091387296409213757587473/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (23985932128359966370540465796897593166977/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23985932128359966370540465796897593166977/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0158.rows ScalarLogs0158.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1271 BracketBatch0079.bracket1272 (23985932128359966370540465796897593166977/20000000000000000000000000000000000000000) (44105497602979590825317392412801388523/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1271 BracketBatch0079.bracket1272
  (23985932128359966370540465796897593166977/20000000000000000000000000000000000000000) (44105497602979590825317392412801388523/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1271
