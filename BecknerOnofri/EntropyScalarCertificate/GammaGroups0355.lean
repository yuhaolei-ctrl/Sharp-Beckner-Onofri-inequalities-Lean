import BecknerOnofri.EntropyScalarCertificate.Bessel0443
import BecknerOnofri.EntropyScalarCertificate.Bessel0444
import BecknerOnofri.EntropyScalarCertificate.Bessel0445
import BecknerOnofri.EntropyScalarCertificate.Bessel0710
import BecknerOnofri.EntropyScalarCertificate.Bessel0711
import BecknerOnofri.EntropyScalarCertificate.Brackets0177
import BecknerOnofri.EntropyScalarCertificate.Brackets0178
import BecknerOnofri.EntropyScalarCertificate.Logs0355
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2840
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (205168953419390663847837166794323980136311/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (205168953419390663847837166794323980136311/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (64246789927889770113791463855446887098477/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (64246789927889770113791463855446887098477/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (2053793405943189641059849255658770094257187/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2053793405943189641059849255658770094257187/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2840 BracketBatch0177.bracket2841 (2053793405943189641059849255658770094257187/20000000000000000000000000000000000000000) (246110764939610322850310483445188157037/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2840 BracketBatch0177.bracket2841
  (2053793405943189641059849255658770094257187/20000000000000000000000000000000000000000) (246110764939610322850310483445188157037/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2840
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2841
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1027948638846236321820663421687150193575629/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1027948638846236321820663421687150193575629/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1030061168543250362088191604126921062645619/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1030061168543250362088191604126921062645619/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (32156403240460729436075859778344863378457/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (32156403240460729436075859778344863378457/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2841 BracketBatch0177.bracket2842 (32156403240460729436075859778344863378457/312500000000000000000000000000000000000) (1231184664826965371725908830264257245821/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2841 BracketBatch0177.bracket2842
  (32156403240460729436075859778344863378457/312500000000000000000000000000000000000) (1231184664826965371725908830264257245821/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2841
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2842
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (64378823033953147630511975257932566415351/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (64378823033953147630511975257932566415351/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (516091204871154899291328282008066497650941/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (516091204871154899291328282008066497650941/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (1031121789142780080335424084071527028973749/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1031121789142780080335424084071527028973749/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2842 BracketBatch0177.bracket2843 (1031121789142780080335424084071527028973749/10000000000000000000000000000000000000000) (6159084074139551051105310112619274459453/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2842 BracketBatch0177.bracket2843
  (1031121789142780080335424084071527028973749/10000000000000000000000000000000000000000) (6159084074139551051105310112619274459453/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2842
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2843
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1032182409742309798582656564016132995301879/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1032182409742309798582656564016132995301879/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (129289052055040828660746556004230403285207/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (129289052055040828660746556004230403285207/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (413298965236527285573725802409995244316707/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (413298965236527285573725802409995244316707/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2843 BracketBatch0177.bracket2844 (413298965236527285573725802409995244316707/4000000000000000000000000000000000000000) (1540562849840965864525637386727680883559/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2843 BracketBatch0177.bracket2844
  (413298965236527285573725802409995244316707/4000000000000000000000000000000000000000) (1540562849840965864525637386727680883559/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2843
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2844
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1034312416440326629285972448033843226281653/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1034312416440326629285972448033843226281653/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (518225621540696123861470411103703793069361/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (518225621540696123861470411103703793069361/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (16566109276173751016071306161930006499363/160000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16566109276173751016071306161930006499363/160000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2844 BracketBatch0177.bracket2845 (16566109276173751016071306161930006499363/160000000000000000000000000000000000000) (616542532581508700737060294381815982731/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2844 BracketBatch0177.bracket2845
  (16566109276173751016071306161930006499363/160000000000000000000000000000000000000) (616542532581508700737060294381815982731/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2844
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2845
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1036451243081392247722940822207407586138719/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1036451243081392247722940822207407586138719/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (207719788912283246674286406400056420706359/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (207719788912283246674286406400056420706359/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (1037525093821404240547186427103844844835257/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1037525093821404240547186427103844844835257/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2845 BracketBatch0177.bracket2846 (1037525093821404240547186427103844844835257/10000000000000000000000000000000000000000) (6168605879649507202015661847250427134827/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2845 BracketBatch0177.bracket2846
  (1037525093821404240547186427103844844835257/10000000000000000000000000000000000000000) (6168605879649507202015661847250427134827/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2845
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2846
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (64912434035088514585714502000017631470737/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (64912434035088514585714502000017631470737/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (32523611757275718950062734277827903041507/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (32523611757275718950062734277827903041507/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (129959657549639952485839970555673437553751/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (129959657549639952485839970555673437553751/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2846 BracketBatch0177.bracket2847 (129959657549639952485839970555673437553751/1250000000000000000000000000000000000000) (617179308717345352519392009945608812377/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2846 BracketBatch0177.bracket2847
  (129959657549639952485839970555673437553751/1250000000000000000000000000000000000000) (617179308717345352519392009945608812377/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2846
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2847
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1040755576232823006402007496890492897328221/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1040755576232823006402007496890492897328221/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1042921193909307190601787286400371619721651/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1042921193909307190601787286400371619721651/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0711.rows BesselBatch0711.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (130229798133883137312737173955679032315617/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (130229798133883137312737173955679032315617/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0355.rows ScalarLogs0355.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2847 BracketBatch0178.bracket2848 (130229798133883137312737173955679032315617/1250000000000000000000000000000000000000) (6174986974844389868382369185913022284319/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2847 BracketBatch0178.bracket2848
  (130229798133883137312737173955679032315617/1250000000000000000000000000000000000000) (6174986974844389868382369185913022284319/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2847
