import BecknerOnofri.EntropyScalarCertificate.Bessel0343
import BecknerOnofri.EntropyScalarCertificate.Bessel0344
import BecknerOnofri.EntropyScalarCertificate.Bessel0345
import BecknerOnofri.EntropyScalarCertificate.Bessel0660
import BecknerOnofri.EntropyScalarCertificate.Bessel0661
import BecknerOnofri.EntropyScalarCertificate.Brackets0137
import BecknerOnofri.EntropyScalarCertificate.Brackets0138
import BecknerOnofri.EntropyScalarCertificate.Logs0275
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2200
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (2280855997677510333132550042732074530837/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2280855997677510333132550042732074530837/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (22889667868682999162935184929425320987211/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22889667868682999162935184929425320987211/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (45698227845458102494260685356746066295581/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (45698227845458102494260685356746066295581/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2200 BracketBatch0137.bracket2201 (45698227845458102494260685356746066295581/5000000000000000000000000000000000000000) (2642999061440077926891207906891928575991/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2200 BracketBatch0137.bracket2201
  (45698227845458102494260685356746066295581/5000000000000000000000000000000000000000) (2642999061440077926891207906891928575991/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2200
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2201
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (91558671474731996651740739717701283948841/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (91558671474731996651740739717701283948841/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (3675418228498220283172649552581802234933/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3675418228498220283172649552581802234933/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (91722063593593751865528489266123169911083/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (91722063593593751865528489266123169911083/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2201 BracketBatch0137.bracket2202 (91722063593593751865528489266123169911083/10000000000000000000000000000000000000000) (165479457516055708196058594762753982537/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2201 BracketBatch0137.bracket2202
  (91722063593593751865528489266123169911083/10000000000000000000000000000000000000000) (165479457516055708196058594762753982537/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2201
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2202
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (45942727856227753539658119407272527936661/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (45942727856227753539658119407272527936661/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (92214618284103840249786866280570622805819/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (92214618284103840249786866280570622805819/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (184100073996559347329103105095115678679141/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (184100073996559347329103105095115678679141/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2202 BracketBatch0137.bracket2203 (184100073996559347329103105095115678679141/20000000000000000000000000000000000000000) (1326180965525378654913177182559265577869/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2202 BracketBatch0137.bracket2203
  (184100073996559347329103105095115678679141/20000000000000000000000000000000000000000) (1326180965525378654913177182559265577869/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2202
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2203
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (11526827285512980031223358285071327850727/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11526827285512980031223358285071327850727/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (9254618522816791365915645662712094890277/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9254618522816791365915645662712094890277/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (92380401756135876954471661453845785854293/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (92380401756135876954471661453845785854293/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2203 BracketBatch0137.bracket2204 (92380401756135876954471661453845785854293/10000000000000000000000000000000000000000) (531414205863561420472720786700349529141/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2203 BracketBatch0137.bracket2204
  (92380401756135876954471661453845785854293/10000000000000000000000000000000000000000) (531414205863561420472720786700349529141/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2203
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2204
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (92546185228167913659156456627120948902767/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (92546185228167913659156456627120948902767/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (92880182964658521238481521414863778469489/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (92880182964658521238481521414863778469489/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (5794574006025826090551186813812022730383/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5794574006025826090551186813812022730383/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2204 BracketBatch0137.bracket2205 (5794574006025826090551186813812022730383/625000000000000000000000000000000000000) (106471798264402988408470207084448825567/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2204 BracketBatch0137.bracket2205
  (5794574006025826090551186813812022730383/625000000000000000000000000000000000000) (106471798264402988408470207084448825567/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2204
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2205
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (46440091482329260619240760707431889234743/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (46440091482329260619240760707431889234743/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (11652079787764944058471463376572598459809/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11652079787764944058471463376572598459809/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (93048410633389036853126614213722283073979/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (93048410633389036853126614213722283073979/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2205 BracketBatch0137.bracket2206 (93048410633389036853126614213722283073979/10000000000000000000000000000000000000000) (2666536477333087022648663579492573102287/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2205 BracketBatch0137.bracket2206
  (93048410633389036853126614213722283073979/10000000000000000000000000000000000000000) (2666536477333087022648663579492573102287/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2205
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2206
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (93216638302119552467771707012580787678469/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (93216638302119552467771707012580787678469/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (3742223137791859432277284720768216430441/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3742223137791859432277284720768216430441/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (93386108373458019137351912515893099219747/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (93386108373458019137351912515893099219747/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2206 BracketBatch0137.bracket2207 (93386108373458019137351912515893099219747/10000000000000000000000000000000000000000) (166956050315653219280658317754032997597/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2206 BracketBatch0137.bracket2207
  (93386108373458019137351912515893099219747/10000000000000000000000000000000000000000) (166956050315653219280658317754032997597/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2206
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2207
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (46777789222398242903466059009602705380511/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (46777789222398242903466059009602705380511/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (46948515499982091036581970759154724606133/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46948515499982091036581970759154724606133/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (23431576180595083485012007442189357496661/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23431576180595083485012007442189357496661/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0275.rows ScalarLogs0275.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2207 BracketBatch0138.bracket2208 (23431576180595083485012007442189357496661/2500000000000000000000000000000000000000) (535215215787970430757908114619640028267/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2207 BracketBatch0138.bracket2208
  (23431576180595083485012007442189357496661/2500000000000000000000000000000000000000) (535215215787970430757908114619640028267/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2207
