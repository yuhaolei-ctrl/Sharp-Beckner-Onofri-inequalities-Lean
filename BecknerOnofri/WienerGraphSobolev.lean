import BecknerOnofri.WienerGraphNorm
import BecknerOnofri.LocalElevenCore.GraphAllSobolevBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousGibbs ContinuousFirstShell

lemma inSobolev {d m : ℕ} {s : ℝ} (hs : s≤(m:ℝ)) (x : graph d m) :
    InSobolev s (toContinuous d m x) :=
  LocalEleven.GraphAllSobolevBounds.inSobolev_of_wiener hs _ (toContinuous_radial x)

def sobolevValue {d m : ℕ} {s : ℝ} (hs : s≤(m:ℝ)) (x : graph d m) : FourierL2 d :=
  encodeSobolev (toContinuous d m x) (inSobolev hs x)

lemma sobolevValue_apply {d m : ℕ} {s : ℝ} (hs : s≤(m:ℝ)) (x : graph d m) (k : Frequency d) :
    sobolevValue hs x k=(sobolevScale s k : ℂ)*coefficient k (toContinuous d m x) := by
  change scaledFourier s (toContinuous d m x) k=_
  rw [scaledFourier,coefficient_eq_fourierCoeff]

/-- A bounded linear embedding into the exact physical weighted Fourier l2
encoding of H^s. This will transport analytic Wiener-space graphs to H^s. -/
def toSobolev {d m : ℕ} {s : ℝ} (hs : s≤(m:ℝ)) : graph d m →L[ℝ] FourierL2 d :=
  LinearMap.mkContinuous
    { toFun := sobolevValue hs
      map_add' := fun x y => by
        apply lp.ext
        funext k
        simp only [lp.coeFn_add,Pi.add_apply,sobolevValue_apply,map_add,mul_add]
      map_smul' := fun c x => by
        apply lp.ext
        funext k
        simp only [lp.coeFn_smul,Pi.smul_apply,sobolevValue_apply,map_smul,
          RingHom.id_apply,Complex.real_smul]
        ring }
    ((1+2*Real.pi)^m) (fun x => by
      change ‖sobolevValue hs x‖≤((1+2*Real.pi)^m)*‖x‖
      rw [sobolevValue,encodeSobolev_norm,norm_eq_wienerSize]
      exact LocalEleven.GraphAllSobolevBounds.sobolevNorm_le_wiener hs _ (toContinuous_radial x))

@[simp] theorem toSobolev_apply {d m : ℕ} {s : ℝ} (hs : s≤(m:ℝ)) (x : graph d m) (k : Frequency d) :
    toSobolev hs x k=(sobolevScale s k : ℂ)*fourierCoeff (toContinuous d m x) k := by
  change sobolevValue hs x k=_
  rw [sobolevValue_apply,coefficient_eq_fourierCoeff]

#print axioms toSobolev_apply
end BecknerOnofri.HighDim.WienerGraph
