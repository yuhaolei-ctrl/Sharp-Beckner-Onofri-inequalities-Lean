module

public import Legacy.TorusEndpoint.EndpointNormalization

@[expose] public section

/-!
# The operator-symbol normalization in the original problem

The original constant is Gamma(d/2) (4*pi)^(d/2) / 2. Here the half-power
is a real power, while the Fourier-symbol factor (2*pi)^d is the natural
power. The equalities below identify this convention with `endpointSigma`.
No numerical estimate for pi or Gamma is used.
-/

namespace Legacy.TorusEndpoint

/-- The exact constant in |nabla|^d g = c_d (delta_0 - 1). -/
noncomputable def endpointSymbolConstant (d : ℕ) : ℝ :=
  Real.Gamma ((d : ℝ) / 2) * (4 * Real.pi) ^ ((d : ℝ) / 2) / 2

theorem endpointSymbolConstant_pos {d : ℕ} (hd : 0 < d) :
    0 < endpointSymbolConstant d := by
  apply div_pos
  · apply mul_pos
    · exact Real.Gamma_pos_of_pos (div_pos (Nat.cast_pos.mpr hd) (by norm_num))
    · exact Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _
  · norm_num

private theorem endpoint_half_power_product (d : ℕ) :
    Real.pi ^ ((d : ℝ) / 2) * (4 * Real.pi) ^ ((d : ℝ) / 2) =
      (2 * Real.pi) ^ d := by
  have hbase : Real.pi * (4 * Real.pi) = (2 * Real.pi) ^ (2 : ℕ) := by ring
  calc
    _ = (Real.pi * (4 * Real.pi)) ^ ((d : ℝ) / 2) :=
      (Real.mul_rpow Real.pi_pos.le (mul_nonneg (by norm_num) Real.pi_pos.le)).symm
    _ = ((2 * Real.pi) ^ (2 : ℕ)) ^ ((d : ℝ) / 2) := by rw [hbase]
    _ = (2 * Real.pi) ^ ((2 : ℝ) * ((d : ℝ) / 2)) := by
      rw [← Real.rpow_natCast (2 * Real.pi) 2,
        ← Real.rpow_mul (mul_nonneg (by norm_num) Real.pi_pos.le)]
      norm_num
    _ = (2 * Real.pi) ^ (d : ℝ) := by congr 1; ring
    _ = (2 * Real.pi) ^ d := Real.rpow_natCast _ _

/-- Multiplying the sphere-area convention by the original symbol constant
recovers the natural Fourier-symbol power exactly. -/
theorem endpointSymbolConstant_mul_sigma {d : ℕ} (hd : 0 < d) :
    endpointSymbolConstant d * endpointSigma d = (2 * Real.pi) ^ d := by
  have hgamma : Real.Gamma ((d : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (div_pos (Nat.cast_pos.mpr hd) (by norm_num))).ne'
  calc
    _ = Real.pi ^ ((d : ℝ) / 2) * (4 * Real.pi) ^ ((d : ℝ) / 2) := by
      unfold endpointSymbolConstant endpointSigma
      field_simp
    _ = _ := endpoint_half_power_product d

/-- The original problem's sigma = (2*pi)^d / c_d agrees with the exact
sigma already used by the endpoint normalization module. -/
theorem endpointSigma_from_symbol {d : ℕ} (hd : 0 < d) :
    endpointSigma d = (2 * Real.pi) ^ d / endpointSymbolConstant d := by
  apply (eq_div_iff (endpointSymbolConstant_pos hd).ne').mpr
  rw [mul_comm]
  exact endpointSymbolConstant_mul_sigma hd

end Legacy.TorusEndpoint
