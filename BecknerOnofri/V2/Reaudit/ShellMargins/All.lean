module

public import BecknerOnofri.V2.Reaudit.ShellMargins.Theta
public import BecknerOnofri.V2.Reaudit.ShellMargins.TwoDim
public import BecknerOnofri.V2.Reaudit.ShellMargins.Checks
public import BecknerOnofri.V2.Reaudit.ShellMargins.RetainedShell

@[expose] public section

/-! # ShellMargins: umbrella module

* `Theta` (row S022): `lem:theta-integral-certificate`, claim by claim.
* `TwoDim` (row S020): `eq:reaudit-S020-two-central`, `eq:dimension-two-large` (`n ≥ 4`).
* `Checks`, `RetainedShell` (rows S020, S030): the retained-shell certificate with margins `4/25`
  (171 pairs) and `111/200000` (`d = 11`, `n = 1..21`). -/
