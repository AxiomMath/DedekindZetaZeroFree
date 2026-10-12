module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalExceptionalParameter

open KPGlobalEisensteinData
open scoped NNReal

def realLogPower (r : ℝ) (u : ℂ) : ℂ :=
  Complex.exp (u * (Real.log r : ℂ))

end DedekindZetaZeroFree.KPGlobalExceptionalParameter

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalExceptionalParameter

open KPGlobalEisensteinData
open scoped NNReal

def sourceExponent (s : ℂ) : ℂ := 2 / 3 + s

def weylExponent (s : ℂ) : ℂ := 1 / 3 - s

theorem source_multiplier (r : ℝ) (hr : 0 < r) (s : ℂ) :
    realLogPower r (1 / 2) * realLogPower r (1 / 6) * realLogPower r s =
      realLogPower r (sourceExponent s) := by
  unfold realLogPower sourceExponent
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

end DedekindZetaZeroFree.KPGlobalExceptionalParameter

end
end
