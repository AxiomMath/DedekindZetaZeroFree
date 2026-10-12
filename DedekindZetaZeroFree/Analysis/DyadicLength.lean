module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DyadicColumns.lean.
-/

namespace DedekindZetaZeroFree.LargeSieve.Vendor

noncomputable def dyadicLength (X : ℝ) : ℕ := ⌈Real.log X / Real.log 2⌉₊

end DedekindZetaZeroFree.LargeSieve.Vendor
