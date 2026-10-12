module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.MaximalTorus

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/Borel.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

noncomputable instance : MeasurableSpace SU2 := borel SU2

instance : BorelSpace SU2 := ⟨rfl⟩

end SU2

end DedekindZetaZeroFree.TauCeti
