/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactProbabilityMeasure
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.UnitaryActions
public import DedekindZetaZeroFree.MeasureTheory.Lp.MeasurePreservingEquivalences
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/Compact/RegularRepresentation.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: retain only the generic compact-group density slice; adapt imports and visibility.
The selected declarations are adapted to the current module interface.
License: repository root LICENSE (Apache-2.0).
-/

@[expose] public section

open MeasureTheory

namespace DedekindZetaZeroFree.TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (𝕜 G) in

noncomputable def rightRegularLp : ContRepresentation 𝕜 G (Lp 𝕜 2 (haarProb G)) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (· * g)
        (measurePreserving_mul_right (haarProb G) g)).toContinuousLinearMap

      map_one' := ContinuousLinearMap.ext fun x => one_smul (MulOpposite G)ᵈᵐᵃ x
      map_mul' g h := ContinuousLinearMap.ext fun x => by
        have hfun : (fun y : G => y * (g * h)) = (fun y : G => y * h) ∘ (fun y : G => y * g) :=
          funext fun y => (mul_assoc y g h).symm
        simp only [mul_apply_eq_comp, hfun]
        exact Lp.compMeasurePreserving_comp_apply x (measurePreserving_mul_right (haarProb G) h)
          (measurePreserving_mul_right (haarProb G) g) }

theorem rightRegularLp_apply (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    rightRegularLp 𝕜 G g f
      = Lp.compMeasurePreserving (· * g) (measurePreserving_mul_right (haarProb G) g) f :=
  (rfl)

theorem continuous_rightRegularLp_apply (f : Lp 𝕜 2 (haarProb G)) :
    Continuous fun g : G => rightRegularLp 𝕜 G g f := by
  have hg : Continuous fun g : G => ContinuousMap.mulRight (X := G) g :=
    (ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, continuous_snd.mul continuous_fst⟩).continuous
  simp only [rightRegularLp_apply]
  exact continuous_const.compMeasurePreservingLp hg _ (by simp)

end CompactGroup

end DedekindZetaZeroFree.TauCeti
