/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module

public import Mathlib.Topology.Algebra.StarSubalgebra
public import DedekindZetaZeroFree.RepresentationTheory.Compact.ApproximateIdentity
public import DedekindZetaZeroFree.RepresentationTheory.Compact.EigenspaceRepresentation

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/Compact/RepresentativeDensity.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: retain only the generic compact-group density slice; adapt imports and visibility.
The selected declarations are adapted to the current module interface.
License: repository root LICENSE (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Set

namespace DedekindZetaZeroFree.TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

variable (𝕜 G) in

theorem dense_representativeSubmodule : Dense (representativeSubmodule 𝕜 G : Set C(G, 𝕜)) := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  intro f
  rw [← closure_closure (s := (representativeSubmodule 𝕜 G : Set C(G, 𝕜)))]
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨k, hk, hle⟩ :=
    exists_isMollifier_norm_convolutionCLM_toLp_sub_le 𝕜 f (half_pos hε) Filter.univ_mem
  refine ⟨convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f),
    convolutionCLM_mem_closure_representativeSubmodule k hk.inv_apply_eq_conj _, ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact hle.trans_lt (half_lt_self hε)

end CompactGroup

end DedekindZetaZeroFree.TauCeti
