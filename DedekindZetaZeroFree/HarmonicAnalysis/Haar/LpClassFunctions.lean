module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import DedekindZetaZeroFree.MeasureTheory.Lp.MeasurePreservingEquivalences

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/MeasureTheory/Group/Conjugation.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace DedekindZetaZeroFree.TauCeti

variable {G E : Type*} [MeasurableSpace G] [NormedAddCommGroup E] {p : ℝ≥0∞} {μ : Measure G}

section DivInvMonoid

variable [DivInvMonoid G] [MeasurableMul G]

instance instMeasurableConstSMulConjAct : MeasurableConstSMul (ConjAct G) G where
  measurable_const_smul c := by
    simp only [ConjAct.smul_def]
    exact (measurable_id.const_mul _).mul_const _

instance instSMulInvariantMeasureConjAct [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] :
    SMulInvariantMeasure (ConjAct G) G μ where
  measure_preimage_smul c s hs := by
    simp only [ConjAct.smul_def]
    exact ((measurePreserving_mul_right μ (ConjAct.ofConjAct c)⁻¹).comp
      (measurePreserving_mul_left μ (ConjAct.ofConjAct c))).measure_preimage hs.nullMeasurableSet

end DivInvMonoid

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

section Group

variable [Group G] [MeasurableMul G] [SMulInvariantMeasure (ConjAct G) G μ]

def classFunctionLp (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (p : ℝ≥0∞) (μ : Measure G) [SMulInvariantMeasure (ConjAct G) G μ] :
    Submodule 𝕜 (Lp E p μ) where
  carrier := {f | ∀ c : (ConjAct G)ᵈᵐᵃ, c • f = f}
  add_mem' hf hg c := by rw [DomMulAct.smul_Lp_add, hf c, hg c]
  zero_mem' c := DomMulAct.smul_Lp_zero c
  smul_mem' a _ hf c := by rw [smul_comm, hf c]

variable {𝕜} in

@[simp]
theorem mem_classFunctionLp_iff {f : Lp E p μ} :
    f ∈ classFunctionLp 𝕜 E p μ ↔ ∀ c : (ConjAct G)ᵈᵐᵃ, c • f = f :=
  Iff.rfl

section Topology

variable [Fact (1 ≤ p)]

theorem isClosed_classFunctionLp : IsClosed (classFunctionLp 𝕜 E p μ : Set (Lp E p μ)) := by
  have : (classFunctionLp 𝕜 E p μ : Set (Lp E p μ)) =
      ⋂ c : (ConjAct G)ᵈᵐᵃ, {f : Lp E p μ | c • f = f} := by
    ext f
    simp
  rw [this]
  exact isClosed_iInter fun c ↦ isClosed_eq (continuous_const_smul c) continuous_id

instance instCompleteSpaceClassFunctionLp [CompleteSpace E] :
    CompleteSpace (classFunctionLp 𝕜 E p μ) :=
  (isClosed_classFunctionLp 𝕜).completeSpace_coe

end Topology

end Group

end DedekindZetaZeroFree.TauCeti
