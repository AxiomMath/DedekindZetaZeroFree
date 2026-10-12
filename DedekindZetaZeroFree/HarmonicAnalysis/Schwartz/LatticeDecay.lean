module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Module.ZLattice.Summable

@[expose] public section

noncomputable section

open Module

namespace DedekindZetaZeroFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def schwartzLatticeTranslate (L : Submodule ℤ E) (f : SchwartzMap E ℂ)
    (ℓ : L) : C(E, ℂ) :=
  ⟨fun x => f (x + (ℓ : E)),
    f.continuous.comp (continuous_id.add continuous_const)⟩

theorem schwartzLatticeDecay (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (f : SchwartzMap E ℂ)
    (C : TopologicalSpace.Compacts E) :
    Summable (fun ℓ : L => ‖(schwartzLatticeTranslate L f ℓ).restrict C‖) := by
  classical
  let k := Module.finrank ℤ L + 1
  obtain ⟨D, hD, hdecay⟩ := f.decay k 0
  have hdecay' (y : E) : ‖y‖ ^ k * ‖f y‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_zero] using hdecay y
  let R := ‖(ContinuousMap.id E).restrict C‖
  have hR : 0 ≤ R := norm_nonneg _
  have hx (x : C) : ‖(x : E)‖ ≤ R :=
    ContinuousMap.norm_coe_le_norm ((ContinuousMap.id E).restrict C) x
  have hfinite : {ℓ : L | ‖(ℓ : E)‖ ≤ 2 * R + 1}.Finite := by
    have hclosed : IsClosed (L : Set E) := L.toAddSubgroup.isClosed_of_discreteTopology
    have hf := (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (Metric.isBounded_closedBall (x := (0 : E)) (r := 2 * R + 1)) hclosed).preimage_embedding
        (Function.Embedding.subtype (fun x : E => x ∈ L))
    convert hf using 1
    ext ℓ
    simp [Metric.mem_closedBall, dist_zero_right]
  have hbase := ZLattice.summable_norm_pow_inv L k (by dsimp [k]; omega)
  refine (hbase.mul_left (D * 2 ^ k)).of_norm_bounded_eventually ?_
  refine hfinite.subset ?_
  intro ℓ hℓ
  by_contra hnot
  have hl : 2 * R + 1 < ‖(ℓ : E)‖ := lt_of_not_ge hnot
  have hlpos : 0 < ‖(ℓ : E)‖ := by linarith
  have hbound : ‖(schwartzLatticeTranslate L f ℓ).restrict C‖ ≤
      D * 2 ^ k * (‖(ℓ : E)‖⁻¹ ^ k) := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro x
    change ‖f ((x : E) + (ℓ : E))‖ ≤ _
    have hnorm : ‖(ℓ : E)‖ ≤ 2 * ‖(x : E) + (ℓ : E)‖ := by
      have ht := norm_add_le (-(x : E)) ((x : E) + (ℓ : E))
      simp only [neg_add_cancel_left, norm_neg] at ht
      have := hx x
      linarith
    have hpow : ‖(ℓ : E)‖ ^ k ≤ 2 ^ k * ‖(x : E) + (ℓ : E)‖ ^ k := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm k
    have hh := mul_le_mul_of_nonneg_right hpow (norm_nonneg (f ((x : E) + (ℓ : E))))
    have hh' := mul_le_mul_of_nonneg_left (hdecay' ((x : E) + (ℓ : E)))
      (show (0 : ℝ) ≤ 2 ^ k by positivity)
    have hprod : ‖(ℓ : E)‖ ^ k * ‖f ((x : E) + (ℓ : E))‖ ≤ D * 2 ^ k := by
      calc
        _ ≤ (2 ^ k * ‖(x : E) + (ℓ : E)‖ ^ k) * ‖f ((x : E) + (ℓ : E))‖ := hh
        _ ≤ D * 2 ^ k := by nlinarith [hh']
    calc
      ‖f ((x : E) + (ℓ : E))‖ =
          (‖(ℓ : E)‖ ^ k * ‖f ((x : E) + (ℓ : E))‖) * (‖(ℓ : E)‖⁻¹ ^ k) := by
            rw [inv_pow]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (by positivity)
  apply hℓ
  change ‖‖(schwartzLatticeTranslate L f ℓ).restrict C‖‖ ≤ D * 2 ^ k * ‖ℓ‖⁻¹ ^ k
  simpa only [Real.norm_of_nonneg (norm_nonneg _), Submodule.norm_coe] using hbound

theorem schwartzLatticeDecay_pointwise (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (f : SchwartzMap E ℂ) (z : E) :
    Summable (fun ℓ : L => ‖f (z + (ℓ : E))‖) := by
  let C : TopologicalSpace.Compacts E := ⟨{z}, isCompact_singleton⟩
  apply (schwartzLatticeDecay L f C).of_norm_bounded
  intro ℓ
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact ContinuousMap.norm_coe_le_norm ((schwartzLatticeTranslate L f ℓ).restrict C)
    ⟨z, Set.mem_singleton z⟩

variable {ι : Type*} [Fintype ι]

def coordinateSchwartzTranslate (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (f : SchwartzMap E ℂ) (n : ι → ℤ) : C(ι → ℝ, ℂ) := by
  let B := LinearEquiv.toContinuousLinearEquiv
    (b.ofZLatticeBasis ℝ L).equivFun.symm
  exact ⟨fun x => f (B (x + fun i => (n i : ℝ))),
    f.continuous.comp (B.continuous.comp (continuous_id.add continuous_const))⟩

theorem schwartzLatticeDecay_coordinates (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (f : SchwartzMap E ℂ) (C : TopologicalSpace.Compacts (ι → ℝ)) :
    Summable (fun n : ι → ℤ => ‖(coordinateSchwartzTranslate L b f n).restrict C‖) := by
  classical
  let B := LinearEquiv.toContinuousLinearEquiv
    (b.ofZLatticeBasis ℝ L).equivFun.symm
  let K : TopologicalSpace.Compacts E := C.map B B.continuous
  have hcast (n : ι → ℤ) : B (fun i => (n i : ℝ)) = (b.equivFun.symm n : E) := by
    apply (b.ofZLatticeBasis ℝ L).equivFun.injective
    ext i
    change (b.ofZLatticeBasis ℝ L).equivFun
      ((b.ofZLatticeBasis ℝ L).equivFun.symm (fun i => (n i : ℝ))) i = _
    rw [LinearEquiv.apply_symm_apply]
    change (n i : ℝ) = (b.ofZLatticeBasis ℝ L).repr (b.equivFun.symm n) i
    rw [Basis.ofZLatticeBasis_repr_apply]
    change (n i : ℝ) = ((b.equivFun (b.equivFun.symm n)) i : ℝ)
    rw [LinearEquiv.apply_symm_apply]
  have hs := (Equiv.summable_iff (e := b.equivFun.toEquiv.symm)).mpr
    (schwartzLatticeDecay L f K)
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  have hx : B (x : ι → ℝ) ∈ (K : Set E) :=
    ⟨(x : ι → ℝ), x.property, rfl⟩
  have ht := ContinuousMap.norm_coe_le_norm
    ((schwartzLatticeTranslate L f (b.equivFun.symm n)).restrict K) ⟨B x, hx⟩
  change ‖f (B ((x : ι → ℝ) + fun i => (n i : ℝ)))‖ ≤ _
  rw [map_add, hcast]
  exact ht

end DedekindZetaZeroFree

end
