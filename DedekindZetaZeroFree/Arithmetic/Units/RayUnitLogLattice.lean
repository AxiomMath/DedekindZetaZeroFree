module

public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitFiniteIndex
public import DedekindZetaZeroFree.Theta.Unfolding.UnitSlabRadialAngularIntegration
public import DedekindZetaZeroFree.Arithmetic.Ideals.IdealElementDecomposition

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField Module

namespace DedekindZetaZeroFree.AbelianQuotient.RayCoset

variable (K : Type) [Field K] [NumberField K]

def weightedLogSum : (InfinitePlace K → ℝ) →ₗ[ℝ] ℝ :=
  ∑ v : InfinitePlace K, (InfinitePlace.mult v : ℝ) • LinearMap.proj v

def logHyperplane : Submodule ℝ (InfinitePlace K → ℝ) :=
  LinearMap.ker (weightedLogSum K)

def logAbs : Additive ((𝓞 K)ˣ) →ₗ[ℤ] logHyperplane K :=
  ({ toFun := fun u => ⟨fun v => Real.log (v (u.toMul : K)), by
       simpa [logHyperplane, weightedLogSum] using
         NumberField.Units.sum_mult_mul_log u.toMul⟩
     map_zero' := by
       apply Subtype.ext
       funext v
       simp
     map_add' := by
       intro u w
       apply Subtype.ext
       funext v
       simp [Real.log_mul] } : Additive ((𝓞 K)ˣ) →+ logHyperplane K).toIntLinearMap

@[simp] theorem logAbs_apply (u : Additive ((𝓞 K)ˣ)) (v : InfinitePlace K) :
    (logAbs K u).val v = Real.log (v (u.toMul : K)) := rfl

def fullUnitLogLattice : Submodule ℤ (logHyperplane K) :=
  LinearMap.range (logAbs K)

def rayUnitLogEmbedding (m : Ideal (𝓞 K)) :
    Additive (U K m) →ₗ[ℤ] logHyperplane K :=
  (logAbs K).comp ((positiveRayUnits K m).subtype.toAdditive.toIntLinearMap)

def rayUnitLogLattice (m : Ideal (𝓞 K)) : Submodule ℤ (logHyperplane K) :=
  LinearMap.range (rayUnitLogEmbedding K m)

open NumberField.Units.dirichletUnitTheorem NumberField.Units

 def coords : logHyperplane K →ₗ[ℝ] logSpace K where
  toFun h v := (InfinitePlace.mult v.val : ℝ) * h.val v.val
  map_add' h g := by ext v; simp [mul_add]
  map_smul' r h := by ext v; simp [mul_left_comm]
private theorem sum_h (h : logHyperplane K) :
    ∑ v, (InfinitePlace.mult v : ℝ) * h.val v = 0 := by
  simpa [logHyperplane, weightedLogSum] using h.property
 theorem coords_injective : Function.Injective (coords K) := by
  intro h g he
  apply Subtype.ext
  funext v
  by_cases hv : v = w₀
  · have hs := sum_h K h
    have ht := sum_h K g
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hs ht
    have hsum : (∑ w : {w : InfinitePlace K // w ≠ w₀},
        (InfinitePlace.mult w.val : ℝ) * h.val w.val) =
        ∑ w : {w : InfinitePlace K // w ≠ w₀},
          (InfinitePlace.mult w.val : ℝ) * g.val w.val :=
      congrArg (fun x : logSpace K => ∑ w, x w) he
    rw [hsum] at hs
    have heq : (InfinitePlace.mult (w₀ : InfinitePlace K) : ℝ) * h.val w₀ =
        (InfinitePlace.mult (w₀ : InfinitePlace K) : ℝ) * g.val w₀ := by linarith
    subst v
    exact mul_left_cancel₀ InfinitePlace.mult_coe_ne_zero heq
  · have hh := congrFun he ⟨v, hv⟩
    exact mul_left_cancel₀ InfinitePlace.mult_coe_ne_zero hh
 theorem coords_surjective : Function.Surjective (coords K) := by
  intro x
  let h : InfinitePlace K → ℝ := fun v =>
    if hv : v = w₀ then -(∑ w, x w) / (InfinitePlace.mult v : ℝ)
    else x ⟨v, hv⟩ / (InfinitePlace.mult v : ℝ)
  have hh : h ∈ logHyperplane K := by
    change weightedLogSum K h = 0
    simp only [weightedLogSum, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
    simp only [h, dif_pos rfl, mul_div_cancel₀ _ InfinitePlace.mult_coe_ne_zero]
    have hs : (∑ v : {v : InfinitePlace K // v ≠ w₀},
        (InfinitePlace.mult v.val : ℝ) *
          if hv : v.val = w₀ then -(∑ w, x w) / (InfinitePlace.mult v.val : ℝ)
          else x ⟨v.val, hv⟩ / (InfinitePlace.mult v.val : ℝ)) = ∑ v, x v := by
      apply Finset.sum_congr rfl
      intro v _
      simp [v.property, mul_div_cancel₀, InfinitePlace.mult_coe_ne_zero]
    rw [hs]
    exact neg_add_cancel _
  refine ⟨⟨h, hh⟩, ?_⟩
  ext v
  simp [coords, h, v.property, InfinitePlace.mult_coe_ne_zero, mul_div_cancel₀]
 def coordEquiv : logHyperplane K ≃ₗ[ℝ] logSpace K :=
  LinearEquiv.ofBijective (coords K) ⟨coords_injective K, coords_surjective K⟩
 theorem full_eq_comap : fullUnitLogLattice K =
    ZLattice.comap ℝ (unitLattice K) (coordEquiv K).toLinearMap := by
  ext h
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, Submodule.mem_top, rfl⟩
  · rintro ⟨u, _, hu⟩
    refine ⟨u, coords_injective K ?_⟩
    exact hu

theorem rayUnitLogLattice_le_full (m : Ideal (𝓞 K)) :
    rayUnitLogLattice K m ≤ fullUnitLogLattice K := by
  exact LinearMap.range_comp_le_range _ _

instance discreteTopology_fullUnitLogLattice :
    DiscreteTopology (fullUnitLogLattice K) := by
  rw [full_eq_comap K]
  exact ZLattice.comap_discreteTopology ℝ (unitLattice K)
    (coordEquiv K).toLinearMap.continuous_of_finiteDimensional (coordEquiv K).injective

instance isZLattice_fullUnitLogLattice :
    IsZLattice ℝ (fullUnitLogLattice K) := by
  constructor
  rw [full_eq_comap K]
  exact ZLattice.comap_span_top ℝ (unitLattice K)
    (IsZLattice.span_top (K := ℝ)) (by
      intro x _
      exact LinearMap.mem_range.mpr ((coordEquiv K).surjective x))

instance discreteTopology_rayUnitLogLattice (m : Ideal (𝓞 K)) :
    DiscreteTopology (rayUnitLogLattice K m) := by
  exact DiscreteTopology.of_subset (inferInstance : DiscreteTopology (fullUnitLogLattice K))
    (rayUnitLogLattice_le_full K m)

theorem rayUnitLogLattice_span_eq_top (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Submodule.span ℝ (rayUnitLogLattice K m : Set (logHyperplane K)) = ⊤ := by
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := fullUnitLogLattice K)]
  apply Submodule.span_le.mpr
  rintro x ⟨u, rfl⟩
  obtain ⟨k, hk, hu⟩ := exists_pos_pow_mem_positiveRayUnits K m hm u.toMul
  have hh : (k : ℝ) • logAbs K u ∈
      Submodule.span ℝ (rayUnitLogLattice K m : Set (logHyperplane K)) := by
    have he : (k : ℝ) • logAbs K u =
        rayUnitLogEmbedding K m (Additive.ofMul ⟨u.toMul ^ k, hu⟩) := by
      change (k : ℝ) • logAbs K u = logAbs K (k • u)
      rw [map_nsmul]
      exact_mod_cast (Nat.cast_smul_eq_nsmul ℝ k (logAbs K u))
    rw [he]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (Submodule.smul_mem_iff _ (show (k : ℝ) ≠ 0 by exact_mod_cast hk.ne')).mp hh

theorem isZLattice_rayUnitLogLattice (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    IsZLattice ℝ (rayUnitLogLattice K m) := by
  exact ⟨rayUnitLogLattice_span_eq_top K m hm⟩

theorem finrank_logHyperplane :
    Module.finrank ℝ (logHyperplane K) = NumberField.Units.rank K := by
  rw [(coordEquiv K).finrank_eq]
  exact Units.finrank_eq_rank K

theorem finrank_rayUnitLogLattice (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Module.finrank ℤ (rayUnitLogLattice K m) = NumberField.Units.rank K := by
  letI := isZLattice_rayUnitLogLattice K m hm
  rw [ZLattice.rank ℝ, finrank_logHyperplane K]

def rayUnitLogBasis (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Basis (Fin (NumberField.Units.rank K)) ℤ (rayUnitLogLattice K m) := by
  letI := isZLattice_rayUnitLogLattice K m hm
  letI := ZLattice.module_finite ℝ (rayUnitLogLattice K m)
  letI := ZLattice.module_free ℝ (rayUnitLogLattice K m)
  exact (Module.finBasis ℤ (rayUnitLogLattice K m)).reindex
    (finCongr (finrank_rayUnitLogLattice K m hm))

end DedekindZetaZeroFree.AbelianQuotient.RayCoset

end
