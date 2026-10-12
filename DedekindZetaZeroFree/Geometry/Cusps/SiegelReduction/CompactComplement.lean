module

public import DedekindZetaZeroFree.Geometry.Cusps.SiegelReduction.CompactBoxes

@[expose] public section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.KPCuspSiegel

variable (F : Type*) [Field F] [NumberField F]

theorem isOpenMap_action (g : KPCuspArithmetic.PGL2 F) : IsOpenMap (action F g) := by
  apply IsOpenMap.of_inverse (continuous_action F g⁻¹)
  · intro z
    change g • (g⁻¹ • z) = z
    exact smul_inv_smul g z
  · intro z
    change g⁻¹ • (g • z) = z
    exact inv_smul_smul g z

theorem isOpen_highCusp (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    IsOpen (highCusp F σ T) := by
  apply isOpenMap_action F σ
  apply isOpen_lt continuous_const
  unfold KPCuspLogShape.meanHeight
  fun_prop

theorem isOpenMap_projection (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) :
    IsOpenMap (projection F Γ) := by
  letI : ContinuousConstSMul Γ (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨fun g => continuous_action F (g : KPCuspArithmetic.PGL2 F)⟩
  exact MulAction.isOpenQuotientMap_quotientMk.isOpenMap

theorem isOpen_projected_highCusps {n : ℕ}
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (σ : Fin n → KPCuspArithmetic.PGL2 F) (T : ℝ) :
    IsOpen (⋃ a : Fin n, projection F Γ '' highCusp F (σ a) T) := by
  apply isOpen_iUnion
  intro a
  exact isOpenMap_projection F Γ _ (isOpen_highCusp F (σ a) T)

theorem meanHeight_box_coordinate (hd : 0 < KPCuspLogShape.dimension F)
    (x : Fin (KPCuspLogShape.dimension F) → ℂ)
    (b : KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)) (t : ℝ) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (fun i => (x i, t + (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)) = t := by
  have hb := b.property
  change (∑ i, (b : Fin (KPCuspLogShape.dimension F) → ℝ) i) = 0 at hb
  simp only [KPCuspLogShape.meanHeight, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hb, add_zero]
  exact mul_div_cancel_left₀ t (by exact_mod_cast ne_of_gt hd)

theorem projection_action (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (γ : Γ)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    projection F Γ (action F (γ : KPCuspArithmetic.PGL2 F) z) = projection F Γ z := by
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩)

theorem isCompact_complement_of_cover {n : ℕ}
    (hd : 0 < KPCuspLogShape.dimension F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (σ : Fin n → KPCuspArithmetic.PGL2 F)
    (P : Fin n → Set (Fin (KPCuspLogShape.dimension F) → ℂ))
    (B : Fin n → Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)))
    (hP : ∀ a, IsCompact (P a)) (hB : ∀ a, IsCompact (B a)) (t₀ T : ℝ)
    (hcover : ∀ z : KPArch.Space (KPCuspLogShape.dimension F),
      ∃ (γ : Γ) (a : Fin n) (w : KPArch.Space (KPCuspLogShape.dimension F)),
        w ∈ box F (P a) (B a) (Set.Ici t₀) ∧
        z = action F (γ : KPCuspArithmetic.PGL2 F) (action F (σ a) w)) :
    IsCompact ((Set.univ : Set (OrbitQuotient F Γ)) \
      (⋃ a : Fin n, projection F Γ '' highCusp F (σ a) T)) := by
  apply (isCompact_projected_truncated_boxes F Γ σ P B hP hB t₀ T).of_isClosed_subset
  · have he : (Set.univ : Set (OrbitQuotient F Γ)) \
        (⋃ a : Fin n, projection F Γ '' highCusp F (σ a) T) =
        (⋃ a : Fin n, projection F Γ '' highCusp F (σ a) T)ᶜ := by
      ext p
      exact and_iff_right (Set.mem_univ p)
    rw [he]
    exact (isOpen_projected_highCusps F Γ σ T).isClosed_compl
  · intro p hp
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective p
    obtain ⟨γ, a, w, hw, hz⟩ := hcover z
    rcases hw with ⟨x, hx, b, hb, t, ht, rfl⟩
    have htT : t ≤ T := by
      by_contra hn
      have hhigh : action F (σ a)
          (fun i => (x i, t + (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)) ∈
          highCusp F (σ a) T := by
        refine ⟨_, ?_, rfl⟩
        change T < KPCuspLogShape.meanHeight _ _
        rw [meanHeight_box_coordinate F hd]
        exact lt_of_not_ge hn
      apply hp.2
      apply Set.mem_iUnion.mpr
      refine ⟨a, _, hhigh, ?_⟩
      change projection F Γ _ = projection F Γ z
      rw [hz, projection_action]
    refine ⟨action F (σ a)
      (fun i => (x i, t + (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)), ?_, ?_⟩
    · apply Set.mem_iUnion.mpr
      exact ⟨a, _, ⟨x, hx, b, hb, t, ⟨ht, htT⟩, rfl⟩, rfl⟩
    · change projection F Γ _ = projection F Γ z
      rw [hz, projection_action]

end DedekindZetaZeroFree.KPCuspSiegel

end
