module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.PGLOrbitNeighborhoods

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCuspSiegel

variable (F : Type*) [Field F] [NumberField F]

theorem isCompact_box
    (P : Set (Fin (KPCuspLogShape.dimension F) → ℂ))
    (B : Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)))
    (I : Set ℝ) (hP : IsCompact P) (hB : IsCompact B) (hI : IsCompact I) :
    IsCompact (box F P B I) := by
  let f : ((Fin (KPCuspLogShape.dimension F) → ℂ) ×
      KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)) × ℝ →
      KPArch.Space (KPCuspLogShape.dimension F) :=
    fun p i => (p.1.1 i, p.2 + (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i)
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_fst.fst).prodMk
      (continuous_snd.add ((continuous_apply i).comp
        (continuous_subtype_val.comp continuous_fst.snd)))
  have he : box F P B I = f '' ((P ×ˢ B) ×ˢ I) := by
    ext z
    constructor
    · rintro ⟨x, hx, b, hb, t, ht, rfl⟩
      exact ⟨((x, b), t), ⟨⟨hx, hb⟩, ht⟩, rfl⟩
    · rintro ⟨⟨⟨x, b⟩, t⟩, ⟨⟨hx, hb⟩, ht⟩, rfl⟩
      exact ⟨x, hx, b, hb, t, ht, rfl⟩
  rw [he]
  exact ((hP.prod hB).prod hI).image hf

theorem continuous_arch_action (A : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Continuous (KPArch.action A) := by
  have hden : Continuous (KPArch.actionDenominator A) := by
    unfold KPArch.actionDenominator KPArch.height
    fun_prop
  have hq : Continuous (fun z : KPArch.H3 =>
      ‖(A : Matrix (Fin 2) (Fin 2) ℂ).det‖ * KPArch.height z /
        KPArch.actionDenominator A z) := by
    apply Continuous.div
    · unfold KPArch.height
      fun_prop
    · exact hden
    · exact fun z => ne_of_gt (KPArch.actionDenominator_pos A z)
  apply Continuous.prodMk
  · apply Continuous.div
    · unfold KPArch.height
      fun_prop
    · exact (Complex.continuous_ofReal.comp hden)
    · intro z
      exact_mod_cast ne_of_gt (KPArch.actionDenominator_pos A z)
  · apply Continuous.log hq
    intro z
    exact ne_of_gt (div_pos (mul_pos (norm_pos_iff.mpr A.det_ne_zero)
      (Real.exp_pos _)) (KPArch.actionDenominator_pos A z))

theorem continuous_action (g : KPCuspArithmetic.PGL2 F) :
    Continuous (action F g) := by
  change Continuous (glAction F (Classical.choose (Matrix.ProjGenLinGroup.mk_surjective g)))
  apply continuous_pi
  intro i
  exact (continuous_arch_action _).comp (continuous_apply i)

theorem continuous_projection (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) :
    Continuous (projection F Γ) := continuous_quotient_mk'

theorem isCompact_projected_truncated_boxes
    {n : ℕ} (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (σ : Fin n → KPCuspArithmetic.PGL2 F)
    (P : Fin n → Set (Fin (KPCuspLogShape.dimension F) → ℂ))
    (B : Fin n → Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)))
    (hP : ∀ a, IsCompact (P a)) (hB : ∀ a, IsCompact (B a)) (t₀ T : ℝ) :
    IsCompact (projection F Γ ''
      (⋃ a : Fin n, action F (σ a) '' box F (P a) (B a) (Set.Icc t₀ T))) := by
  apply IsCompact.image _ (continuous_projection F Γ)
  apply isCompact_iUnion
  intro a
  exact (isCompact_box F (P a) (B a) _ (hP a) (hB a) isCompact_Icc).image
    (continuous_action F (σ a))

end DedekindZetaZeroFree.KPCuspSiegel

end
