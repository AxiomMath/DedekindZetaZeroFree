module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicRationalSplitting

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.MatrixConstruction
open NumberField IsDedekindDomain

theorem root_torus_sixth_mem_kStar
    {F : Type} [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (p : HeightOneSpectrum (𝓞 F))
    (hp : ringChar (KPTameCompact.O F p ⧸ KPTameCompact.p F p) ≠ 3)
    (u : (KPTameCompact.O F p)ˣ) (t t' : KPTameCompact.K F p)
    (ht : t' - (KPTameCompact.unitInclusion F p u : KPTameCompact.K F p) ^ 6 * t ∈
      KPTameCompact.O F p) :
    (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) t')⁻¹ *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inr p)
          (KPTameCompact.unitInclusion F p u ^ 6) *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) t ∈
      (KPGoodCompactSplitting.kStar F ζ hζ p hp).range := by
  set a : (KPTameCompact.K F p)ˣ := KPTameCompact.unitInclusion F p u ^ 6 with ha

  obtain ⟨s, hs⟩ : ∃ s : KPTameCompact.O F p,
      (s : KPTameCompact.K F p) = t' - (a : KPTameCompact.K F p) * t :=
    ⟨⟨_, ht⟩, rfl⟩

  have hsplit : t' = (a : KPTameCompact.K F p) * t + (s : KPTameCompact.K F p) := by
    rw [hs]; ring
  have hNt' : KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) t' =
      KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) ((a : KPTameCompact.K F p) * t) *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) (s : KPTameCompact.K F p) := by
    rw [hsplit, KPStandardLocalRootLifts.N_add]

  have hNnegs : KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) (-(s : KPTameCompact.K F p)) =
      (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) (s : KPTameCompact.K F p))⁻¹ := by
    have h := KPStandardLocalRootLifts.N_add F ζ hζ (Sum.inr p)
      (-(s : KPTameCompact.K F p)) (s : KPTameCompact.K F p)
    rw [neg_add_cancel, KPStandardLocalRootLifts.N_zero] at h
    exact eq_inv_of_mul_eq_one_left h.symm

  have hAN : KPStandardLocalRootLifts.A F ζ hζ (Sum.inr p) a *
      KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) t =
      KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) ((a : KPTameCompact.K F p) * t) *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inr p) a := by
    have h := KPCorrectedBruhatLifts.upper_diagonal F ζ hζ (Sum.inr p)
      ((a : KPTameCompact.K F p) * t) a
    rw [mul_div_cancel_left₀ _ a.ne_zero] at h
    exact h.symm

  have hmain : (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) t')⁻¹ *
      KPStandardLocalRootLifts.A F ζ hζ (Sum.inr p) a *
      KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) t =
      KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) (-(s : KPTameCompact.K F p)) *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inr p) a := by
    rw [hNt', mul_inv_rev, ← hNnegs]
    simp only [mul_assoc]
    rw [hAN]
    group

  have hN : KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p) (-(s : KPTameCompact.K F p)) =
      KPGoodCompactSplitting.kStar F ζ hζ p hp (KPStandardLocalRootLifts.integralN F p (-s)) := by
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p)
      ((-s : KPTameCompact.O F p) : KPTameCompact.K F p) = _
    rw [KPStandardLocalRootLifts.N_eq_compact F ζ hζ p hp (-s)]
    rfl
  have hA : KPStandardLocalRootLifts.A F ζ hζ (Sum.inr p) a =
      KPGoodCompactSplitting.kStar F ζ hζ p hp (KPStandardLocalRootLifts.integralA F p (u ^ 6)) := by
    rw [ha, ← map_pow, KPStandardLocalRootLifts.A_eq_compact F ζ hζ p hp (u ^ 6)]
    rfl
  rw [hmain, hN, hA, ← map_mul]
  exact ⟨KPStandardLocalRootLifts.integralN F p (-s) * KPStandardLocalRootLifts.integralA F p (u ^ 6), rfl⟩

end DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.MatrixConstruction

end
