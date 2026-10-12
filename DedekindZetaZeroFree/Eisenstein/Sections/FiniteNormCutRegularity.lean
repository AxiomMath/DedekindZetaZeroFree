module

public import DedekindZetaZeroFree.Eisenstein.Sections.FiniteNormTranslationRange

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}

theorem logIncrement_compact_right_orbit_locallyConstant
    (u : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    IsLocallyConstant (fun k : D.K =>
      (fun g : KPMsRationalCompactCrossPairing.G F ζ hζ =>
        logIncrement (D := D) (g * k.val) u.val)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro k
  letI : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  have he : ∀ᶠ l : D.K in 𝓝 k, ∀ v : D.K,
      logIncrement (D := D) (v.val * l.val) u.val =
        logIncrement (D := D) (v.val * k.val) u.val := by
    have he' : ∀ᶠ l : D.K in 𝓝 k, ∀ v ∈ (Set.univ : Set D.K),
        logIncrement (D := D) (v.val * l.val) u.val =
          logIncrement (D := D) (v.val * k.val) u.val := by
      apply IsCompact.eventually_forall_of_forall_eventually isCompact_univ
      intro v _
      have h := (logIncrement_finite_global_locallyConstant (D := D) u).eventually_eq
        (v.val * k.val)
      have hc₁ : Continuous (fun p : D.K × D.K => p.2.val * p.1.val) :=
        (continuous_subtype_val.comp continuous_snd).mul
          (continuous_subtype_val.comp continuous_fst)
      have hc₂ : Continuous (fun p : D.K × D.K => p.2.val * k.val) :=
        (continuous_subtype_val.comp continuous_snd).mul continuous_const
      filter_upwards [hc₁.continuousAt h, hc₂.continuousAt h] with p hp₁ hp₂
      exact hp₁.trans hp₂.symm
    simpa only [Set.mem_univ, forall_true_left] using he'
  filter_upwards [he] with l hl
  funext g
  obtain ⟨t, x, v, hg⟩ := D.decomposition g
  rw [hg, mul_assoc (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) v.val l.val,
    mul_assoc (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) v.val k.val,
    logIncrement_borel_mul, logIncrement_borel_mul]
  exact hl v

theorem logIncrement_compact_right_orbit_finite
    (u : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    (Set.range (fun k : D.K =>
      (fun g : KPMsRationalCompactCrossPairing.G F ζ hζ =>
        logIncrement (D := D) (g * k.val) u.val))).Finite := by
  letI : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  exact (logIncrement_compact_right_orbit_locallyConstant (D := D) u).range_finite

end DedekindZetaZeroFree.KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition

end
