module

import all DedekindZetaZeroFree.Eisenstein.Residues.FlatRange.ActualProjectedFlatExpansion
public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAbsoluteConvergence

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.ResidualFlatRange.ProjectedChamberComparison
open KPLiteralRaw
open private projected_family_finite_flat_expansion from
  DedekindZetaZeroFree.Eisenstein.Residues.FlatRange.ActualProjectedFlatExpansion
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

private theorem projected_chamber_interchange
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a g : G F ζ hζ) (h : C(K, ℂ))
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) :
    (∫ k : K, h k * eisenstein F ζ hζ K f s (g * k.val * a) ∂μ) =
      ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
        ∫ k : K, h k * f.val s (rationalLift F ζ hζ (Quotient.out c) * g * k.val * a) ∂μ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  let : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  let : Countable (Matrix.ProjGenLinGroup (Fin 2) F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  let o : K → G F ζ hζ := fun k => g * k.val * a
  have ho : Continuous o := (continuous_const.mul continuous_subtype_val).mul continuous_const
  obtain ⟨b, hb, hbound⟩ := KPLiteralChamber.chamber_scalar_compact_majorants
    F ζ hζ K hK f {s} (isCompact_singleton) (by simpa using hs)
    (Set.range o) (isCompact_range ho)
  let A : KPChamberBruhatTwoCells.RationalQuotient F → K → ℂ := fun c k =>
    h k * f.val s (rationalLift F ζ hζ (Quotient.out c) * g * k.val * a)
  have hAi (c) : Integrable (A c) μ := by
    exact (h.continuous.mul ((f.property.1 s).1.1.comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hA_bound (c) (k : K) : ‖A c k‖ ≤ ‖h‖ * |b c| := by
    rw [norm_mul]
    apply mul_le_mul (h.norm_coe_le_norm k) _ (norm_nonneg _) (norm_nonneg _)
    have hbnd := hbound c s (Set.mem_singleton s) (o k) ⟨k, rfl⟩
    have hbnd' : ‖f.val s (rationalLift F ζ hζ (Quotient.out c) * g * k.val * a)‖ ≤ b c := by
      simpa only [o, mul_assoc] using hbnd
    exact hbnd'.trans (le_abs_self _)
  have hsum : Summable (fun c => ∫ k : K, ‖A c k‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun c => integral_nonneg (fun k => norm_nonneg _))
      (fun c => ?_) (hb.abs.mul_left ‖h‖)
    have hi := integral_mono_of_nonneg (Eventually.of_forall (fun k => norm_nonneg _)) (integrable_const (μ := μ) (‖h‖ * |b c|))
      (Eventually.of_forall (hA_bound c))
    simpa using hi
  have hi := integral_tsum_of_summable_integral_norm hAi hsum
  calc
    (∫ k : K, h k * eisenstein F ζ hζ K f s (g * k.val * a) ∂μ) =
        ∫ k : K, ∑' c, A c k ∂μ := by
      apply integral_congr_ae
      filter_upwards with k
      change h k * (∑' c, f.val s
        (rationalLift F ζ hζ (Quotient.out c) * (g * k.val * a))) =
        ∑' c, h k * f.val s
          (rationalLift F ζ hζ (Quotient.out c) * g * k.val * a)
      rw [← tsum_mul_left]
      congr 1
      funext c
      congr 1
      group
    _ = _ := hi.symm

private theorem finite_flat_projected_chamber
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ) (h : C(K, ℂ))
    (n : ℕ) (v : Fin n → Flat F ζ hζ K) (c : Fin n → ℂ → ℂ)
    (he : ∀ s g, (∫ k : K, h k * f.val s (g * k.val * a) ∂μ) =
      ∑ j, c j s * (v j).val s g)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    (∫ k : K, h k * eisenstein F ζ hζ K f s (g * k.val * a) ∂μ) =
      ∑ j, c j s * eisenstein F ζ hζ K (v j) s g := by
  rw [projected_chamber_interchange F ζ hζ K hK μ f a g h s hs]
  have hsub : (fun q : KPChamberBruhatTwoCells.RationalQuotient F =>
      ∫ k : K, h k * f.val s
        (rationalLift F ζ hζ (Quotient.out q) * g * k.val * a) ∂μ) =
      (fun q => ∑ j, c j s * (v j).val s
        (rationalLift F ζ hζ (Quotient.out q) * g)) := by
    funext q
    exact he s (rationalLift F ζ hζ (Quotient.out q) * g)
  rw [hsub]
  rw [Summable.tsum_finsetSum (fun j _ =>
    (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK (v j) s hs g).mul_left (c j s))]
  exact Finset.sum_congr rfl (fun j _ => tsum_mul_left)

end DedekindZetaZeroFree.ResidualFlatRange.ProjectedChamberComparison

end
