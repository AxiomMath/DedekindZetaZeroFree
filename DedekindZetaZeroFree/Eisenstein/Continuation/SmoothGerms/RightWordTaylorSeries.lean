module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightWordFiniteSums

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.SharedSource
open KPGlobalResidualConstruction KPContSectorSmoothFramesSupport
open KPContActualCommonDiskRightHolomorphy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul

theorem coherentSectionWord_compact_taylor
    (W : ℂ → smoothSections F ζ hζ U R P H)
    (b : ℕ → smoothSections F ζ hζ U R P H) (c : ℂ) (ρ : ℝ)
    (hb : CoherentSeries F ζ hζ U R P H W b c ρ)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (g : G F ζ hζ) (m : ℕ) (K : Set (ArchCoordinates F))
    (hK : IsCompact K) (hKd : K ⊆ archDomain F)
    (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ M ≥ N, ∀ s : ℂ, ‖s-c‖ ≤ r → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun y =>
        KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
          (lift F ζ hζ U R P H (W s).val) (g * archChart F ζ hζ y) -
        ∑ n ∈ Finset.range M, (s-c)^n *
          KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
            (lift F ζ hζ U R P H (b n).val) (g * archChart F ζ hζ y)) x‖ < ε := by
  obtain ⟨N, hN⟩ := ActualCoherentSpatialSeries.coherentSeries_moving_jets
    F ζ hζ U R P H W b c ρ hb {g} isCompact_singleton K hK hKd [(1,w)] m
    r hr.le hrρ ε hε
  refine ⟨N, ?_⟩
  intro M hM s hs x hx
  have h := hN M hM s (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hs)
    g (Set.mem_singleton g) x hx
  let L := ActualSectionLift.scalarLift F ζ hζ U R P H
  have hlin : lift F ζ hζ U R P H
      ((∑ n ∈ Finset.range M, (s-c)^n • b n) - W s).val =
      (∑ n ∈ Finset.range M, (s-c)^n • lift F ζ hζ U R P H (b n).val) -
        lift F ζ hζ U R P H (W s).val := by
    change L _ = _
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
      map_sub, map_sum, map_smul]
    rfl
  have hsm (n : ℕ) := sectionLift_smooth U R P H (b n)
  have hsum := nativeSmooth_finset_sum (Finset.range M) _
    (fun n _ => smooth_smul F ζ hζ ((s-c)^n) _ (hsm n))
  have hneg := smooth_smul F ζ hζ (-1) _ (sectionLift_smooth U R P H (W s))
  have he : rightCombination F ζ hζ [(1,w)]
      (lift F ζ hζ U R P H ((∑ n ∈ Finset.range M, (s-c)^n • b n) - W s).val) =
      fun a => (∑ n ∈ Finset.range M, (s-c)^n *
        KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
          (lift F ζ hζ U R P H (b n).val) a) -
        KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
          (lift F ζ hζ U R P H (W s).val) a := by
    rw [hlin, sub_eq_add_neg, show -lift F ζ hζ U R P H (W s).val =
      (-1 : ℂ) • lift F ζ hζ U R P H (W s).val by simp]
    funext a
    simp only [rightCombination, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, one_mul, add_zero]
    rw [actualRightWord_add _ _ hsum hneg w,
      actualRightWord_finset_sum _ _ (fun n _ => smooth_smul F ζ hζ ((s-c)^n) _ (hsm n)) w]
    simp only [actualRightWord_smul _ _ (hsm _) w,
      actualRightWord_smul _ _ (sectionLift_smooth U R P H (W s)) w,
      Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, neg_one_mul]
    rfl
  rw [he] at h
  have hfun : (fun y =>
      KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
        (lift F ζ hζ U R P H (W s).val) (g * archChart F ζ hζ y) -
      ∑ n ∈ Finset.range M, (s-c)^n *
        KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
          (lift F ζ hζ U R P H (b n).val) (g * archChart F ζ hζ y)) =
      -(fun y => (∑ n ∈ Finset.range M, (s-c)^n *
        KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
          (lift F ζ hζ U R P H (b n).val) (g * archChart F ζ hζ y)) -
        KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
          (lift F ζ hζ U R P H (W s).val) (g * archChart F ζ hζ y)) := by
    funext y
    simp only [Pi.neg_apply, neg_sub]
  rw [hfun, iteratedFDeriv_neg]
  simpa only [Pi.neg_apply, norm_neg] using h

end DedekindZetaZeroFree.SharedSource

end
