module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.SmoothDualCompactPairing
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.CyclicIrreducibleQuotients
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.CuspidalProjectiveRetraction
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.VanishingAndCompactCoefficients

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalPrincipalSeriesCuspidalExclusion

open scoped NumberField NNReal
open NumberField IsDedekindDomain Topology
open KPLocalSmoothRepresentation KPLocalInducedSmoothDual
open KPLocalStoneVonNeumann KPLocalInductionJacquetReciprocity

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)

def dualInducedAction {E : Type*} [AddCommGroup E] [Module ℂ E]
    (τ : Representation ℂ (Torus F ζ hζ w) E) :
    letI := finiteCoverTopology F ζ hζ w m
    letI : AddCommGroup (PrincipalSeries F ζ hζ w m (borelRetraction F ζ hζ w) τ) :=
      (PrincipalSeries F ζ hζ w m (borelRetraction F ζ hζ w) τ).addCommGroup
    Representation ℂ (FiniteCover F ζ hζ w)
      (SmoothDual (inducedAction F ζ hζ w m hm τ)) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  letI : AddCommGroup (PrincipalSeries F ζ hζ w m (borelRetraction F ζ hζ w) τ) :=
    (PrincipalSeries F ζ hζ w m (borelRetraction F ζ hζ w) τ).addCommGroup
  exact smoothDualRepresentation (inducedAction F ζ hζ w m hm τ)

def JacquetDetectsSubquotients {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteCover F ζ hζ w) V) : Prop :=
  ∀ (A B : Submodule ℂ V)
    (hA : ∀ g, A ≤ A.comap (ρ g)) (hB : ∀ g, B ≤ B.comap (ρ g)),
    B ≤ A →
    Subsingleton (OrdinaryCoinvariants F ζ hζ w
      (KPCyclicQuotient.subquotientRepresentation ρ A B hA hB)) → A = B

include hm in
theorem actual_cover_compact_open_basis :
    letI := finiteCoverTopology F ζ hζ w m
    ∀ N ∈ nhds (1 : FiniteCover F ζ hζ w),
      ∃ J : CompactOpenLevel (FiniteCover F ζ hζ w), (J.toOpenSubgroup : Set _) ⊆ N := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ w m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ w m hm).2.2
  letI : NonarchimedeanGroup (KPLocalCube.LocalGL2 F w) :=
    { is_nonarchimedean := fun U hU => by
        obtain ⟨r, hr, hsub⟩ := (KPLocalCube.Gamma_nhds_basis F w m hm.1).mem_iff.mp hU
        exact ⟨⟨KPLocalCube.Gamma F w r, (KPLocalCube.Gamma_compact_open F w r (hm.1.trans hr)).2⟩, hsub⟩ }
  letI : NonarchimedeanGroup (KPLocalCube.Gamma F w m) :=
    { is_nonarchimedean := fun U hU => by
        obtain ⟨V, hV, hsub⟩ := (mem_nhds_subtype _ _ _).mp hU
        obtain ⟨J, hJ⟩ := NonarchimedeanGroup.is_nonarchimedean V hV
        refine ⟨⟨J.toSubgroup.comap (KPLocalCube.Gamma F w m).subtype,
          J.isOpen.preimage continuous_subtype_val⟩, ?_⟩
        exact fun x hx => hsub (hJ hx) }
  letI : CompactSpace (KPLocalCube.Gamma F w m) :=
    isCompact_iff_compactSpace.mp (KPLocalCube.Gamma_compact_open F w m hm.1).1
  obtain ⟨s, hs, hi, hp⟩ := KPDeepRawSplitting.raw_section_splitting F ζ hζ w m
    (fun g hg h hh => KPDeepRawSplitting.sigmaTwo_eq_one_on_Gamma F ζ hζ w m hm.2 g h hg hh)
  have he : IsOpenEmbedding s := by
    have he := KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ w m hm 1
    have hse : (s : _ → _) = KPLocalChartTopology.translatedChart F ζ hζ w m 1 := by
      funext x; simp [hs, KPLocalChartTopology.translatedChart]
    rwa [← hse] at he
  let q := KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr w)
  letI := finiteCoverTopology F ζ hζ w m
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  intro N hN
  have hn : (q.comp s) ⁻¹' N ∈ nhds 1 := by
    have h := (hq.comp he.continuous).tendsto 1
    simpa only [Filter.mem_map, MonoidHom.coe_comp, Function.comp_apply, map_one] using h (by simpa only [Function.comp_apply, map_one] using hN)
  obtain ⟨U, hU⟩ := NonarchimedeanGroup.is_nonarchimedean _ hn
  let J : OpenSubgroup (FiniteCover F ζ hζ w) :=
    { Subgroup.map (q.comp s) U.toSubgroup with
      isOpen' := by
        change IsOpen ((q.comp s) '' (U : Set _))
        rw [MonoidHom.coe_comp, Set.image_comp]
        exact hqo _ (he.isOpenMap _ U.isOpen) }
  refine ⟨⟨J, ?_⟩, ?_⟩
  · exact (IsClosed.isCompact U.isClosed).image (hq.comp he.continuous)
  · exact Set.image_subset_iff.mpr hU

end DedekindZetaZeroFree.KPLocalPrincipalSeriesCuspidalExclusion

end
