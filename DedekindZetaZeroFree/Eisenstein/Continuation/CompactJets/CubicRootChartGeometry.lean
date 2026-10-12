module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.Defs

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private lemma central_comm (e : rootsOfUnity 3 F) (c : FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ e * c = c * KPCuspGenuineMonodromy.central F ζ hζ e := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨e,rfl⟩) c).symm

private lemma comparison_member (a : ActualChart (U := U) (H := H))
    (g : KPCuspArithmetic.PGL2 F) (e : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (he : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ g * (H.atlas U).representative a.component =
      KPCuspGenuineMonodromy.central F ζ hζ e * (H.atlas U).representative a.component * u.val) :
    g ∈ KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component := by
  have hz : KPCuspGenuineMonodromy.finiteBase F ζ hζ (KPCuspGenuineMonodromy.central F ζ hζ e) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.1]
    exact ⟨e, rfl⟩
  have hp := congrArg (KPCuspGenuineMonodromy.finiteBase F ζ hζ) he
  simp only [map_mul, hz, one_mul] at hp
  rw [← MonoidHom.comp_apply, (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1] at hp
  change KPFiniteComponents.diagonal F g ∈
    (U.toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ)).map
      (MulAut.conj (KPCuspGenuineMonodromy.finiteBase F ζ hζ ((H.atlas U).representative a.component))).toMonoidHom
  refine ⟨KPCuspGenuineMonodromy.finiteBase F ζ hζ u.val, ⟨u.val, u.property, rfl⟩, ?_⟩
  change KPCuspGenuineMonodromy.finiteBase F ζ hζ ((H.atlas U).representative a.component) *
    KPCuspGenuineMonodromy.finiteBase F ζ hζ u.val *
      (KPCuspGenuineMonodromy.finiteBase F ζ hζ ((H.atlas U).representative a.component))⁻¹ = _
  have ht := congrArg (fun z => z *
    (KPCuspGenuineMonodromy.finiteBase F ζ hζ ((H.atlas U).representative a.component))⁻¹) hp.symm
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using ht

private lemma separated_member (a : ActualChart (U := U) (H := H))
    (g : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
    (x : KPCuspGenuineMonodromy.SymmetricSpace F) (hx : x ∈ a.domain)
    (hg : (g.val : KPCuspArithmetic.PGL2 F) • x ∈ a.domain) : g ∈ a.Isotropy := by
  let ga : KPContSectorPhaseComponentCharts.ArchComponent F ζ hζ U R P H a.component :=
    ⟨KPContSectorPhaseComponentCharts.complexProjectiveEmbedding F g.val,
      Subgroup.mem_map.mpr ⟨g.val,g.property,rfl⟩⟩
  have hh : ga ∈ MulAction.stabilizer _ a.center := a.larger.separated ga
    ⟨g.val • x, ⟨x,a.closure_subset (subset_closure hx),
      KPContSectorPhaseComponentCharts.complexProjectiveEmbedding_smul F g.val x⟩,
      a.closure_subset (subset_closure hg)⟩
  change ga • a.center = a.center at hh
  change g.val • a.center = a.center
  exact (KPContSectorPhaseComponentCharts.complexProjectiveEmbedding_smul F g.val a.center).symm.trans hh

private lemma la_al (x : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) x) = x := by
  funext k; simp [labeledA, labeledAInv]
private lemma al_la (x : M F) :
    labeledAInv (placeEquiv F ζ hζ) (labeledA (placeEquiv F ζ hζ) x) = x := by
  simp [labeledA, labeledAInv]

private lemma root_fibers (a : ActualChart (U := U) (H := H))
    (C : Set (M F)) (hD : C ⊆ omega a) (p r : rootsOfUnity 3 F × C) :
    (Quotient.mk (coveredRelation F ζ hζ U)
      (labeledA (placeEquiv F ζ hζ) p.2.val,
        KPCuspGenuineMonodromy.central F ζ hζ p.1 * (H.atlas U).representative a.component) : CoveredSpherical F ζ hζ U) =
    Quotient.mk (coveredRelation F ζ hζ U)
      (labeledA (placeEquiv F ζ hζ) r.2.val,
        KPCuspGenuineMonodromy.central F ζ hζ r.1 * (H.atlas U).representative a.component) ↔
    ∃ g : Gamma a, r.1 = p.1 * (isotropyArrow a g).root⁻¹ ∧
      r.2.val = (isotropyArrow a g).psi p.2.val := by
  constructor
  · intro he
    obtain ⟨g,u,hx,hc⟩ := Quotient.exact he
    have hcomp : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ g * (H.atlas U).representative a.component =
        KPCuspGenuineMonodromy.central F ζ hζ (p.1⁻¹ * r.1) * (H.atlas U).representative a.component * u.val⁻¹ := by
      rw [← mul_assoc, ← central_comm p.1] at hc
      have ht := congrArg (fun z : FiniteCover F ζ hζ =>
        (KPCuspGenuineMonodromy.central F ζ hζ p.1)⁻¹ * z * u.val⁻¹) hc
      simp only [map_mul, map_inv]
      simpa only [Prod.snd, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using ht.symm
    let gg : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component :=
      ⟨g, comparison_member a g (p.1⁻¹*r.1) u⁻¹ hcomp⟩
    have hfix : gg ∈ a.Isotropy := separated_member a gg _ (hD p.2.property) (by
      change g • labeledA (placeEquiv F ζ hζ) p.2.val ∈ a.domain
      rw [← hx]; exact hD r.2.property)
    let sigma : a.Isotropy := ⟨gg,hfix⟩
    let gamma : Gamma a := ⟨(sigma, r.1⁻¹*p.1), u⁻¹, by
      change _ = KPCuspGenuineMonodromy.central F ζ hζ (r.1⁻¹*p.1)⁻¹ * _ * u.val⁻¹
      simpa only [mul_inv_rev, inv_inv] using hcomp⟩
    refine ⟨gamma, ?_, ?_⟩
    · change r.1 = p.1 * (r.1⁻¹*p.1)⁻¹
      group
    · change r.2.val = labeledAInv (placeEquiv F ζ hζ)
        ((1⁻¹ * g * 1) • labeledA (placeEquiv F ζ hζ) p.2.val)
      simp only [inv_one, one_mul, mul_one, ← hx, al_la]
  · rintro ⟨g,hr,hx⟩
    apply Quotient.sound
    refine ⟨g.val.1.val.val, (isotropyArrow a g).levelLift⁻¹, ?_, ?_⟩
    · have hx' := congrArg (labeledA (placeEquiv F ζ hζ)) hx
      simpa [Arrow.psi, coordinateMap, isotropyArrow, isotropyChart, ChartKind.representative, la_al] using hx'
    · have hc := (isotropyArrow a g).finite_comparison
      change KPCuspGenuineMonodromy.central F ζ hζ r.1 * (H.atlas U).representative a.component =
        KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (isotropyArrow a g).gamma *
          (KPCuspGenuineMonodromy.central F ζ hζ p.1 * (H.atlas U).representative a.component) *
            ((isotropyArrow a g).levelLift.val)⁻¹
      rw [hr, map_mul]
      rw [← mul_assoc (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ _), ← central_comm p.1]
      conv_rhs => rw [mul_assoc _ _ ((H.atlas U).representative a.component)]
      rw [hc]
      simp [mul_assoc]

private lemma base_raw_root (a : ActualChart (U := U) (H := H))
    (e : rootsOfUnity 3 F) (x : M F) :
    KPContSectorCoveredQuotientVocabulary.q F ζ hζ U
      (Quotient.mk (coveredRelation F ζ hζ U)
        (labeledA (placeEquiv F ζ hζ) x,
         KPCuspGenuineMonodromy.central F ζ hζ e * (H.atlas U).representative a.component)) = q a x := by
  have he := q_z F ζ hζ U e (Quotient.mk (coveredRelation F ζ hζ U)
    (labeledA (placeEquiv F ζ hζ) x, (H.atlas U).representative a.component))
  rw [z_mk] at he
  exact he

theorem compact_root_chart_geometry_source (a : ActualChart (U := U) (H := H))
    (C : Set (M F)) (hC : IsCompact C) (hD : C ⊆ omega a)
    (hI : ∀ g : Gamma a, (isotropyArrow a g).psi '' C = C) :
    let Q : rootsOfUnity 3 F × C → CoveredSpherical F ζ hζ U := fun p =>
      Quotient.mk (coveredRelation F ζ hζ U)
        (labeledA (placeEquiv F ζ hζ) p.2.val,
         KPCuspGenuineMonodromy.central F ζ hζ p.1 * (H.atlas U).representative a.component)
    Set.range Q = KPContSectorCoveredQuotientVocabulary.q F ζ hζ U ⁻¹' (q a '' C) ∧
      ∀ p r, Q p = Q r ↔ ∃ g : Gamma a,
        r.1 = p.1 * (isotropyArrow a g).root⁻¹ ∧
        r.2.val = (isotropyArrow a g).psi p.2.val := by
  dsimp only
  refine ⟨Set.Subset.antisymm ?_ ?_, root_fibers a C hD⟩
  · rintro _ ⟨p, rfl⟩
    exact ⟨p.2.val, p.2.property, (base_raw_root a p.1 p.2.val).symm⟩
  · rintro z ⟨x, hx, he⟩
    let v : CoveredSpherical F ζ hζ U := Quotient.mk (coveredRelation F ζ hζ U)
      (labeledA (placeEquiv F ζ hζ) x, (H.atlas U).representative a.component)
    have hv : KPContSectorCoveredQuotientVocabulary.q F ζ hζ U v = q a x := by
      have ht := base_raw_root a (1 : rootsOfUnity 3 F) x
      simpa [v] using ht
    obtain ⟨e, he⟩ := (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ U v z).mp (hv.trans he)
    refine ⟨(e, ⟨x,hx⟩), ?_⟩
    rw [he, z_mk]

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

end
