module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Borel.LiftedFactorization

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneInductionRaw

open scoped Topology NNReal Matrix OnePoint Classical
open IsDedekindDomain NumberField MeasureTheory
variable (F : Type*) [Field F] [NumberField F]
  (v : HeightOneSpectrum (RingOfIntegers F))

section CoverProjection

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (π : G →* PGL2 F v)

def coveredBorel : Subgroup G := (upperBorel F v).comap π

def coveredTorus : Subgroup G := (diagonalTorus F v).comap π

def borelProjection : coveredBorel F v π →* upperBorel F v :=
  (π.comp (coveredBorel F v π).subtype).codRestrict (upperBorel F v) (fun b => b.property)

def deltaB : coveredBorel F v π →* (ℝ≥0)ˣ :=
  (ordinaryDelta F v).comp (borelProjection F v π)

def dB : coveredBorel F v π →* (ℝ≥0)ˣ := halfModulus (deltaB F v π)

theorem deltaB_eq (b : coveredBorel F v π) (A : GL2 F v)
    (hA : Matrix.ProjGenLinGroup.mk A = π b.val) (hupper : A 1 0 = 0) :
    ((deltaB F v π b : ℝ≥0) : ℝ) = ‖A 0 0 / A 1 1‖ := by
  exact ordinaryDelta_eq F v (borelProjection F v π b) A hA hupper

theorem deltaB_locallyConstant (hπ : Continuous π) :
    IsLocallyConstant (deltaB F v π) := by
  exact (ordinaryDelta_locallyConstant F v).comp_continuous
    ((hπ.comp continuous_subtype_val).subtype_mk (fun b => b.property))

theorem dB_locallyConstant (hπ : Continuous π) :
    IsLocallyConstant (dB F v π) := by
  exact halfModulus_locallyConstant _ (deltaB_locallyConstant F v π hπ)

theorem deltaB_upperRoot (x : LocalField F v) (b : coveredBorel F v π)
    (hb : π b.val = upperRootElement F v x) : deltaB F v π b = 1 := by
  change ordinaryDelta F v (borelProjection F v π b) = _
  have he : borelProjection F v π b =
      ⟨upperRootElement F v x, upperRootElement_mem F v x⟩ := Subtype.ext hb
  rw [he]
  exact ordinaryDelta_upperRoot F v x

theorem coveredBorel_closed (hπ : Continuous π) :
    IsClosed (coveredBorel F v π : Set G) := by
  exact (upperBorel_closed F v).preimage hπ

 def coveredFlagMap : SectionCosetSpace (coveredBorel F v π) → SectionCosetSpace (upperBorel F v) :=
  Quotient.map π (by
    intro a b hab
    apply (QuotientGroup.rightRel_apply).mpr
    have h := (QuotientGroup.rightRel_apply).mp hab
    change π (b * a⁻¹) ∈ upperBorel F v at h
    simpa only [map_mul, map_inv] using h)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
 theorem coveredFlagMap_bijective (hsurj : Function.Surjective π) : Function.Bijective (coveredFlagMap F v π) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    intro hab
    apply Quotient.sound
    apply (QuotientGroup.rightRel_apply).mpr
    have h := (QuotientGroup.rightRel_apply).mp (Quotient.eq.mp hab)
    change π (b * a⁻¹) ∈ upperBorel F v
    simpa only [map_mul, map_inv] using h
  · intro a
    induction a using Quotient.inductionOn with | h a =>
    obtain ⟨b, rfl⟩ := hsurj a
    exact ⟨Quotient.mk _ b, rfl⟩

omit [IsTopologicalGroup G] in
 theorem coveredFlagMap_quotient (hπ : Continuous π) (hopen : IsOpenMap π)
    (hsurj : Function.Surjective π) : Topology.IsQuotientMap (coveredFlagMap F v π) := by
  have hq : Topology.IsQuotientMap
      (Quotient.mk (QuotientGroup.rightRel (upperBorel F v))) := by
    exact MulAction.isOpenQuotientMap_quotientMk.isQuotientMap
  have hc : Topology.IsQuotientMap (coveredFlagMap F v π ∘
      Quotient.mk (QuotientGroup.rightRel (coveredBorel F v π))) :=
    hq.comp (hopen.isQuotientMap hπ hsurj)
  exact hc.of_comp_of_isCoinducing isQuotientMap_quot_mk.isCoinducing

def coveredFlagHomeomorph (hπ : Continuous π) (hopen : IsOpenMap π)
    (hsurj : Function.Surjective π) :
    SectionCosetSpace (coveredBorel F v π) ≃ₜ OnePoint (LocalField F v) := by
  let e := Equiv.ofBijective (coveredFlagMap F v π) (coveredFlagMap_bijective F v π hsurj)
  have hq := coveredFlagMap_quotient F v π hπ hopen hsurj
  have hi : Continuous e.symm := by
    apply hq.continuous_iff.mpr
    change Continuous (e.symm ∘ e)
    simpa using (continuous_id : Continuous (id : SectionCosetSpace (coveredBorel F v π) → _))
  let he : SectionCosetSpace (coveredBorel F v π) ≃ₜ SectionCosetSpace (upperBorel F v) :=
    { toEquiv := e
      continuous_toFun := hq.continuous
      continuous_invFun := hi }
  exact he.trans (ordinaryFlagHomeomorph F v)

theorem coveredFlag_compact (hπ : Continuous π) (hopen : IsOpenMap π)
    (hsurj : Function.Surjective π) :
    IsCompact (Set.univ : Set (SectionCosetSpace (coveredBorel F v π))) := by
  simpa using (coveredFlagHomeomorph F v π hπ hopen hsurj).isCompact_preimage.mpr
    (isCompact_univ : IsCompact (Set.univ : Set (OnePoint (LocalField F v))))

def coveredUpperRoot (n : Multiplicative (LocalField F v) →* G) : Subgroup G := n.range

theorem coveredTorus_le_Borel : coveredTorus F v π ≤ coveredBorel F v π := by
  intro g hg
  obtain ⟨A, hA, h10, h01⟩ := hg
  exact ⟨A, hA, h10⟩

theorem rootLift_mem_Borel (n : Multiplicative (LocalField F v) →* G)
    (hn : ∀ x, π (n x) = ordinaryUpperRootHom F v x)
    (x : Multiplicative (LocalField F v)) : n x ∈ coveredBorel F v π := by
  change π (n x) ∈ upperBorel F v
  rw [hn]
  exact upperRootElement_mem F v (Multiplicative.toAdd x)

 theorem uniqueTorusFactor
    (n : Multiplicative (LocalField F v) →* G)
    (hn : ∀ x, π (n x) = ordinaryUpperRootHom F v x)
    (b : coveredBorel F v π) :
    ∃! t : coveredTorus F v π,
      ∃ a : LocalField F v, b.val = n (Multiplicative.ofAdd a) * t.val := by
  obtain ⟨a, t, ht, hfac, _, _, hu⟩ :=
    FiniteCentralBorel.exists_unique_lifted_factorization F v π n hn b.val b.property
  refine ⟨⟨t, ht⟩, ⟨a, hfac⟩, ?_⟩
  rintro t' ⟨a', hfac'⟩
  exact Subtype.ext (hu a' t'.val t'.property hfac').2

 def torusFactor
    (n : Multiplicative (LocalField F v) →* G)
    (hn : ∀ x, π (n x) = ordinaryUpperRootHom F v x)
    (b : coveredBorel F v π) : coveredTorus F v π :=
  Classical.choose (uniqueTorusFactor F v π n hn b)

private theorem torusFactor_spec
    (n : Multiplicative (LocalField F v) →* G)
    (hn : ∀ x, π (n x) = ordinaryUpperRootHom F v x)
    (b : coveredBorel F v π) :
    (∃ a : LocalField F v, b.val = n (Multiplicative.ofAdd a) *
      (torusFactor F v π n hn b).val) ∧
    (∀ t : coveredTorus F v π, (∃ a : LocalField F v,
      b.val = n (Multiplicative.ofAdd a) * t.val) →
      t = torusFactor F v π n hn b) :=
  Classical.choose_spec (uniqueTorusFactor F v π n hn b)

theorem exists_canonicalBorelRetraction [Finite π.ker]
    (hcentral : π.ker ≤ Subgroup.center G)
    (hπ : Function.Surjective π) (n : Multiplicative (LocalField F v) →* G)
    (hn : ∀ x, π (n x) = ordinaryUpperRootHom F v x) :
    ∃ q : coveredBorel F v π →* coveredTorus F v π,
      (∀ h : coveredTorus F v π,
        q ⟨h.val, coveredTorus_le_Borel F v π h.property⟩ = h) ∧
      (∀ x : Multiplicative (LocalField F v),
        q ⟨n x, rootLift_mem_Borel F v π n hn x⟩ = 1) ∧
      (∀ b : coveredBorel F v π,
        b.val * (q b : G)⁻¹ ∈ coveredUpperRoot F v n) := by
  let t := torusFactor F v π n hn
  have hfac (b : coveredBorel F v π) :
      ∃ a : LocalField F v, b.val = n (Multiplicative.ofAdd a) * (t b).val :=
    (torusFactor_spec F v π n hn b).1
  have huniq (b : coveredBorel F v π) (s : coveredTorus F v π)
      (hs : ∃ a : LocalField F v, b.val = n (Multiplicative.ofAdd a) * s.val) :
      s = t b := (torusFactor_spec F v π n hn b).2 s hs
  let q : coveredBorel F v π →* coveredTorus F v π :=
    { toFun := t
      map_one' := by
        apply Eq.symm
        apply huniq
        exact ⟨0, by simp⟩
      map_mul' := by
        intro b c
        apply Eq.symm
        apply huniq
        obtain ⟨a, ha⟩ := hfac b
        obtain ⟨d, hd⟩ := hfac c
        let r : LocalField F v :=
          borelRatio F v ⟨π (t b).val, coveredTorus_le_Borel F v π (t b).property⟩
        have hc := FiniteCentralBorel.torusLift_conjugates_root F v π hcentral n hn
          (t b).val (t b).property
          (coveredTorus_le_Borel F v π (t b).property) d
        have hmove : (t b).val * n (Multiplicative.ofAdd d) =
            n (Multiplicative.ofAdd (r * d)) * (t b).val := by
          exact (mul_inv_eq_iff_eq_mul).mp hc
        refine ⟨a + r * d, ?_⟩
        change b.val * c.val = n (Multiplicative.ofAdd (a + r * d)) *
          ((t b).val * (t c).val)
        rw [ha, hd]
        calc
          _ = n (Multiplicative.ofAdd a) * ((t b).val * n (Multiplicative.ofAdd d)) *
              (t c).val := by group
          _ = n (Multiplicative.ofAdd a) *
              (n (Multiplicative.ofAdd (r * d)) * (t b).val) * (t c).val := by
            rw [hmove]
          _ = _ := by simp [← map_mul, ← mul_assoc] }
  refine ⟨q, ?_, ?_, ?_⟩
  · intro h
    change t _ = h
    apply Eq.symm
    apply huniq
    exact ⟨0, by simp⟩
  · intro x
    change t _ = 1
    apply Eq.symm
    apply huniq
    exact ⟨Multiplicative.toAdd x, by simp⟩
  · intro b
    obtain ⟨a, ha⟩ := hfac b
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    change n (Multiplicative.ofAdd a) = b.val * (t b).val⁻¹
    rw [ha]
    simp [mul_assoc]

end CoverProjection

end DedekindZetaZeroFree.KPRankOneInductionRaw

end

end
