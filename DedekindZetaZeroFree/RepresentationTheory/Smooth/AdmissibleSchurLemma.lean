module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompactOpenFixedExactness

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Topology

private theorem average_action_invariant
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : SmoothRepresentation ρ)
    (U : CompactOpenLevel G) (u : U.toOpenSubgroup) (v : V) :
    compactOpenAverage ρ hρ U (ρ (u : G) v) = compactOpenAverage ρ hρ U v := by
  classical
  let K := Classical.choice (exists_finiteAveragingLevel ρ hρ U v)
  letI := K.finite
  letI := K.isNormal
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K.subgroup)
  let L : FiniteAveragingLevel ρ U (ρ (u : G) v) :=
    { subgroup := K.subgroup
      isOpen := K.isOpen
      isNormal := K.isNormal
      finite := K.finite
      fixes := by
        intro k
        have hk : u⁻¹ * k.val * u ∈ K.subgroup := by
          simpa using K.isNormal.conj_mem k.val k.property u⁻¹
        have hfix := K.fixes ⟨u⁻¹ * k.val * u, hk⟩
        calc
          ρ (k.val.val : G) (ρ (u : G) v) =
              ρ (u : G) (ρ ((u⁻¹ * k.val * u : U.toOpenSubgroup) : G) v) := by
                simp [map_mul, Module.End.mul_apply]
          _ = ρ (u : G) v := by rw [hfix] }
  rw [compactOpenAverage_eq_finite ρ hρ U (ρ (u : G) v) L Quotient.out
    (fun q => QuotientGroup.out_eq' q),
    compactOpenAverage_eq_finite ρ hρ U v K Quotient.out
    (fun q => QuotientGroup.out_eq' q)]
  change (Nat.card (U.toOpenSubgroup ⧸ K.subgroup) : ℂ)⁻¹ •
      (∑ q : U.toOpenSubgroup ⧸ K.subgroup, ρ ((Quotient.out q : U.toOpenSubgroup) : G) (ρ (u : G) v)) =
    (Nat.card (U.toOpenSubgroup ⧸ K.subgroup) : ℂ)⁻¹ •
      (∑ q : U.toOpenSubgroup ⧸ K.subgroup, ρ ((Quotient.out q : U.toOpenSubgroup) : G) v)
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk u))
  intro q
  let a : U.toOpenSubgroup := Quotient.out (q * QuotientGroup.mk u)
  let b : U.toOpenSubgroup := Quotient.out q * u
  have hab : (a : U.toOpenSubgroup ⧸ K.subgroup) = (b : U.toOpenSubgroup ⧸ K.subgroup) := by
    simp [a, b, QuotientGroup.mk_mul, QuotientGroup.out_eq']
  have hk : a⁻¹ * b ∈ K.subgroup := QuotientGroup.eq.mp hab
  have hfix := K.fixes ⟨a⁻¹ * b, hk⟩
  change ρ ((Quotient.out q : U.toOpenSubgroup) : G) (ρ (u : G) v) = ρ (a : G) v
  calc
    ρ ((Quotient.out q : U.toOpenSubgroup) : G) (ρ (u : G) v) = ρ (b : G) v := by
      simp [b, map_mul, Module.End.mul_apply]
    _ = ρ (a : G) (ρ ((a⁻¹ * b : U.toOpenSubgroup) : G) v) := by
      simp [map_mul, Module.End.mul_apply]
    _ = ρ (a : G) v := by rw [hfix]

theorem exists_smooth_dual_separating
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup V] [Module ℂ V]
    (hcompactOpen : ∀ U ∈ nhds (1 : G),
      ∃ J : CompactOpenLevel G, (J.toOpenSubgroup : Set G) ⊆ U)
    (ρ : Representation ℂ G V) (hρ : SmoothRepresentation ρ)
    (hadmissible : Admissible ρ) (v : V) (hv : v ≠ 0) :
    ∃ ℓ : Module.Dual ℂ V, SmoothVector ρ.dual ℓ ∧ ℓ v ≠ 0 := by
  classical
  obtain ⟨U, hU⟩ := (smoothVector_iff_compactOpen_fixed hcompactOpen ρ v).mp (hρ v)
  let W := fixedSubmodule ρ U.toOpenSubgroup.toSubgroup
  have hvW : (⟨v, hU⟩ : W) ≠ 0 := by
    intro he
    exact hv (congrArg Subtype.val he)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hvW
  let Av : V →ₗ[ℂ] W := (compactOpenAverage ρ hρ U).codRestrict W (by
    intro x
    change compactOpenAverage ρ hρ U x ∈ fixedSubmodule ρ U.toOpenSubgroup.toSubgroup
    rw [← compactOpenAverage_range ρ hρ U]
    exact ⟨x, rfl⟩)
  let ℓ : Module.Dual ℂ V := f.comp Av
  refine ⟨ℓ, ?_, ?_⟩
  · refine ⟨U.toOpenSubgroup, ?_⟩
    intro u hu
    ext x
    change ℓ (ρ u⁻¹ x) = ℓ x
    change f (Av (ρ u⁻¹ x)) = f (Av x)
    have hu' : u⁻¹ ∈ U.toOpenSubgroup := U.toOpenSubgroup.inv_mem hu
    have h := average_action_invariant ρ hρ U ⟨u⁻¹, hu'⟩ x
    exact congrArg f (Subtype.ext h)
  · change f (Av v) ≠ 0
    have hAv : compactOpenAverage ρ hρ U v = v := compactOpenAverage_fixed ρ hρ U v hU
    have he : Av v = ⟨v, hU⟩ := Subtype.ext hAv
    rw [he]
    exact hf

theorem admissible_irreducible_endomorphism_scalar
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (hcompactOpen : ∀ U ∈ nhds (1 : G),
      ∃ J : CompactOpenLevel G, (J.toOpenSubgroup : Set G) ⊆ U)
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hρ : SmoothRepresentation ρ) (hadmissible : Admissible ρ)
    (T : Representation.IntertwiningMap ρ ρ) :
    ∃ c : ℂ, T.toLinearMap = c • LinearMap.id := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨U, hU⟩ := (smoothVector_iff_compactOpen_fixed hcompactOpen ρ v).mp (hρ v)
  let W := fixedSubmodule ρ U.toOpenSubgroup.toSubgroup
  letI : Module.Finite ℂ W := hadmissible U
  have hvW : (⟨v, hU⟩ : W) ≠ 0 := by
    intro h
    exact hv (congrArg Subtype.val h)
  letI : Nontrivial W := ⟨⟨⟨v, hU⟩, 0, hvW⟩⟩
  let TW : Module.End ℂ W := fixedSpaceMap ρ ρ T U.toOpenSubgroup.toSubgroup
  obtain ⟨c, hc⟩ := TW.exists_eigenvalue
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hwV : (w : V) ≠ 0 := by
    intro h
    exact hw.2 (Subtype.ext h)
  have heq : T (w : V) = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  let S : Representation.IntertwiningMap ρ ρ := T - c • Representation.IntertwiningMap.id ρ
  have hS : S (w : V) = 0 := by
    change T (w : V) - c • (w : V) = 0
    exact sub_eq_zero.mpr heq
  have hzero : S = 0 := by
    rcases Representation.IsIrreducible.injective_or_eq_zero S with hi | hz
    · exact False.elim (hwV (hi (hS.trans (map_zero S).symm)))
    · exact hz
  refine ⟨c, ?_⟩
  have hT := sub_eq_zero.mp hzero
  exact congrArg Representation.IntertwiningMap.toLinearMap hT

end DedekindZetaZeroFree
