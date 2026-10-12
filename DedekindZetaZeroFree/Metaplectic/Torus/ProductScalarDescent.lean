module

public import DedekindZetaZeroFree.Metaplectic.Torus.RestrictedScalarEvaluations

@[expose] public section

open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

def RawUnitProductModel (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) : Prop :=
  Q.H = KPGlobalProductPolarizationCharacter.B F ζ hζ P ∧
  ∀ (r : Q.H) (s : KPGlobalProductPolarizationCharacter.B F ζ hζ P), r.val = s.val →
    Q.character r = KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T s /
      KPGlobalCenterRationalCharacter.positiveComplex
        (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)

def RawPureScalarFormula
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q) : Prop :=
  ∀ (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (g : KPGlobalTorusFunctionData.E F ζ hζ),
    (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) →
    (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) →
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val →
    v.val g = ∏ᶠ q, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q)

theorem raw_local_denominator_mul
    (C : RawLocalScalarData F ζ hζ P T) (q : HeightOneSpectrum (𝓞 F))
    (a t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate (a * t))) (1 / 6 : ℝ) : ℂ) =
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate a)) (1 / 6 : ℝ) : ℂ) *
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate t)) (1 / 6 : ℝ) : ℂ) := by
  rw [map_mul]
  have habs : (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate a * (C.canonical q).borel.coordinate t) : ℝ) =
      (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate a) : ℝ) *
      (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate t) : ℝ) := by
    change ‖((↑((C.canonical q).borel.coordinate a) : q.adicCompletion F) *
      (↑((C.canonical q).borel.coordinate t) : q.adicCompletion F))‖ = _
    exact norm_mul _ _
  rw [habs, ← Complex.ofReal_mul]
  congr 1
  exact Real.mul_rpow
    (by exact_mod_cast (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q)
      ((C.canonical q).borel.coordinate a)).le)
    (by exact_mod_cast (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q)
      ((C.canonical q).borel.coordinate t)).le)

theorem raw_local_evaluation_covariance
    (C : RawLocalScalarData F ζ hζ P T) (q : HeightOneSpectrum (𝓞 F))
    (a : (C.polarization q).L.comap (C.canonical q).heisenberg.π)
    (f : KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    C.evaluation q f (a.val * t) =
      ((C.polarization q).ωL a : ℂ) /
        (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
          ((C.canonical q).borel.coordinate a.val)) (1 / 6 : ℝ) : ℂ) *
      C.evaluation q f t := by
  rw [C.evaluation_formula, C.evaluation_formula, f.property a t,
    raw_local_denominator_mul F ζ hζ P T C q a.val t]
  change ((C.polarization q).ωL a : ℂ) * f.val t / _ = _
  ring

theorem raw_local_polarization_lift
    (C : RawLocalScalarData F ζ hζ P T)
    (x : KPGlobalProductPolarizationCharacter.rawB F ζ hζ P)
    (q : HeightOneSpectrum (𝓞 F)) :
    ∃ a : (C.polarization q).L.comap (C.canonical q).heisenberg.π,
      a.val.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (x.val (Sum.inr q)) := by
  obtain ⟨b, hb⟩ := KPGlobalProductPolarizationCharacter.raw_coordinate_mem F ζ hζ P x (Sum.inr q)
  have hmem : b.val.val ∈
      ((C.polarization q).L.comap (C.canonical q).heisenberg.π).map
        (KPLocalExceptionalConstruction.actualTorus F ζ hζ q).subtype := by
    rw [C.subgroup_matches]
    exact Subgroup.mem_map.mpr ⟨b.val, b.property, rfl⟩
  obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp hmem
  exact ⟨⟨a, ha⟩, hab.trans hb⟩

theorem raw_pure_product_covariance
    (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (rawA raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (a : ∀ q, (C.polarization q).L.comap (C.canonical q).heisenberg.π)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ha : ∀ q, (a q).val.val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (rawA (Sum.inr q)))
    (ht : ∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) :
    (∏ᶠ q, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) ((a q).val * t q)) =
    (∏ᶠ q, C.evaluation q (C.reference q) (a q).val) *
    (∏ᶠ q, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q)) := by
  have href : ∀ q, C.evaluation q (C.reference q) (a q).val =
      ((C.polarization q).ωL (a q) : ℂ) /
        (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
          ((C.canonical q).borel.coordinate (a q).val)) (1 / 6 : ℝ) : ℂ) := by
    intro q
    have hmem : (C.canonical q).heisenberg.π (a q).val ∈ (C.polarization q).L :=
      (a q).property
    rw [C.evaluation_formula, C.reference_formula, dif_pos hmem]
  have hvalues : ∀ q, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) ((a q).val * t q) =
      C.evaluation q (C.reference q) (a q).val * C.evaluation q
        (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q) := by
    intro q
    rw [raw_local_evaluation_covariance F ζ hζ P T C q, href]
  simp only [hvalues]
  apply finprod_mul_distrib
  · have hfin := restricted_local_evaluations_finite_support F ζ hζ P T C
      S hS (fun q => C.reference q) rawA (fun q => (a q).val) ha
    have heq : (fun q => C.evaluation q
        (if _h : q ∈ S then C.reference q else C.reference q) (a q).val) =
        (fun q => C.evaluation q (C.reference q) (a q).val) := by
      funext q
      split_ifs <;> rfl
    rw [heq] at hfin
    exact hfin
  · exact restricted_local_evaluations_finite_support F ζ hζ P T C S hS f raw t ht

theorem raw_local_central_denominator
    (C : RawLocalScalarData F ζ hζ P T) (q : HeightOneSpectrum (𝓞 F))
    (e : rootsOfUnity 3 F) :
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate ((C.canonical q).central e).val))
      (1 / 6 : ℝ) : ℂ) = 1 := by
  have he : e ^ 3 = 1 := Subtype.ext ((mem_rootsOfUnity 3 e.val).mp e.property)
  have hy : ((C.canonical q).borel.coordinate ((C.canonical q).central e).val) ^ 3 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, ← map_pow, he, map_one, Subgroup.coe_one, map_one]
  have hnorm : ‖(↑((C.canonical q).borel.coordinate
      ((C.canonical q).central e).val) : q.adicCompletion F)‖ = 1 := by
    have hp : ‖(↑((C.canonical q).borel.coordinate
        ((C.canonical q).central e).val) : q.adicCompletion F)‖ ^ 3 = 1 := by
      have hv := congrArg (fun u : (q.adicCompletion F)ˣ => ‖(u : q.adicCompletion F)‖) hy
      simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using hv
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (3 : ℕ) ≠ 0)).mp hp
  have hAbs : (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate ((C.canonical q).central e).val) : ℝ) = 1 := hnorm
  rw [hAbs]
  simp

theorem raw_local_central_evaluation_covariance
    (C : RawLocalScalarData F ζ hζ P T) (q : HeightOneSpectrum (𝓞 F))
    (e : rootsOfUnity 3 F)
    (f : KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    C.evaluation q f (((C.canonical q).central e).val * t) =
      (KPLocalExceptionalConstruction.ordinaryIota F ζ hζ e : ℂ) * C.evaluation q f t := by
  have hker : (C.canonical q).heisenberg.π ((C.canonical q).central e).val = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [(C.canonical q).heisenberg.quotient_kernel]
    exact ((C.canonical q).central e).property
  let a : (C.polarization q).L.comap (C.canonical q).heisenberg.π :=
    ⟨((C.canonical q).central e).val, by
      change (C.canonical q).heisenberg.π ((C.canonical q).central e).val ∈ (C.polarization q).L
      rw [hker]
      exact (C.polarization q).L.one_mem⟩
  rw [show ((C.canonical q).central e).val = a.val from rfl,
    raw_local_evaluation_covariance F ζ hζ P T C q a f t,
    (C.polarization q).extends_center a ((C.canonical q).central e).property]
  change ((C.canonical q).heisenberg.ω ((C.canonical q).central e) : ℂ) / _ * _ = _
  rw [(C.canonical q).central_character,
    raw_local_central_denominator F ζ hζ P T C q e, div_one]

private theorem finprod_finite_places {M : Type*} [CommMonoid M]
    (z : KPHilbert.Place F → M) (hz : ∀ w : InfinitePlace F, z (Sum.inl w) = 1) :
    (∏ᶠ v, z v) = ∏ᶠ q, z (Sum.inr q) := by
  classical
  calc
    (∏ᶠ v, z v) = ∏ᶠ v, if h : v ∈ Set.range (Sum.inr :
        HeightOneSpectrum (𝓞 F) → KPHilbert.Place F) then
        z (Sum.inr (Classical.choose h)) else 1 := by
      apply finprod_congr
      intro v
      split_ifs with h
      · rw [Classical.choose_spec h]
      · cases v with
        | inl w => exact hz w
        | inr q => exact (h ⟨q, rfl⟩).elim
    _ = ∏ᶠ q, z (Sum.inr q) := finprod_emb_domain'
      (Sum.inr_injective : Function.Injective (Sum.inr :
        HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)) (fun q => z (Sum.inr q))

theorem raw_pure_product_product_one_invariant
    (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (e : KPAdelicCoverRestrictedProduct.CentralTuples F)
    (he : KPAdelicCoverRestrictedProduct.centralProduct F e = 1)
    (heinf : ∀ w : InfinitePlace F, e (Sum.inl w) = 1)
    (t t' : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : ∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)))
    (ht' : ∀ q, (t' q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        ((KPAdelicCoverRestrictedProduct.centralTupleMap F ζ hζ e * raw) (Sum.inr q))) :
    (∏ᶠ q, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t' q)) =
    (∏ᶠ q, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q)) := by
  have hefin : Function.HasFiniteMulSupport (fun q => e (Sum.inr q)) :=
    (KPAdelicCoverRestrictedProduct.centralTuples_finiteSupport F e).preimage_embedding
      ⟨Sum.inr, Sum.inr_injective⟩
  let χ : rootsOfUnity 3 F →* ℂ :=
    (Units.coeHom ℂ).comp (KPLocalExceptionalConstruction.ordinaryIota F ζ hζ)
  have hχ : Function.HasFiniteMulSupport (fun q => χ (e (Sum.inr q))) :=
    hefin.comp χ.map_one
  have hval : ∀ q, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t' q) =
      χ (e (Sum.inr q)) * C.evaluation q
        (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q) := by
    intro q
    have htq : t' q = ((C.canonical q).central (e (Sum.inr q))).val * t q := by
      apply Subtype.ext
      rw [ht']
      change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) (e (Sum.inr q)) *
          raw (Sum.inr q)) = _
      rw [map_mul, ← ht]
      change KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (e (Sum.inr q)) *
        (t q).val = _
      rw [← (C.canonical q).central_actual]
      rfl
    rw [htq]
    exact raw_local_central_evaluation_covariance F ζ hζ P T C q (e (Sum.inr q)) _ _
  simp only [hval]
  rw [finprod_mul_distrib hχ
    (restricted_local_evaluations_finite_support F ζ hζ P T C S hS f raw t ht),
    ← χ.map_finprod hefin]
  have hep : (∏ᶠ q, e (Sum.inr q)) = 1 := by
    rw [← finprod_finite_places F (fun v => e v) heinf]
    exact he
  rw [hep, map_one, one_mul]

theorem raw_pure_product_quotient_independent
    (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (raw raw' : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t t' : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (hinf : ∀ w : InfinitePlace F, raw (Sum.inl w) = 1)
    (hinf' : ∀ w : InfinitePlace F, raw' (Sum.inl w) = 1)
    (ht : ∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)))
    (ht' : ∀ q, (t' q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw' (Sum.inr q)))
    (hquot : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw')) :
    (∏ᶠ q, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q)) =
    (∏ᶠ q, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t' q)) := by
  let A := KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
  let π := KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
  have hd : π (A (raw'⁻¹ * raw)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv]
    change (π (A raw'))⁻¹ * π (A raw) = 1
    rw [hquot, inv_mul_cancel]
  obtain ⟨u, hu⟩ := (QuotientGroup.eq_one_iff _).mp hd
  let s := KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ u
  let k := raw'⁻¹ * raw * s⁻¹
  have hk : k ∈ KPAdelicCoverRestrictedProduct.M F ζ hζ := by
    apply (QuotientGroup.eq_one_iff _).mp
    change A k = 1
    dsimp only [k]
    rw [map_mul, map_inv]
    change A (raw'⁻¹ * raw) * (KPAdelicCoverRestrictedProduct.scalarHom F ζ hζ u)⁻¹ = 1
    rw [← hu, mul_inv_cancel]
  obtain ⟨e, he, hek⟩ := Subgroup.mem_map.mp hk
  have hcomm : Commute k raw' := by
    exact (Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.M_central F ζ hζ hk) raw').symm
  have hraw : raw = KPAdelicCoverRestrictedProduct.centralTupleMap F ζ hζ e * (raw' * s) := by
    rw [hek]
    change raw = k * (raw' * s)
    rw [← mul_assoc, hcomm.eq, mul_assoc]
    dsimp only [k]
    group
  have hs : ∀ v : KPHilbert.Place F,
      KPPGLLocalCover.coverQuotient F ζ hζ v (s v) = 1 := by
    intro v
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v) u, rfl⟩
  have heinf : ∀ w : InfinitePlace F, e (Sum.inl w) = 1 := by
    intro w
    have hw := congrArg (fun x : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ =>
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) (x (Sum.inl w))) hraw
    rw [hinf] at hw
    change 1 = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)
      (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) (e (Sum.inl w)) *
        (raw' (Sum.inl w) * s (Sum.inl w))) at hw
    rw [map_mul, map_mul, hinf', map_one, hs, one_mul, mul_one] at hw
    apply KPPGLLocalCover.centralInjection_injective F ζ hζ (Sum.inl w)
    change KPPGLLocalCover.centralInjection F ζ hζ (Sum.inl w) (e (Sum.inl w)) = _
    rw [map_one]
    exact hw.symm
  have htbase : ∀ q, (t' q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) ((raw' * s) (Sum.inr q)) := by
    intro q
    change (t' q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (raw' (Sum.inr q) * s (Sum.inr q))
    rw [map_mul, hs, mul_one, ht']
  apply raw_pure_product_product_one_invariant F ζ hζ P T C S hS f
    (raw' * s) e he heinf t' t htbase
  intro q
  rw [← hraw]
  exact ht q

theorem raw_pure_product_function_descent
    (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q)) :
    ∃ w : KPGlobalTorusFunctionData.E F ζ hζ → ℂ,
      ∀ (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
        (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
        (g : KPGlobalTorusFunctionData.E F ζ hζ),
        (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) →
        (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) →
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val →
        w g = ∏ᶠ q, C.evaluation q
          (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q) := by
  let R (g : KPGlobalTorusFunctionData.E F ζ hζ) : Prop :=
    ∃ (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
      (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q),
      (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) ∧
      (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) ∧
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val
  let w (g : KPGlobalTorusFunctionData.E F ζ hζ) : ℂ :=
    if h : R g then
      ∏ᶠ q, C.evaluation q
        (if hq : q ∈ S then f ⟨q, hq⟩ else C.reference q)
        (Classical.choose (Classical.choose_spec h) q)
    else 0
  refine ⟨w, ?_⟩
  intro raw t g hinf ht hg
  have hR : R g := ⟨raw, t, hinf, ht, hg⟩
  dsimp only [w]
  rw [dif_pos hR]
  obtain ⟨hinf', ht', hg'⟩ := Classical.choose_spec (Classical.choose_spec hR)
  exact raw_pure_product_quotient_independent F ζ hζ P T C S hS f
    (Classical.choose hR) raw (Classical.choose (Classical.choose_spec hR)) t
    hinf' hinf ht' ht (hg'.trans hg.symm)

theorem raw_local_coordinate_norm_matches
    (C : RawLocalScalarData F ζ hζ P T) (q : HeightOneSpectrum (𝓞 F))
    (a : KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (b : KPGlobalProductPolarizationCharacter.LocalE F ζ hζ (Sum.inr q))
    (hab : a.val = b.val) :
    KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate a) =
    KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      (KPGlobalProductPolarizationCharacter.localRatio F ζ hζ (Sum.inr q) b) := by
  letI : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
    KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
  let y := ActualFiniteTorus.coordinate F ζ hζ q a
  let e := ActualFiniteTorus.sheet F ζ hζ q a
  have hn : a.val = KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) y :=
    (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.1 a
  let z := ((C.canonical q).central e).val
  have hz : z.val = KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e :=
    (C.canonical q).central_actual e
  have hx : (z⁻¹ * a).val = KPPGLLocalCover.A F ζ hζ (Sum.inr q) y := by
    change z.val⁻¹ * a.val = _
    rw [hn, hz, inv_mul_cancel_left]
  have hc : (C.canonical q).borel.coordinate a =
      (C.canonical q).borel.coordinate z * y := by
    rw [← (C.canonical q).coordinate_lift (z⁻¹ * a) y hx, map_mul, map_inv]
    simp
  have he : e ^ 3 = 1 := Subtype.ext ((mem_rootsOfUnity 3 e.val).mp e.property)
  have hzpow : ((C.canonical q).borel.coordinate z) ^ 3 = 1 := by
    dsimp only [z]
    rw [← map_pow, ← Subgroup.coe_pow, ← map_pow, he, map_one, Subgroup.coe_one, map_one]
  have hzn : ‖(↑((C.canonical q).borel.coordinate z) : q.adicCompletion F)‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (3 : ℕ) ≠ 0)).mp
    have hv := congrArg (fun u : (q.adicCompletion F)ˣ => ‖(u : q.adicCompletion F)‖) hzpow
    simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using hv
  have hy : y = KPGlobalProductPolarizationCharacter.localRatio F ζ hζ (Sum.inr q) b := by
    apply ProductPolarization.baseQuotient_diagonalHom_injective F (Sum.inr q)
    have hp := ProductPolarization.localRatioValue_spec F ζ hζ (Sum.inr q) b
    rw [← hab, hn, map_mul] at hp
    have hcentral : KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
        (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection]
      exact ⟨e, rfl⟩
    rw [hcentral, one_mul] at hp
    exact hp.symm
  apply NNReal.eq
  change ‖(↑((C.canonical q).borel.coordinate a) : q.adicCompletion F)‖ = _
  rw [hc, Units.val_mul, norm_mul, hzn, one_mul, hy]
  rfl

theorem raw_local_denominator_eq_adjusted_norm
    (C : RawLocalScalarData F ζ hζ P T) (q : HeightOneSpectrum (𝓞 F))
    (a : (C.polarization q).L.comap (C.canonical q).heisenberg.π)
    (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
      (P.localData (Sum.inr q)).L) (hab : a.val.val = b.val.val) :
    Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate a.val)) (1 / 6 : ℝ) =
    ‖(KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ P T (Sum.inr q) b : ℂ)‖ := by
  rw [raw_local_coordinate_norm_matches F ζ hζ P T C q a.val b.val hab]
  exact (adjustedLocalValue_preserves_modulus F ζ hζ P T (Sum.inr q) b).symm

theorem raw_reference_product_character
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : RawUnitProductModel F ζ hζ P T Q)
    (x : KPGlobalProductPolarizationCharacter.rawB F ζ hζ P)
    (h : Q.H)
    (a : ∀ q, (C.polarization q).L.comap (C.canonical q).heisenberg.π)
    (ha : ∀ q, (a q).val.val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (x.val (Sum.inr q)))
    (hinf : ∀ w : InfinitePlace F, x.val (Sum.inl w) = 1)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = h.val.val) :
    (∏ᶠ q, C.evaluation q (C.reference q) (a q).val) = (Q.character h : ℂ) := by
  let b : KPGlobalProductPolarizationCharacter.B F ζ hζ P :=
    ⟨h.val, hQ.1 ▸ h.property⟩
  let z (v : KPHilbert.Place F) := KPGlobalProductPolarizationCharacter.adjustedLocalValue
    F ζ hζ P T v (KPGlobalProductPolarizationCharacter.rawCoordinate F ζ hζ P x v)
  have hzfin := KPGlobalProductPolarizationCharacter.rawProduct_finiteSupport F ζ hζ P T x
  have hbval : ∀ v, (KPGlobalProductPolarizationCharacter.rawCoordinate F ζ hζ P x v).val.val =
      KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) := by
    intro v
    exact Classical.choose_spec
      (KPGlobalProductPolarizationCharacter.raw_coordinate_mem F ζ hζ P x v)
  have hzinf : ∀ w : InfinitePlace F, z (Sum.inl w) = 1 := by
    intro w
    have hbone : KPGlobalProductPolarizationCharacter.rawCoordinate F ζ hζ P x (Sum.inl w) = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hbval, hinf, map_one]
      rfl
    dsimp only [z]
    rw [hbone]
    simp only [KPGlobalProductPolarizationCharacter.adjustedLocalValue, map_one, one_mul]
    rw [T.complex_unchanged]
    rfl
  have hzqfin : Function.HasFiniteMulSupport (fun q => z (Sum.inr q)) :=
    hzfin.preimage_embedding ⟨Sum.inr, Sum.inr_injective⟩
  have heval : ∀ q, C.evaluation q (C.reference q) (a q).val =
      (z (Sum.inr q) : ℂ) / (‖(z (Sum.inr q) : ℂ)‖ : ℂ) := by
    intro q
    have hab := (ha q).trans (hbval (Sum.inr q)).symm
    have hmem : (C.canonical q).heisenberg.π (a q).val ∈ (C.polarization q).L :=
      (a q).property
    rw [C.evaluation_formula, C.reference_formula, dif_pos hmem,
      C.character_matches q (a q) _ hab,
      raw_local_denominator_eq_adjusted_norm F ζ hζ P T C q (a q) _ hab]
  let χ : ℂˣ →* ℂ := Units.coeHom ℂ
  let nχ : ℂˣ →* ℂ :=
    (Complex.ofRealHom.toMonoidHom).comp ((normHom : ℂ →*₀ ℝ).toMonoidHom.comp χ)
  have hχfin : Function.HasFiniteMulSupport (fun q => (z (Sum.inr q) : ℂ)) :=
    hzqfin.comp χ.map_one
  have hnfin : Function.HasFiniteMulSupport (fun q => (‖(z (Sum.inr q) : ℂ)‖ : ℂ)) :=
    hzqfin.comp nχ.map_one
  simp only [heval]
  rw [finprod_div_distrib hχfin hnfin]
  change (∏ᶠ q, χ (z (Sum.inr q))) / (∏ᶠ q, nχ (z (Sum.inr q))) = _
  rw [← χ.map_finprod hzqfin, ← nχ.map_finprod hzqfin]
  have hprod : (∏ᶠ q, z (Sum.inr q)) = KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b := by
    rw [← finprod_finite_places F z hzinf]
    exact (KPGlobalProductPolarizationCharacter.lambdaB_raw_formula F ζ hζ P T b x hx).symm
  rw [hprod]
  change (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b : ℂ) /
    (‖(KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b : ℂ)‖ : ℂ) = _
  rw [KPGlobalProductPolarizationCharacter.lambdaB_norm, hQ.2 h b rfl]
  simp [Units.val_div_eq_div_val, KPGlobalCenterRationalCharacter.positiveComplex]

 def covarianceExtension {G : Type*} [Group G] (H S : Subgroup G)
    (χ : H →* ℂˣ) (f : S → ℂ) (g : G) : ℂ :=
  if hg : ∃ (h : H) (x : S), g = h.val * x.val then
    (χ (Classical.choose hg) : ℂ) * f (Classical.choose (Classical.choose_spec hg))
  else 0

private theorem covarianceExtension_formula {G : Type*} [Group G] (H S : Subgroup G)
    (χ : H →* ℂˣ) (f : S → ℂ)
    (hf : ∀ (h : H.comap S.subtype) (x : S),
      f (h.val * x) = (χ ⟨h.val.val, h.property⟩ : ℂ) * f x)
    (h : H) (x : S) : covarianceExtension H S χ f (h.val * x.val) = (χ h : ℂ) * f x := by
  have hg : ∃ (a : H) (y : S), h.val * x.val = a.val * y.val := ⟨h, x, rfl⟩
  rw [covarianceExtension, dif_pos hg]
  let a := Classical.choose hg
  let y := Classical.choose (Classical.choose_spec hg)
  have he : h.val * x.val = a.val * y.val := Classical.choose_spec (Classical.choose_spec hg)
  have hk : a.val⁻¹ * h.val = y.val * x.val⁻¹ := by
    have hh := congrArg (fun g => a.val⁻¹ * g * x.val⁻¹) he
    simpa only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left] using hh
  let k : H.comap S.subtype := ⟨⟨a.val⁻¹ * h.val, hk ▸ S.mul_mem y.property (S.inv_mem x.property)⟩,
    H.mul_mem (H.inv_mem a.property) h.property⟩
  have hy : k.val * x = y := by
    apply Subtype.ext
    change (a.val⁻¹ * h.val) * x.val = y.val
    rw [hk, mul_assoc, inv_mul_cancel, mul_one]
  have hh : (⟨k.val.val, k.property⟩ : H) = a⁻¹ * h := rfl
  have hv := hf k x
  rw [hy, hh, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hv
  change (χ a : ℂ) * f y = (χ h : ℂ) * f x
  rw [hv]
  have hne : (χ a : ℂ) ≠ 0 := Units.ne_zero (χ a)
  field_simp

private theorem covarianceExtension_covariance {G : Type*} [Group G] (H S : Subgroup G)
    (χ : H →* ℂˣ) (f : S → ℂ)
    (hf : ∀ (h : H.comap S.subtype) (x : S),
      f (h.val * x) = (χ ⟨h.val.val, h.property⟩ : ℂ) * f x)
    (h : H) (g : G) : covarianceExtension H S χ f (h.val * g) =
      (χ h : ℂ) * covarianceExtension H S χ f g := by
  by_cases hg : ∃ (a : H) (x : S), g = a.val * x.val
  · obtain ⟨a, x, rfl⟩ := hg
    rw [← mul_assoc]
    change covarianceExtension H S χ f ((h * a).val * x.val) = _
    rw [covarianceExtension_formula H S χ f hf,
      covarianceExtension_formula H S χ f hf, map_mul, Units.val_mul, mul_assoc]
  · have hh : ¬ ∃ (a : H) (x : S), h.val * g = a.val * x.val := by
      rintro ⟨a, x, he⟩
      apply hg
      refine ⟨h⁻¹ * a, x, ?_⟩
      have hh := congrArg (fun z => h.val⁻¹ * z) he
      simpa only [mul_assoc, inv_mul_cancel_left, Subgroup.coe_mul, Subgroup.coe_inv] using hh
    simp only [covarianceExtension, dif_neg hg, dif_neg hh, mul_zero]

theorem raw_pure_scalar_descent_exists
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : RawUnitProductModel F ζ hζ P T Q)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q)) :
    ∃ v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q,
      RawPureScalarFormula F ζ hζ P T C Q S f v := by
  classical
  let φ := (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)
  let R : Subgroup (KPGlobalTorusFunctionData.E F ζ hζ) :=
    { carrier := {g | ∃ (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
        (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q),
        (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) ∧
        (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) ∧
        φ raw = g.val}
      one_mem' := by
        refine ⟨1, fun _ => 1, ?_, ?_, ?_⟩
        · intro w; rfl
        · intro q
          change 1 = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) 1
          rw [map_one]
        · exact φ.map_one
      mul_mem' := by
        rintro g k ⟨raw, t, hi, ht, hg⟩ ⟨raw', t', hi', ht', hk⟩
        refine ⟨raw * raw', fun q => t q * t' q, ?_, ?_, ?_⟩
        · intro w
          change raw (Sum.inl w) * raw' (Sum.inl w) = 1
          rw [hi, hi', one_mul]
        · intro q
          change (t q).val * (t' q).val =
            KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q) * raw' (Sum.inr q))
          rw [map_mul, ht, ht']
        · rw [map_mul, hg, hk]; rfl
      inv_mem' := by
        rintro g ⟨raw, t, hi, ht, hg⟩
        refine ⟨raw⁻¹, fun q => (t q)⁻¹, ?_, ?_, ?_⟩
        · intro w
          change (raw (Sum.inl w))⁻¹ = 1
          rw [hi, inv_one]
        · intro q
          change (t q).val⁻¹ =
            KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))⁻¹
          rw [ht, map_inv]
        · rw [map_inv, hg]; rfl }
  obtain ⟨w, hw⟩ := raw_pure_product_function_descent F ζ hζ P T C S hS f
  let wR : R → ℂ := fun x => w x.val
  have hcov : ∀ (h : Q.H.comap R.subtype) (x : R),
      wR (h.val * x) = (Q.character ⟨h.val.val, h.property⟩ : ℂ) * wR x := by
    intro h x
    obtain ⟨rawH, tH, hiH, htH, hgH⟩ := h.val.property
    obtain ⟨rawX, tX, hiX, htX, hgX⟩ := x.property
    let hQH : Q.H := ⟨h.val.val, h.property⟩
    let rH : KPGlobalProductPolarizationCharacter.rawB F ζ hζ P :=
      ⟨rawH, by
        change φ rawH ∈ (KPGlobalProductPolarizationCharacter.B F ζ hζ P).map
          (KPGlobalTorusFunctionData.E F ζ hζ).subtype
        rw [hgH]
        exact Subgroup.mem_map.mpr ⟨h.val.val, hQ.1 ▸ h.property, rfl⟩⟩
    choose a ha using raw_local_polarization_lift F ζ hζ P T C rH
    have haH : ∀ q, (a q).val = tH q := by
      intro q
      exact Subtype.ext ((ha q).trans (htH q).symm)
    have htprod : ∀ q, ((a q).val * tX q).val =
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) ((rawH * rawX) (Sum.inr q)) := by
      intro q
      change (a q).val.val * (tX q).val =
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (rawH (Sum.inr q) * rawX (Sum.inr q))
      rw [map_mul, ha, htX]
    have hiprod : ∀ v : InfinitePlace F, (rawH * rawX) (Sum.inl v) = 1 := by
      intro v
      change rawH (Sum.inl v) * rawX (Sum.inl v) = 1
      rw [hiH, hiX, one_mul]
    have hgprod : φ (rawH * rawX) = (h.val * x).val.val := by
      rw [map_mul, hgH, hgX]
      rfl
    change w (h.val * x).val = (Q.character hQH : ℂ) * w x.val
    rw [hw (rawH * rawX) (fun q => (a q).val * tX q) (h.val * x).val hiprod htprod hgprod,
      hw rawX tX x.val hiX htX hgX,
      raw_pure_product_covariance F ζ hζ P T C S hS f rawH rawX a tX ha htX,
      raw_reference_product_character F ζ hζ P T C Q hQ rH hQH a ha hiH hgH]
  let v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q :=
    ⟨covarianceExtension Q.H R Q.character.toMonoidHom wR,
      covarianceExtension_covariance Q.H R Q.character.toMonoidHom wR hcov⟩
  refine ⟨v, ?_⟩
  intro raw t g hi ht hg
  let x : R := ⟨g, ⟨raw, t, hi, ht, hg⟩⟩
  have hv := covarianceExtension_formula Q.H R Q.character.toMonoidHom wR hcov (1 : Q.H) x
  change covarianceExtension Q.H R Q.character.toMonoidHom wR g = _
  have hv' : covarianceExtension Q.H R Q.character.toMonoidHom wR g = w g := by
    simpa only [Subgroup.coe_one, one_mul, map_one, Units.val_one, wR] using hv
  exact hv'.trans (hw raw t g hi ht hg)

end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers
