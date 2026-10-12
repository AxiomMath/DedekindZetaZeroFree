module

public import DedekindZetaZeroFree.Metaplectic.Torus.ComplexPolarizationCharacters

@[expose] public section

section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.ProductPolarization.UnramifiedExtension
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology localCoverTopology

theorem center_character_trivial_on_good_compact
    (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (z : localCenter F ζ hζ (Sum.inr q))
    (hz : z.val.val ∈ KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q)) :
    localOmega F ζ hζ (Sum.inr q) z = 1 := by
  classical
  obtain ⟨g, hg, hgz⟩ := hz
  change g ∈ KPAdelicCoverRestrictedProduct.finiteCompact F ζ hζ q at hg
  rw [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hgood] at hg
  obtain ⟨k, rfl⟩ := hg
  rw [localOmega_raw_formula F ζ hζ (Sum.inr q) z _ hgz]
  have hp := (localRatioValue_spec F ζ hζ (Sum.inr q) z.val).trans
    (congrArg (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)) hgz).symm
  rw [KPPGLLocalCover.projection_coverQuotient] at hp
  change KPPGLLocalCover.baseQuotient F (Sum.inr q)
      (diagonalHom F (Sum.inr q) (localRatio F ζ hζ (Sum.inr q) z.val)) =
    KPPGLLocalCover.baseQuotient F (Sum.inr q) (KPTameCompact.inclusion F q k) at hp
  simp only [KPPGLLocalCover.baseQuotient] at hp
  rw [QuotientGroup.mk'_eq_mk'] at hp
  obtain ⟨s, hs, heq⟩ := hp
  obtain ⟨a, rfl⟩ := hs
  have hc := congrArg (fun m : KPLocalCover.LocalGL2 F (Sum.inr q) =>
    (m : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inr q))) 1 0) heq
  have hc0 : KPTameCompact.c F q k = 0 := by
    simpa [diagonalHom, KubotaRankTwo.coe_d, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply,
      KPTameCompact.inclusion, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply] using hc.symm
  have hkap : KPTameCompact.kappa F q ζ hζ k = 1 :=
    KPTameCompact.kappa_zero F q ζ hζ k hc0
  have hnorm := KPTameCompact.det_norm_and_entries F q k
  have hprod : ‖KPTameCompact.a F q k‖ * ‖KPTameCompact.d F q k‖ = 1 := by
    have hd := hnorm.1
    simpa [KPTameCompact.Δ, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_two, KPTameCompact.inclusion, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply, hc0, norm_mul] using hd
  have ha : ‖KPTameCompact.a F q k‖ = 1 := by
    nlinarith [hnorm.2 0 0, hnorm.2 1 1, norm_nonneg (KPTameCompact.a F q k)]
  have hd : ‖KPTameCompact.d F q k‖ = 1 := by
    nlinarith [hnorm.2 0 0, hnorm.2 1 1, norm_nonneg (KPTameCompact.d F q k)]
  have h1 : IsUnit (KPTameCompact.a F q k) :=
    isUnit_iff_ne_zero.mpr (by intro h; simpa [h] using ha)
  have h2 : IsUnit (KPTameCompact.d F q k) :=
    isUnit_iff_ne_zero.mpr (by intro h; simpa [h] using hd)
  rw [KPGlobalCenterRationalCharacter.localValue, dif_pos ⟨h1, h2⟩]
  have habs : KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      (h1.unit * h2.unit⁻¹) = 1 := by
    apply NNReal.eq
    simp [KPGlobalCenterRationalCharacter.localAbs, IsUnit.unit_spec,
      norm_mul, norm_inv, ha, hd]
  change KPGlobalTorusFunctionData.iota F ζ hζ (KPTameCompact.kappa F q ζ hζ k) *
    KPGlobalCenterRationalCharacter.positiveComplex
      (KPGlobalCenterRationalCharacter.sixthPower
        (Units.mk0 (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
          (h1.unit * h2.unit⁻¹)) _)) = 1
  have hu : Units.mk0 (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      (h1.unit * h2.unit⁻¹))
      (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q) _)) = 1 :=
    Units.ext habs
  rw [hkap, hu]
  simp

end
end DedekindZetaZeroFree.ProductPolarization.UnramifiedExtension

end

section

namespace DedekindZetaZeroFree.ProductPolarization.UnramifiedExtension
noncomputable section
set_option autoImplicit false

theorem open_character_extension_trivial_on_subgroup
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C A S : Subgroup H) (hCA : C ≤ A) (hSA : S ≤ A)
    (hCopen : IsOpen (C : Set H))
    (hAabelian : ∀ x ∈ A, ∀ y ∈ A, Commute x y)
    (ω : C →ₜ* ℂˣ)
    (hω : ∀ c : C, c.val ∈ S → ω c = 1) :
    ∃ ωA : A →ₜ* ℂˣ,
      (∀ (a : A) (c : C), a.val = c.val → ωA a = ω c) ∧
      (∀ a : A, a.val ∈ S → ωA a = 1) := by
  classical
  let p : C × S →* H :=
    { toFun := fun x => x.1.val * x.2.val
      map_one' := mul_one _
      map_mul' := by
        intro x y
        change (x.1.val * y.1.val) * (x.2.val * y.2.val) =
          (x.1.val * x.2.val) * (y.1.val * y.2.val)
        have h := (hAabelian y.1.val (hCA y.1.property) x.2.val (hSA x.2.property)).eq
        calc
          _ = x.1.val * (y.1.val * x.2.val) * y.2.val := by simp only [mul_assoc]
          _ = x.1.val * (x.2.val * y.1.val) * y.2.val := by rw [h]
          _ = _ := by simp only [mul_assoc] }
  let g : C × S →* ℂˣ := ω.toMonoidHom.comp (MonoidHom.fst C S)
  have hker : p.rangeRestrict.ker ≤ g.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    have hx' : x.1.val * x.2.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hc : x.1.val ∈ S := by
      have heq : x.1.val = x.2.val⁻¹ := eq_inv_of_mul_eq_one_left hx'
      rw [heq]
      exact S.inv_mem x.2.property
    exact hω x.1 hc
  let φ : p.range →* ℂˣ := p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective ⟨g, hker⟩
  have hφ : ∀ x : C × S, φ (p.rangeRestrict x) = ω x.1 := by
    intro x
    change φ (p.rangeRestrict x) = g x
    exact p.rangeRestrict.liftOfRightInverse_comp_apply
      (Function.surjInv p.rangeRestrict_surjective)
      (Function.rightInverse_surjInv p.rangeRestrict_surjective) ⟨g, hker⟩ x
  have hCB : C ≤ p.range := by
    intro c hc
    exact ⟨(⟨c, hc⟩, 1), mul_one c⟩
  have hSB : S ≤ p.range := by
    intro s hs
    exact ⟨(1, ⟨s, hs⟩), one_mul s⟩
  have hBA : p.range ≤ A := by
    intro b hb
    obtain ⟨x, rfl⟩ := hb
    exact A.mul_mem (hCA x.1.property) (hSA x.2.property)
  let i : C →* p.range := Subgroup.inclusion hCB
  have hext : ∀ c : C, φ (i c) = ω c := by
    intro c
    have heq : i c = p.rangeRestrict (c, 1) := by
      apply Subtype.ext
      exact (mul_one c.val).symm
    rw [heq]
    exact hφ (c, 1)
  have hcont : Continuous φ := by
    apply continuous_of_continuousAt_one φ
    have hiind : Topology.IsInducing i := (Topology.IsEmbedding.inclusion hCB).isInducing
    have hirange : Set.range i = {b : p.range | b.val ∈ C} := by
      ext b
      constructor
      · rintro ⟨c, rfl⟩
        exact c.property
      · intro hb
        exact ⟨⟨b.val, hb⟩, rfl⟩
    have hmem : Set.range i ∈ nhds (i (1 : C)) := by
      rw [hirange]
      exact (hCopen.preimage continuous_subtype_val).mem_nhds C.one_mem
    have hc : Continuous (φ ∘ i) := by
      have heq : φ ∘ i = ω := funext hext
      rw [heq]
      exact ω.continuous
    have hcat := (hiind.continuousAt_iff' hmem).mp (hc.continuousAt (x := (1 : C)))
    simpa only [map_one] using hcat
  have hBopen : IsOpen (p.range : Set H) := Subgroup.isOpen_mono hCB hCopen
  obtain ⟨ωA, hωA⟩ := KPLocalPolarization.continuous_character_extension
    p.range A hBA hBopen hAabelian ⟨φ, hcont⟩
  refine ⟨ωA, ?_, ?_⟩
  · intro a c hac
    rw [hωA a (hac ▸ hCB c.property)]
    change φ _ = ω c
    have heq : (⟨a.val, hac ▸ hCB c.property⟩ : p.range) = i c := by
      exact Subtype.ext hac
    rw [heq]
    exact hext c
  · intro a ha
    rw [hωA a (hSB ha)]
    change φ _ = 1
    have heq : (⟨a.val, hSB ha⟩ : p.range) = p.rangeRestrict (1, ⟨a.val, ha⟩) := by
      apply Subtype.ext
      exact (one_mul a.val).symm
    rw [heq, hφ]
    exact ω.map_one

end
end DedekindZetaZeroFree.ProductPolarization.UnramifiedExtension

end

section
open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ProductPolarization
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology localCoverTopology

structure LocalPolarization (v : KPHilbert.Place F) where
  L : Subgroup (LocalD F v)
  maximal : IsMaximalIsotropic F (KPGlobalCubicIdelePairing.localPairing F ζ hζ v) L
  lambda : localPreimage F ζ hζ v L →ₜ* ℂˣ
  extends_center : ∀ (b : localPreimage F ζ hζ v L) (z : localCenter F ζ hζ v),
    b.val = z.val → lambda b = localOmega F ζ hζ v z
  modulus : ∀ b : localPreimage F ζ hζ v L,
    ‖(lambda b : ℂ)‖ = Real.rpow
      (KPGlobalCenterRationalCharacter.localAbs F v (localRatio F ζ hζ v b.val)) (1 / 6 : ℝ)

def IsUnramified (q : HeightOneSpectrum (𝓞 F))
    (P : LocalPolarization F ζ hζ (Sum.inr q)) : Prop :=
  ¬ KPAdelicCoverRestrictedProduct.Bad F q ∧
  P.L = KPGlobalCubicIdelePairing.U F (Sum.inr q) ∧
  ∀ b : localPreimage F ζ hζ (Sum.inr q) P.L,
    b.val.val ∈ KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q) →
    P.lambda b = 1

structure CompatibleLocalData where
  localData : ∀ v : KPHilbert.Place F, LocalPolarization F ζ hζ v
  complex_full : ∀ w : InfinitePlace F, (localData (Sum.inl w)).L = ⊤
  unramified_almost_everywhere : ∀ᶠ q in Filter.cofinite,
    IsUnramified F ζ hζ q (localData (Sum.inr q))

private theorem pair_one (v : KPHilbert.Place F) (x : LocalD F v) :
    KPGlobalCubicIdelePairing.localPairing F ζ hζ v x 1 = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (CubicCharacters.cubes (KPHilbert.Completion F v)ˣ) x
  change KPHilbert.B3 F ζ hζ v y 1 = 1
  simpa using ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 y 1).2

theorem tame_unit_maximal_isotropic (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q) :
    IsMaximalIsotropic F (KPGlobalCubicIdelePairing.localPairing F ζ hζ (Sum.inr q))
      (KPGlobalCubicIdelePairing.U F (Sum.inr q)) := by
  refine ⟨fun a ha b hb => KPGlobalCubicIdelePairing.tame_unit_isotropic F ζ hζ q hgood a b ha hb, ?_⟩
  intro N hUN hN
  apply le_antisymm _ hUN
  intro a ha
  let U := KPGlobalCubicIdelePairing.U F (Sum.inr q)
  let d : KPGlobalCubicIdelePairing.LocalValuationClasses F (Sum.inr q) := QuotientGroup.mk' U a
  obtain ⟨d₀, hd₀, huniq⟩ := (KPGlobalCubicIdelePairing.tame_unit_valuation_perfect
    F ζ hζ q hgood).2 (1 : U →* rootsOfUnity 3 F)
  have hd : ∀ u : U, KPGlobalCubicIdelePairing.unitValuationPairing F ζ hζ q hgood u d = 1 := by
    intro u
    exact hN u.val (hUN u.property) a ha
  have h1 : ∀ u : U, KPGlobalCubicIdelePairing.unitValuationPairing F ζ hζ q hgood u 1 = 1 := by
    intro u
    exact pair_one F ζ hζ (Sum.inr q) u.val
  have heq : d = 1 := (huniq d hd).trans (huniq 1 h1).symm
  exact (QuotientGroup.eq_one_iff a).mp heq

theorem complex_full_maximal_isotropic (w : InfinitePlace F) :
    IsMaximalIsotropic F (KPGlobalCubicIdelePairing.localPairing F ζ hζ (Sum.inl w))
      (⊤ : Subgroup (LocalD F (Sum.inl w))) := by
  letI := KPGlobalCubicIdelePairing.local_complex_trivial F w
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    rw [Subsingleton.elim y 1]
    exact pair_one F ζ hζ (Sum.inl w) x
  · intro N hN _
    exact le_antisymm le_top hN

theorem local_maximal_isotropic_exists (v : KPHilbert.Place F) :
    ∃ L : Subgroup (LocalD F v),
      IsMaximalIsotropic F (KPGlobalCubicIdelePairing.localPairing F ζ hζ v) L := by
  classical
  have hfinite : Finite (LocalD F v) := by
    cases v with
    | inl w =>
      letI := KPGlobalCubicIdelePairing.local_complex_trivial F w
      infer_instance
    | inr q =>
      letI : ValuativeRel (q.adicCompletion F) :=
        ClassFieldTheory.finitePlaceCompletionValuativeRel F q
      letI : IsNonarchimedeanLocalField (q.adicCompletion F) :=
        ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
      exact ClassFieldTheory.powerClassGroup_finite (q.adicCompletion F) 3
        (Nat.cast_ne_zero.mpr (by decide))
  letI := hfinite
  let isotropic (L : Subgroup (LocalD F v)) : Prop :=
    ∀ x ∈ L, ∀ y ∈ L, KPGlobalCubicIdelePairing.localPairing F ζ hζ v x y = 1
  have hne : {L : Subgroup (LocalD F v) | isotropic L}.Nonempty := by
    refine ⟨⊥, ?_⟩
    intro x hx y hy
    rw [Subgroup.mem_bot] at hy
    rw [hy]
    exact pair_one F ζ hζ v x
  obtain ⟨L, hL, hmax⟩ := Set.Finite.exists_maximal
    (Set.toFinite {L : Subgroup (LocalD F v) | isotropic L}) hne
  refine ⟨L, hL, ?_⟩
  intro N hLN hN
  exact le_antisymm (hmax hN hLN) hLN

theorem localProjection_cube (v : KPHilbert.Place F) (b : LocalE F ζ hζ v) :
    localProjection F ζ hζ v (b ^ 3) = 1 := by
  change KPGlobalCubicIdelePairing.localClass F v (localRatio F ζ hζ v (b ^ 3)) = 1
  rw [map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨localRatio F ζ hζ v b, rfl⟩

theorem localAbs_cube (v : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) :
    KPGlobalCenterRationalCharacter.localAbs F v (y ^ 3) =
      KPGlobalCenterRationalCharacter.localAbs F v y ^ 3 := by
  cases v with
  | inl w =>
    simp only [KPGlobalCenterRationalCharacter.localAbs, Units.val_pow_eq_pow_val, nnnorm_pow]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 2]
  | inr q =>
    simp only [KPGlobalCenterRationalCharacter.localAbs, Units.val_pow_eq_pow_val, nnnorm_pow]

theorem modulus_of_extends_center (v : KPHilbert.Place F)
    (L : Subgroup (LocalD F v))
    (lambda : localPreimage F ζ hζ v L →ₜ* ℂˣ)
    (hext : ∀ (b : localPreimage F ζ hζ v L) (z : localCenter F ζ hζ v),
      b.val = z.val → lambda b = localOmega F ζ hζ v z)
    (hcenter : ∀ z : localCenter F ζ hζ v,
      ‖(localOmega F ζ hζ v z : ℂ)‖ = Real.rpow
        (KPGlobalCenterRationalCharacter.localAbs F v (localRatio F ζ hζ v z.val))
        (1 / 6 : ℝ)) :
    ∀ b : localPreimage F ζ hζ v L, ‖(lambda b : ℂ)‖ = Real.rpow
      (KPGlobalCenterRationalCharacter.localAbs F v (localRatio F ζ hζ v b.val))
      (1 / 6 : ℝ) := by
  intro b
  let z : localCenter F ζ hζ v := ⟨b.val ^ 3, localProjection_cube F ζ hζ v b.val⟩
  have hz : lambda (b ^ 3) = localOmega F ζ hζ v z := hext (b ^ 3) z rfl
  have hn := congrArg (fun x : ℂˣ => ‖(x : ℂ)‖) hz
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow, hcenter] at hn
  change ‖(lambda b : ℂ)‖ ^ 3 =
    ((KPGlobalCenterRationalCharacter.localAbs F v
      (localRatio F ζ hζ v (b.val ^ 3)) : ℝ) ^ (1 / 6 : ℝ)) at hn
  rw [map_pow, localAbs_cube, NNReal.coe_pow, ← Real.rpow_pow_comm (by positivity)] at hn
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (by positivity) _) (by decide : (3 : ℕ) ≠ 0)).mp hn

theorem local_polarization_of_open_abelian_preimage (v : KPHilbert.Place F)
    [IsTopologicalGroup (LocalE F ζ hζ v)]
    (L : Subgroup (LocalD F v))
    (hL : IsMaximalIsotropic F (KPGlobalCubicIdelePairing.localPairing F ζ hζ v) L)
    (hopen : IsOpen (localCenter F ζ hζ v : Set (LocalE F ζ hζ v)))
    (hab : ∀ x ∈ localPreimage F ζ hζ v L, ∀ y ∈ localPreimage F ζ hζ v L,
      Commute x y)
    (hcenter : ∀ z : localCenter F ζ hζ v,
      ‖(localOmega F ζ hζ v z : ℂ)‖ = Real.rpow
        (KPGlobalCenterRationalCharacter.localAbs F v (localRatio F ζ hζ v z.val))
        (1 / 6 : ℝ)) :
    ∃ P : LocalPolarization F ζ hζ v, P.L = L := by
  have hCA : localCenter F ζ hζ v ≤ localPreimage F ζ hζ v L := by
    intro x hx
    change localProjection F ζ hζ v x ∈ L
    change localProjection F ζ hζ v x = 1 at hx
    rw [hx]
    exact L.one_mem
  obtain ⟨lambda, hlambda⟩ := KPLocalPolarization.continuous_character_extension
    (localCenter F ζ hζ v) (localPreimage F ζ hζ v L) hCA hopen hab
    (localOmega F ζ hζ v)
  have hext : ∀ (b : localPreimage F ζ hζ v L) (z : localCenter F ζ hζ v),
      b.val = z.val → lambda b = localOmega F ζ hζ v z := by
    intro b z hz
    have hb : b.val ∈ localCenter F ζ hζ v := hz ▸ z.property
    have heq : (⟨b.val, hb⟩ : localCenter F ζ hζ v) = z := Subtype.ext hz
    simpa only [heq] using hlambda b hb
  exact ⟨{ L := L
           maximal := hL
           lambda := lambda
           extends_center := hext
           modulus := modulus_of_extends_center F ζ hζ v L lambda hext hcenter }, rfl⟩

private theorem normal_word_exists (v : KPHilbert.Place F) (g : LocalE F ζ hζ v) :
    ∃ e, g.val = KPPGLLocalCover.centralInjection F ζ hζ v e *
      KPPGLLocalCover.A F ζ hζ v (localRatio F ζ hζ v g) := by
  letI : (KPPGLLocalCover.scalarSubgroup F v).Normal :=
    KPPGLLocalCover.scalarSubgroup_normal F v
  let p := KPPGLLocalCover.projection F ζ hζ v
  have hp : p (KPPGLLocalCover.A F ζ hζ v (localRatio F ζ hζ v g)) = p g.val :=
    localRatioValue_spec F ζ hζ v g
  have hk : g.val * (KPPGLLocalCover.A F ζ hζ v (localRatio F ζ hζ v g))⁻¹ ∈ p.ker := by
    change p (_ * _) = 1
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  rw [show p.ker = (KPPGLLocalCover.centralInjection F ζ hζ v).range from
    (KPPGLLocalCover.range_centralInjection_eq_ker_projection F ζ hζ v).symm] at hk
  obtain ⟨e, he⟩ := hk
  exact ⟨e, by rw [he]; simp⟩

theorem local_center_modulus (v : KPHilbert.Place F) (z : localCenter F ζ hζ v) :
    ‖(localOmega F ζ hζ v z : ℂ)‖ = Real.rpow
      (KPGlobalCenterRationalCharacter.localAbs F v (localRatio F ζ hζ v z.val))
      (1 / 6 : ℝ) := by
  obtain ⟨e, he⟩ := normal_word_exists F ζ hζ v z.val
  let y := localRatio F ζ hζ v z.val
  let g := KPLocalCover.centralInjection F ζ hζ v e *
    KPStandardLocalRootLifts.A F ζ hζ v y
  have hg : KPPGLLocalCover.coverQuotient F ζ hζ v g = z.val.val := by
    rw [he]
    change KPPGLLocalCover.coverQuotient F ζ hζ v (_ * _) = _
    rw [map_mul]
    rfl
  rw [localOmega_raw_formula F ζ hζ v z g hg]
  have hval : KPGlobalCenterRationalCharacter.localValue F ζ hζ v g =
      KPGlobalTorusFunctionData.iota F ζ hζ e *
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.sixthPower
            (Units.mk0 (KPGlobalCenterRationalCharacter.localAbs F v y)
              (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F v y)))) := by
    cases v with
    | inl w => exact KPGlobalCenterRationalCharacter.localValue_complex F ζ hζ w e y
    | inr q =>
      have hy : y ∈ CubicCharacters.cubes (KPHilbert.Completion F (Sum.inr q))ˣ := by
        exact (QuotientGroup.eq_one_iff y).mp z.property
      exact KPGlobalCenterRationalCharacter.localValue_finite_cube F ζ hζ q e ⟨y, hy⟩
  rw [hval, Units.val_mul, norm_mul]
  have hn : ‖(KPGlobalTorusFunctionData.iota F ζ hζ e : ℂ)‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one (n := 3) _ (by decide)
    change ((KPGlobalTorusFunctionData.iota F ζ hζ e) ^ 3 : ℂˣ).val = 1
    rw [← map_pow, show e ^ 3 = 1 from Subtype.ext e.property, map_one]
    rfl
  rw [hn, one_mul]
  simp [KPGlobalCenterRationalCharacter.positiveComplex,
    KPGlobalCenterRationalCharacter.sixthPower, NNReal.coe_rpow,
    Real.rpow_nonneg (NNReal.coe_nonneg _) (1 / 6 : ℝ), y]
  positivity

theorem complex_local_polarization (w : InfinitePlace F) :
    ∃ P : LocalPolarization F ζ hζ (Sum.inl w), P.L = ⊤ := by
  haveI := KPGlobalCubicIdelePairing.local_complex_trivial F w
  have hAC : localPreimage F ζ hζ (Sum.inl w) ⊤ ≤ localCenter F ζ hζ (Sum.inl w) := by
    intro x hx
    exact Subsingleton.elim _ _
  let i := Subgroup.inclusion hAC
  let lambda : localPreimage F ζ hζ (Sum.inl w) ⊤ →ₜ* ℂˣ :=
    ⟨(localOmega F ζ hζ (Sum.inl w)).toMonoidHom.comp i,
      (localOmega F ζ hζ (Sum.inl w)).continuous.comp
        (continuous_subtype_val.subtype_mk _)⟩
  have hext : ∀ (b : localPreimage F ζ hζ (Sum.inl w) ⊤)
      (z : localCenter F ζ hζ (Sum.inl w)),
      b.val = z.val → lambda b = localOmega F ζ hζ (Sum.inl w) z := by
    intro b z hz
    exact congrArg (localOmega F ζ hζ (Sum.inl w)) (Subtype.ext hz)
  exact ⟨{ L := ⊤
           maximal := complex_full_maximal_isotropic F ζ hζ w
           lambda := lambda
           extends_center := hext
           modulus := modulus_of_extends_center F ζ hζ (Sum.inl w) ⊤ lambda hext
             (local_center_modulus F ζ hζ (Sum.inl w)) }, rfl⟩

 theorem finite_torus_eq (q : HeightOneSpectrum (𝓞 F)) :
    localTorus F ζ hζ (Sum.inr q) = ActualFiniteTorus.H F ζ hζ q := by
  letI : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
    KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
  apply le_antisymm
  · intro g hg
    obtain ⟨y, hy⟩ := hg
    change KPLocalSmoothRepresentation.projection F ζ hζ q g ∈ KPRankOneInduction.diagonalTorus F q
    refine ⟨diagonalHom F (Sum.inr q) y, ?_, ?_, ?_⟩
    · exact congrArg (KPLocalSmoothRepresentation.ordinaryPGLMap F q) hy
    · simp [diagonalHom, KubotaRankTwo.d]
    · simp [diagonalHom, KubotaRankTwo.d]
  · intro g hg
    let h : ActualFiniteTorus.H F ζ hζ q := ⟨g, hg⟩
    have hn := (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.1 h
    change KPPGLLocalCover.projection F ζ hζ (Sum.inr q) g ∈ localOrdinaryTorus F (Sum.inr q)
    rw [show g = ActualFiniteTorus.normalWord F ζ hζ q _ _ from hn]
    refine ⟨ActualFiniteTorus.coordinate F ζ hζ q h, ?_⟩
    simp only [ActualFiniteTorus.normalWord, map_mul]
    have hp : KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
        (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (ActualFiniteTorus.sheet F ζ hζ q h)) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection]
      exact ⟨_, rfl⟩
    rw [hp, one_mul]
    rfl

 def finite_torus_equiv (q : HeightOneSpectrum (𝓞 F)) :
    LocalE F ζ hζ (Sum.inr q) ≃* ActualFiniteTorus.H F ζ hζ q :=
  MulEquiv.subgroupCongr (finite_torus_eq F ζ hζ q)

private theorem finite_ratio_eq (q : HeightOneSpectrum (𝓞 F))
    (g : LocalE F ζ hζ (Sum.inr q)) :
    ActualFiniteTorus.coordinate F ζ hζ q (finite_torus_equiv F ζ hζ q g) =
      localRatio F ζ hζ (Sum.inr q) g := by
  apply Units.ext
  change (KPRankOneInduction.borelRatio F q _ : ActualFiniteTorus.K F q) = _
  rw [KPRankOneInduction.borelRatio_eq _ _ _
    (diagonalHom F (Sum.inr q) (localRatio F ζ hζ (Sum.inr q) g))]
  · simp [diagonalHom, KubotaRankTwo.d]
  · exact congrArg (KPLocalSmoothRepresentation.ordinaryPGLMap F q)
      (localRatioValue_spec F ζ hζ (Sum.inr q) g)
  · simp [diagonalHom, KubotaRankTwo.d]

theorem finite_local_center_open (q : HeightOneSpectrum (𝓞 F)) :
    IsOpen (localCenter F ζ hζ (Sum.inr q) : Set (LocalE F ζ hζ (Sum.inr q))) := by
  have hc : Continuous (localRatio F ζ hζ (Sum.inr q)) := by
    have he : Continuous (finite_torus_equiv F ζ hζ q) :=
      continuous_subtype_val.subtype_mk _
    have h := (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.2.1.comp he
    exact h.congr (finite_ratio_eq F ζ hζ q)
  obtain ⟨E, hE⟩ := LocalClassFieldTheory.exists_finiteGalois_normSubgroup_le_powMonoidHom_range
    (q.adicCompletion F) 3 (by norm_num)
  letI : FiniteDimensional (q.adicCompletion F)
      (E : IntermediateField (q.adicCompletion F) (SeparableClosure (q.adicCompletion F))) := E.finiteDimensional
  letI : IsGalois (q.adicCompletion F)
      (E : IntermediateField (q.adicCompletion F) (SeparableClosure (q.adicCompletion F))) := E.isGalois
  have hopen : IsOpen (CubicCharacters.cubes (q.adicCompletion F)ˣ : Set (q.adicCompletion F)ˣ) :=
    Subgroup.isOpen_mono hE (LocalClassFieldTheory.localNormSubgroup_isOpen (q.adicCompletion F)
      (E : IntermediateField (q.adicCompletion F) (SeparableClosure (q.adicCompletion F))))
  have heq : (localCenter F ζ hζ (Sum.inr q) : Set (LocalE F ζ hζ (Sum.inr q))) =
      (localRatio F ζ hζ (Sum.inr q)) ⁻¹' (CubicCharacters.cubes (q.adicCompletion F)ˣ : Set _) := by
    ext x
    exact QuotientGroup.eq_one_iff _
  rw [heq]
  exact hopen.preimage hc

theorem local_preimage_abelian (v : KPHilbert.Place F) (L : Subgroup (LocalD F v))
    (hL : IsMaximalIsotropic F (KPGlobalCubicIdelePairing.localPairing F ζ hζ v) L) :
    ∀ x ∈ localPreimage F ζ hζ v L, ∀ y ∈ localPreimage F ζ hζ v L, Commute x y := by
  intro x hx y hy
  obtain ⟨e, he⟩ := normal_word_exists F ζ hζ v x
  obtain ⟨f, hf⟩ := normal_word_exists F ζ hζ v y
  have hxy : KPHilbert.B3 F ζ hζ v (localRatio F ζ hζ v x) (localRatio F ζ hζ v y) = 1 :=
    hL.1 (localProjection F ζ hζ v x) hx (localProjection F ζ hζ v y) hy
  have hyx : KPHilbert.B3 F ζ hζ v (localRatio F ζ hζ v y) (localRatio F ζ hζ v x) = 1 :=
    hL.1 (localProjection F ζ hζ v y) hy (localProjection F ζ hζ v x) hx
  have zcomm (z : rootsOfUnity 3 F) (a : KPPGLLocalCover.CubicPGL2 F ζ hζ v) :
      Commute (KPPGLLocalCover.centralInjection F ζ hζ v z) a :=
    (Subgroup.mem_center_iff.mp
      (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ v ⟨z, rfl⟩) a).symm
  have ac : Commute (KPPGLLocalCover.A F ζ hζ v (localRatio F ζ hζ v x))
      (KPPGLLocalCover.A F ζ hζ v (localRatio F ζ hζ v y)) := by
    change KPPGLLocalCover.A F ζ hζ v _ * KPPGLLocalCover.A F ζ hζ v _ = _
    simp [KPPGLLocalCover.A_mul, hxy, hyx, mul_comm]
  apply show Commute x.val y.val → Commute x y from fun h => Subtype.ext h.eq
  rw [he, hf]
  exact ((zcomm e _).mul_right (zcomm e _)).mul_left
    (((zcomm f _).symm).mul_right ac)

theorem finite_local_polarization (q : HeightOneSpectrum (𝓞 F)) :
    Nonempty (LocalPolarization F ζ hζ (Sum.inr q)) := by
  letI : IsTopologicalGroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) :=
    (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2.1
  letI : IsTopologicalGroup (LocalE F ζ hζ (Sum.inr q)) := by
    change IsTopologicalGroup (localTorus F ζ hζ (Sum.inr q))
    infer_instance
  obtain ⟨L, hL⟩ := local_maximal_isotropic_exists F ζ hζ (Sum.inr q)
  obtain ⟨P, hP⟩ := @local_polarization_of_open_abelian_preimage F _ _ ζ hζ (Sum.inr q) ‹IsTopologicalGroup (LocalE F ζ hζ (Sum.inr q))› L hL
    (finite_local_center_open F ζ hζ q) (local_preimage_abelian F ζ hζ (Sum.inr q) L hL)
    (local_center_modulus F ζ hζ (Sum.inr q))
  exact ⟨P⟩

theorem good_local_extension (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q) :
    ∃ P : LocalPolarization F ζ hζ (Sum.inr q), IsUnramified F ζ hζ q P := by
  letI : IsTopologicalGroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) :=
    (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2.1
  letI : IsTopologicalGroup (LocalE F ζ hζ (Sum.inr q)) := by
    change IsTopologicalGroup (localTorus F ζ hζ (Sum.inr q))
    infer_instance
  let L := KPGlobalCubicIdelePairing.U F (Sum.inr q)
  let A := localPreimage F ζ hζ (Sum.inr q) L
  let S : Subgroup (LocalE F ζ hζ (Sum.inr q)) :=
    A ⊓ (KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q)).comap
      (localTorus F ζ hζ (Sum.inr q)).subtype
  have hCA : localCenter F ζ hζ (Sum.inr q) ≤ A := by
    intro x hx
    change localProjection F ζ hζ (Sum.inr q) x ∈ L
    change localProjection F ζ hζ (Sum.inr q) x = 1 at hx
    rw [hx]
    exact L.one_mem
  have hL := tame_unit_maximal_isotropic F ζ hζ q hgood
  obtain ⟨lambda, hext, htrivial⟩ :=
    UnramifiedExtension.open_character_extension_trivial_on_subgroup
      (localCenter F ζ hζ (Sum.inr q)) A S hCA inf_le_left
      (finite_local_center_open F ζ hζ q)
      (local_preimage_abelian F ζ hζ (Sum.inr q) L hL)
      (localOmega F ζ hζ (Sum.inr q))
      (fun z hz => UnramifiedExtension.center_character_trivial_on_good_compact
        F ζ hζ q hgood z hz.2)
  let P : LocalPolarization F ζ hζ (Sum.inr q) :=
    { L := L
      maximal := hL
      lambda := lambda
      extends_center := hext
      modulus := modulus_of_extends_center F ζ hζ (Sum.inr q) L lambda hext
        (local_center_modulus F ζ hζ (Sum.inr q)) }
  refine ⟨P, hgood, rfl, ?_⟩
  intro b hb
  exact htrivial b ⟨b.property, hb⟩

end
end DedekindZetaZeroFree.ProductPolarization

end

section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ProductPolarization
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology localCoverTopology

theorem compatible_local_choices_of_local_extensions
    (hcomplex : ∀ w : InfinitePlace F,
      ∃ P : LocalPolarization F ζ hζ (Sum.inl w), P.L = ⊤)
    (hbad : ∀ q : HeightOneSpectrum (𝓞 F), KPAdelicCoverRestrictedProduct.Bad F q →
      Nonempty (LocalPolarization F ζ hζ (Sum.inr q)))
    (hgood : ∀ q : HeightOneSpectrum (𝓞 F), ¬ KPAdelicCoverRestrictedProduct.Bad F q →
      ∃ P : LocalPolarization F ζ hζ (Sum.inr q), IsUnramified F ζ hζ q P) :
    Nonempty (CompatibleLocalData F ζ hζ) := by
  classical
  let complexData (w : InfinitePlace F) := (hcomplex w).choose
  let finiteData (q : HeightOneSpectrum (𝓞 F)) :
      LocalPolarization F ζ hζ (Sum.inr q) :=
    if h : KPAdelicCoverRestrictedProduct.Bad F q then (hbad q h).some
    else (hgood q h).choose
  refine ⟨{ localData := fun v => match v with
              | Sum.inl w => complexData w
              | Sum.inr q => finiteData q
            complex_full := ?_
            unramified_almost_everywhere := ?_ }⟩
  · intro w
    exact (hcomplex w).choose_spec
  · have hcof : ∀ᶠ q in Filter.cofinite, ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
      exact (KPAdelicCoverRestrictedProduct.bad_finite F).compl_mem_cofinite
    filter_upwards [hcof] with q hq
    simpa only [Sum.elim_inr, finiteData, dif_neg hq] using (hgood q hq).choose_spec

theorem compatible_local_choices : Nonempty (CompatibleLocalData F ζ hζ) :=
  compatible_local_choices_of_local_extensions F ζ hζ
    (complex_local_polarization F ζ hζ)
    (fun q _ => finite_local_polarization F ζ hζ q)
    (good_local_extension F ζ hζ)

end
end DedekindZetaZeroFree.ProductPolarization

end
