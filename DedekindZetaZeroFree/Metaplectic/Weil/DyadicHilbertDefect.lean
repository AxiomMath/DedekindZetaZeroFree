module

public import DedekindZetaZeroFree.Adeles.Approximation.FiniteAndDyadicSquareClasses
public import DedekindZetaZeroFree.Metaplectic.Weil.GlobalPhaseProductAndThetaSymmetries

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]

private lemma odd_char (v : HeightOneSpectrum (𝓞 F)) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    ringChar (OddLocalResidue v) ≠ 2 := by
  classical
  intro hc
  have hu : IsUnit (2 : v.adicCompletionIntegers F) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have hv := (v.valuation_eq_one_iff_notMem (K := F)).mpr h
    change Valued.v (2 : v.adicCompletion F) = 1
    have he' : Valued.v (algebraMap F (v.adicCompletion F) (2 : F)) = _ :=
      v.valuedAdicCompletion_eq_valuation' (K := F) (2 : F)
    simpa only [map_ofNat] using he'.trans (by simpa only [map_ofNat] using hv)
  have hn := (hu.map (IsLocalRing.residue (v.adicCompletionIntegers F)))
  have hz : (2 : OddLocalResidue v) = 0 := (ringChar.spec _ 2).mpr (by rw [hc])
  rw [map_ofNat, hz] at hn
  exact not_isUnit_zero hn
private lemma symbol_embed (A : SArithmeticData F) (σ : F →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (a b : (v.adicCompletion F)ˣ) :
    A.finiteQuadraticHilbertCoefficient v a b =
      σ (((A.actualLocalSymbol v 2 (Or.inl rfl) a b : rootsOfUnity 2 F) : Fˣ) : F) := by
  let z := A.actualLocalSymbol v 2 (Or.inl rfl) a b
  have hz : (z.val.val : F) ^ 2 = 1 := by
    have h := (mem_rootsOfUnity 2 z.val).mp z.property
    exact congrArg Units.val h
  obtain h | h := sq_eq_one_iff.mp hz
  · have h1 : z = 1 := Subtype.ext (Units.ext h)
    change (if z = 1 then 1 else -1) = σ z.val.val
    rw [if_pos h1]
    simp only [h, map_one]
  · have h1 : z ≠ 1 := by
      intro h1
      have : (1 : F) = -1 := by simpa [h1] using h
      have : (2 : F) = 0 := by linear_combination this
      exact (two_ne_zero : (2 : F) ≠ 0) this
    change (if z = 1 then 1 else -1) = σ z.val.val
    rw [if_neg h1, h, map_neg, map_one]
private lemma sum_prod {I J : Type*} (f : I ⊕ J → ℂ) (h : ∀ i : I, f (Sum.inl i) = 1) :
    (∏ᶠ p : I ⊕ J, f p) = ∏ᶠ j : J, f (Sum.inr j) := by
  classical
  rw [← finprod_mem_range (f := f) (g := Sum.inr) Sum.inr_injective, finprod_mem_def]
  apply finprod_congr
  intro p
  rcases p with i | j
  · simp [Set.mulIndicator, h i]
  · simp [Set.mulIndicator]
private lemma phase_product (A : SArithmeticData F) (x : Fˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      A.finiteWeilPhase v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x)) = 1 ∧
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) =>
      A.finiteWeilPhase v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x)) := by
  have hp := A.globalQuadraticWeilPhase_product x
  have hs : ∀ w : InfinitePlace F, A.globalQuadraticWeilPhase x (Sum.inl w) = 1 := by
    intro w
    simp [globalQuadraticWeilPhase, globalQuadraticGamma, complexGamma]
  have hprod := sum_prod (A.globalQuadraticWeilPhase x) hs
  have heq (v : HeightOneSpectrum (𝓞 F)) :
      A.globalQuadraticWeilPhase x (Sum.inr v) =
        A.finiteWeilPhase v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x) := by
    rfl
  constructor
  · have hp2 := hprod.symm.trans hp.2
    simpa only [heq] using hp2
  · convert hp.1.comp_of_injective Sum.inr_injective using 1
    funext v
    exact (heq v).symm
 def rootMap (σ : F →+* ℂ) : rootsOfUnity 2 F →* ℂ :=
  σ.toMonoidHom.comp ((Units.coeHom F).comp (rootsOfUnity 2 F).subtype)
private lemma symbol_product (A : SArithmeticData F) (σ : F →+* ℂ) (x y : Fˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      σ (((A.actualLocalSymbol v 2 (Or.inl rfl)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom y) : rootsOfUnity 2 F) : Fˣ) : F)) = 1 ∧
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) =>
      σ (((A.actualLocalSymbol v 2 (Or.inl rfl)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom y) : rootsOfUnity 2 F) : Fˣ) : F)) := by
  classical
  let raw := fun v : HeightOneSpectrum (𝓞 F) =>
    ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor F
      (A.actualRawHilbert 2 (Or.inl rfl)) (A.actualHilbert_roots 2 (Or.inl rfl)) v x y
  have hp := ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_productFormula
    F 2 (A.actualHilbert_roots 2 (Or.inl rfl))
  have hs : Function.HasFiniteMulSupport raw := hp.2.1 x y
  have hi : ∀ w : InfinitePlace F,
      ClassFieldTheory.globalInfinitePlaceHilbertSymbol F 2 w x y = 1 := by
    intro w
    simp [ClassFieldTheory.globalInfinitePlaceHilbertSymbol,
      InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place w)]
  have hr : (∏ᶠ v, raw v) = 1 := by
    simpa only [hi, Finset.prod_const_one, one_mul, raw, actualRawHilbert] using hp.2.2 x y
  have hs' := hs.fun_inv
  have hmap := (rootMap σ).map_finprod hs'
  have heq (v : HeightOneSpectrum (𝓞 F)) : (rootMap σ) ((raw v)⁻¹) =
      σ (((A.actualLocalSymbol v 2 (Or.inl rfl)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom y) : rootsOfUnity 2 F) : Fˣ) : F) := by
    rw [A.actualLocalSymbol_diagonal]
    rfl
  constructor
  · rw [finprod_inv_distrib, hr, inv_one, map_one] at hmap
    simpa only [heq] using hmap.symm
  · have hfin := hs'.fun_comp (rootMap σ).map_one
    simpa only [heq] using hfin
private lemma square_ratio {G : Type*} [CommGroup G] {a b : G} (h : IsSquare (a / b)) :
    ∃ t : G, a = b * t ^ 2 := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  have : a / b = t ^ 2 := by simpa only [pow_two] using ht
  calc
    a = b * (a / b) := by simp [div_eq_mul_inv, mul_comm, mul_left_comm]
    _ = b * t ^ 2 := by rw [this]
private lemma phase_class (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    {a b : (v.adicCompletion F)ˣ} (h : IsSquare (a / b)) :
    A.finiteWeilPhase v a = A.finiteWeilPhase v b := by
  obtain ⟨t, rfl⟩ := square_ratio h
  exact A.finiteWeilPhase_mul_sq v b t
private lemma square_class_one (v : HeightOneSpectrum (𝓞 F))
    {a : (v.adicCompletion F)ˣ} (h : IsSquare a) :
    QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) ((2 : ℕ+) : ℕ)).range a = 1 := by
  apply (QuotientGroup.eq_one_iff a).mpr
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by change t ^ 2 = a; simpa only [pow_two] using ht.symm⟩
private lemma symbol_sq (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    {a : (v.adicCompletion F)ˣ} (h : IsSquare a) (b : (v.adicCompletion F)ˣ) :
    A.actualLocalSymbol v 2 (Or.inl rfl) a b = 1 := by
  unfold actualLocalSymbol
  rw [square_class_one v h, map_one, MonoidHom.one_apply]
private lemma symbol_class (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    {a b c d : (v.adicCompletion F)ˣ} (ha : IsSquare (a / c)) (hb : IsSquare (b / d)) :
    A.actualLocalSymbol v 2 (Or.inl rfl) a b = A.actualLocalSymbol v 2 (Or.inl rfl) c d := by
  have hq {x y : (v.adicCompletion F)ˣ} (h : IsSquare (x / y)) :
      QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) ((2 : ℕ+) : ℕ)).range x =
        QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) ((2 : ℕ+) : ℕ)).range y := by
    have hs := square_class_one v h
    rw [map_div] at hs
    exact div_eq_one.mp hs
  unfold actualLocalSymbol
  rw [hq ha, hq hb]
private lemma lift_product {I : Type*} (f : I → ℂ) (hf : ∀ i, f i ≠ 0)
    (hp : (∏ᶠ i, f i) = 1 ∧ Function.HasFiniteMulSupport f) :
    (∏ᶠ i, Units.mk0 (f i) (hf i)) = 1 ∧
    Function.HasFiniteMulSupport (fun i => Units.mk0 (f i) (hf i)) := by
  have hs : Function.HasFiniteMulSupport (fun i => Units.mk0 (f i) (hf i)) := by
    convert hp.2 using 1
    simp only [Function.HasFiniteMulSupport, Function.mulSupport, ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one]
  constructor
  · apply Units.ext
    have hm := (Units.coeHom ℂ).map_finprod hs
    exact hm.trans hp.1
  · exact hs
private lemma phase_nonzero (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) : A.finiteWeilPhase v a ≠ 0 := by
  intro h
  have hh := A.finiteWeilPhase_norm v a
  rw [h, norm_zero] at hh
  exact zero_ne_one hh
private lemma symbol_nonzero (A : SArithmeticData F) (σ : F →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (a b : (v.adicCompletion F)ˣ) :
    σ (((A.actualLocalSymbol v 2 (Or.inl rfl) a b : rootsOfUnity 2 F) : Fˣ) : F) ≠ 0 :=
  (map_ne_zero σ).mpr (A.actualLocalSymbol v 2 (Or.inl rfl) a b).val.ne_zero
private lemma isolated_law (A : SArithmeticData F) (σ : F →+* ℂ)
    (v₀ : HeightOneSpectrum (𝓞 F)) (x y : Fˣ)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → v ≠ v₀ →
      IsSquare (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x))
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → v ≠ v₀ →
      IsSquare (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom y)) :
    let xm := Units.map (algebraMap F (v₀.adicCompletion F)).toMonoidHom x
    let ym := Units.map (algebraMap F (v₀.adicCompletion F)).toMonoidHom y
    A.finiteWeilPhase v₀ xm * A.finiteWeilPhase v₀ ym =
      σ (((A.actualLocalSymbol v₀ 2 (Or.inl rfl) xm ym : rootsOfUnity 2 F) : Fˣ) : F) *
        A.finiteWeilPhase v₀ (xm * ym) := by
  classical
  let m := fun v : HeightOneSpectrum (𝓞 F) =>
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom
  let P := fun (z : Fˣ) (v : HeightOneSpectrum (𝓞 F)) =>
    Units.mk0 (A.finiteWeilPhase v (m v z)) (phase_nonzero A v _)
  let S := fun v : HeightOneSpectrum (𝓞 F) =>
    Units.mk0 (σ (((A.actualLocalSymbol v 2 (Or.inl rfl) (m v x) (m v y) :
      rootsOfUnity 2 F) : Fˣ) : F)) (symbol_nonzero A σ v _ _)
  have hp (z : Fˣ) : (∏ᶠ v, P z v) = 1 ∧ Function.HasFiniteMulSupport (P z) :=
    lift_product _ _ (phase_product A z)
  have hs : (∏ᶠ v, S v) = 1 ∧ Function.HasFiniteMulSupport S :=
    lift_product _ _ (symbol_product A σ x y)
  let D := fun v => (P x v * P y v) / (S v * P (x*y) v)
  have hd : (∏ᶠ v, D v) = 1 := by
    dsimp [D]
    change (∏ᶠ v, (P x * P y) v / (S * P (x*y)) v) = 1
    rw [finprod_div_distrib ((hp x).2.mul (hp y).2) (hs.2.mul (hp (x*y)).2)]
    simp only [Pi.mul_apply]
    rw [finprod_mul_distrib (hp x).2 (hp y).2,
      finprod_mul_distrib hs.2 (hp (x*y)).2, (hp x).1, (hp y).1, hs.1, (hp (x*y)).1]
    simp
  have off : ∀ v, v ≠ v₀ → D v = 1 := by
    intro v hv
    apply div_eq_one.mpr
    apply Units.ext
    change A.finiteWeilPhase v (m v x) * A.finiteWeilPhase v (m v y) =
      σ (((A.actualLocalSymbol v 2 (Or.inl rfl) (m v x) (m v y) : rootsOfUnity 2 F) : Fˣ) : F) *
        A.finiteWeilPhase v (m v (x*y))
    rw [map_mul]
    by_cases hv2 : (2 : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨r, hr⟩ := hx v hv2 hv
      obtain ⟨t, ht⟩ := hy v hv2 hv
      have hphase {a : (v.adicCompletion F)ˣ} (h : IsSquare a) : A.finiteWeilPhase v a = 1 := by
        obtain ⟨s, hs⟩ := h
        rw [hs, ← pow_two, A.finiteWeilPhase_sq]
      rw [hphase (hx v hv2 hv), hphase (hy v hv2 hv),
        hphase ((hx v hv2 hv).mul (hy v hv2 hv)), symbol_sq A v (hx v hv2 hv)]
      simp
    · rw [← symbol_embed A σ]
      exact A.finiteWeilPhase_odd_hilbert_defect v (odd_char v hv2) _ _
  have hone : D v₀ = 1 := (finprod_eq_single D v₀ off).symm.trans hd
  have he := div_eq_one.mp hone
  have he' := congrArg Units.val he
  simpa only [P, S, m, Units.val_mul, Units.val_mk0, map_mul] using he'

theorem finiteWeilPhase_mul_dyadic (A : SArithmeticData F) (σ : F →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (2 : 𝓞 F) ∈ v.asIdeal)
    (a b : (v.adicCompletion F)ˣ) :
    A.finiteWeilPhase v a * A.finiteWeilPhase v b =
      σ (((A.actualLocalSymbol v 2 (Or.inl rfl) a b : rootsOfUnity 2 F) : Fˣ) : F) *
        A.finiteWeilPhase v (a * b) := by
  obtain ⟨x, hx, hxoff⟩ := weil_dyadic_squareclass_approximation F v hv a
  obtain ⟨y, hy, hyoff⟩ := weil_dyadic_squareclass_approximation F v hv b
  have h := isolated_law A σ v x y hxoff hyoff
  dsimp only at h
  have hab : IsSquare
      ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x *
        Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom y) / (a*b)) := by
    simpa only [mul_div_mul_comm] using hx.mul hy
  rw [phase_class A v hx, phase_class A v hy, phase_class A v hab,
    symbol_class A v hx hy] at h
  exact h

end DedekindZetaZeroFree.SArithmeticData

end
