module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.ExteriorCRTIdelicCongruence

@[expose] public section

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

open scoped NumberField Classical
open NumberField IsDedekindDomain

theorem integral_residue_congr_iff
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (qO : Ideal (𝓞 F)) (hq : qO ≠ ⊥) (hcop : qO ⊔ A.cS = ⊤)
    (a b : 𝓞 F) :
    Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
        (algebraMap (𝓞 F) A.R a) =
      Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
        (algebraMap (𝓞 F) A.R b) ↔ a - b ∈ qO := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
  change a - b ∈ (FixedSResidue.residueModulus A qO).under (𝓞 F) ↔ _
  rw [FixedSResidue.residueModulus,
    SIntegerLocalization.under_map_exterior A.Sf qO hcop]

end DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

end

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
set_option maxHeartbeats 800000

variable {F : Type} [Field F] [NumberField F]

private lemma unit_iff_span_sup {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    IsUnit (Ideal.Quotient.mk I x) ↔ Ideal.span {x} ⊔ I = ⊤ := by
  rw [isUnit_iff_exists_inv, Ideal.eq_top_iff_one]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hm : x * z - 1 ∈ I := Ideal.Quotient.eq.mp (by simpa using hy)
    have hx : x * z ∈ Ideal.span {x} ⊔ I :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr ⟨z, rfl⟩)
    have hd : x * z - 1 ∈ Ideal.span {x} ⊔ I := Ideal.mem_sup_right hm
    simpa using (Ideal.span {x} ⊔ I).sub_mem hx hd
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp ha
    refine ⟨Ideal.Quotient.mk I z, ?_⟩
    have hh := congrArg (Ideal.Quotient.mk I) hab
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hb] using hh

private lemma exists_ne_zero_sub_mem {R : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal R) (hI : I ≠ ⊥) (a : R) : ∃ b : R, b ≠ 0 ∧ b - a ∈ I := by
  by_cases ha : a = 0
  · obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨x, hx0, by rw [ha, sub_zero]; exact hxI⟩
  · exact ⟨a, ha, by simp⟩

private lemma coprime_of_support (A : SArithmeticData F) (fS qO : Ideal (𝓞 F))
    (hfS : fS ≠ ⊥)
    (hsupp : ∀ v : HeightOneSpectrum (𝓞 F), fS ≤ v.asIdeal → v ∈ A.Sf)
    (hcop : qO ⊔ A.cS = ⊤) : IsCoprime qO fS := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal (qO ⊔ fS) h
  have hfM : fS ≤ M := le_trans le_sup_right hle
  have hMb : M ≠ ⊥ := by
    intro h0
    exact hfS (le_bot_iff.mp (h0 ▸ hfM))
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hMmax.isPrime, hMb⟩
  have hvSf : v ∈ A.Sf := hsupp v (by simpa [v] using hfM)
  have hcSM : A.cS ≤ M := by
    have hdvd : M ∣ A.cS := by
      simpa [SArithmeticData.cS, v] using
        Finset.dvd_prod_of_mem (fun v' : HeightOneSpectrum (𝓞 F) => v'.asIdeal) hvSf
    exact Ideal.dvd_iff_le.mp hdvd
  have hle' : qO ⊔ A.cS ≤ M := sup_le (le_trans le_sup_left hle) hcSM
  rw [hcop] at hle'
  exact hMmax.ne_top (top_le_iff.mp hle')

theorem exists_exterior_crt_representative
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (f fS qO : Ideal (𝓞 F))
    (hsplit : FixedSResidue.ConductorSplit A f fS qO) (a : 𝓞 F) :
    ∃ b : 𝓞 F, b ≠ 0 ∧ b - a ∈ qO ∧ b - 1 ∈ fS ∧
      Ideal.span {b} ⊔ A.cS = ⊤ := by
  obtain ⟨hf, hfS, hqO, hfac, hsupp, hcS⟩ := hsplit
  by_cases hm : fS * A.cS = ⊤
  ·
    have hfStop : fS = ⊤ := top_le_iff.mp (hm ▸ Ideal.mul_le_left)
    have hcStop : A.cS = ⊤ := top_le_iff.mp (hm ▸ Ideal.mul_le_right)
    obtain ⟨b, hb0, hba⟩ := exists_ne_zero_sub_mem qO hqO a
    exact ⟨b, hb0, hba, by rw [hfStop]; exact Submodule.mem_top, by rw [hcStop, sup_top_eq]⟩
  ·
    have hcop_fS : IsCoprime qO fS := coprime_of_support A fS qO hfS hsupp hcS
    have hcop_cS : IsCoprime qO A.cS := Ideal.isCoprime_iff_sup_eq.mpr hcS
    have hcop : IsCoprime qO (fS * A.cS) := hcop_fS.mul_right hcop_cS

    let I : Fin 2 → Ideal (𝓞 F) := ![qO, fS * A.cS]
    have hpair : Pairwise (fun i j => IsCoprime (I i) (I j)) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | exact absurd rfl hij
          | exact hcop
          | exact hcop.symm
    obtain ⟨b, hb⟩ := Ideal.exists_forall_sub_mem_ideal (I := I) hpair (x := ![a, 1])
    have hba : b - a ∈ qO := by simpa [I] using hb 0
    have hbm : b - 1 ∈ fS * A.cS := by simpa [I] using hb 1
    have hbS : b - 1 ∈ fS := Ideal.mul_le_left hbm
    have hbcS : b - 1 ∈ A.cS := Ideal.mul_le_right hbm

    have hb0 : b ≠ 0 := by
      intro hb0
      have h1 : (1 : 𝓞 F) ∈ fS * A.cS := by
        have : -(1 : 𝓞 F) ∈ fS * A.cS := by simpa [hb0] using hbm
        simpa using neg_mem this
      exact hm ((fS * A.cS).eq_top_iff_one.mpr h1)
    have hspan : Ideal.span {b} ⊔ A.cS = ⊤ := by
      rw [← unit_iff_span_sup A.cS b]
      have h1 : Ideal.Quotient.mk A.cS b = Ideal.Quotient.mk A.cS 1 :=
        Ideal.Quotient.eq.mpr (by simpa using hbcS)
      rw [h1, map_one]
      exact isUnit_one
    exact ⟨b, hb0, hba, hbS, hspan⟩

end

end DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

end

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
set_option maxHeartbeats 800000
variable {F : Type} [Field F] [NumberField F]

def inverseLocalCharacter (A : SArithmeticData F) (sigma : FixedSResidue.FullLocalCharacters A) :
    Fˣ →* ℂˣ where
  toFun x := (∏ w : InfinitePlace F, (sigma.1 w ((A.diagonal x).1 w))⁻¹) *
    ∏ v : {v // v ∈ A.Sf}, (sigma.2 v ((A.diagonal x).2 v))⁻¹
  map_one' := by simp
  map_mul' := by
    intro x y
    simp only [map_mul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_inv_rev,
      Finset.prod_mul_distrib]
    ac_rfl

theorem localInverseProduct_eq (A : SArithmeticData F)
    (sigma : FixedSResidue.FullLocalCharacters A) (n : FixedSResidue.NonzeroSInteger A) :
    FixedSResidue.localInverseProduct A sigma n =
      (inverseLocalCharacter A sigma (FixedSResidue.fieldUnit A n) : ℂ) := by
  simp [FixedSResidue.localInverseProduct, inverseLocalCharacter]

theorem localInverseProduct_ne_zero (A : SArithmeticData F)
    (sigma : FixedSResidue.FullLocalCharacters A) (n : FixedSResidue.NonzeroSInteger A) :
    FixedSResidue.localInverseProduct A sigma n ≠ 0 := by
  rw [localInverseProduct_eq]
  exact Units.ne_zero _

theorem localInverseProduct_mul (A : SArithmeticData F)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (n m : FixedSResidue.NonzeroSInteger A) :
    FixedSResidue.localInverseProduct A sigma ⟨n.val * m.val, mul_ne_zero n.property m.property⟩ =
      FixedSResidue.localInverseProduct A sigma n * FixedSResidue.localInverseProduct A sigma m := by
  have hfield : FixedSResidue.fieldUnit A ⟨n.val * m.val, mul_ne_zero n.property m.property⟩ =
      FixedSResidue.fieldUnit A n * FixedSResidue.fieldUnit A m := by
    apply Units.ext
    rfl
  simp only [localInverseProduct_eq, hfield, map_mul, Units.val_mul]

def numeratorExterior (A : SArithmeticData F) (n : FixedSResidue.NonzeroSInteger A) :
    A.Exterior := A.exteriorIdealEquiv.symm
      ⟨Ideal.span {n.val}, Ideal.span_singleton_eq_bot.not.mpr n.property⟩

theorem numeratorExterior_generates (A : SArithmeticData F)
    (n : FixedSResidue.NonzeroSInteger A) :
    A.extendIdeal (numeratorExterior A n) = Ideal.span {n.val} := by
  exact congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply _)

theorem numeratorExterior_unique (A : SArithmeticData F)
    (n : FixedSResidue.NonzeroSInteger A) (a : A.Exterior)
    (ha : Ideal.span {n.val} = A.extendIdeal a) : numeratorExterior A n = a := by
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  exact (numeratorExterior_generates A n).trans ha

theorem numeratorExterior_mul (A : SArithmeticData F)
    (n m : FixedSResidue.NonzeroSInteger A) :
    (numeratorExterior A ⟨n.val * m.val, mul_ne_zero n.property m.property⟩).val =
      (numeratorExterior A n).val * (numeratorExterior A m).val := by
  have hcopn : IsCoprime (numeratorExterior A n).val A.cS :=
    Ideal.isCoprime_iff_sup_eq.mpr (numeratorExterior A n).property.2
  have hcopm : IsCoprime (numeratorExterior A m).val A.cS :=
    Ideal.isCoprime_iff_sup_eq.mpr (numeratorExterior A m).property.2
  have hcop : (numeratorExterior A n).val * (numeratorExterior A m).val ⊔ A.cS = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp (hcopn.mul_left hcopm)
  have hne : (numeratorExterior A n).val * (numeratorExterior A m).val ≠ ⊥ :=
    mul_ne_zero (numeratorExterior A n).property.1 (numeratorExterior A m).property.1
  let a : A.Exterior := ⟨(numeratorExterior A n).val * (numeratorExterior A m).val, hne, hcop⟩
  have ha : Ideal.span {n.val * m.val} = A.extendIdeal a := by
    change _ = Ideal.map _ (_ * _)
    rw [Ideal.map_mul]
    change _ = A.extendIdeal (numeratorExterior A n) * A.extendIdeal (numeratorExterior A m)
    rw [numeratorExterior_generates A n, numeratorExterior_generates A m]
    exact (Ideal.span_singleton_mul_span_singleton n.val m.val).symm
  have hh := numeratorExterior_unique A
    (⟨n.val * m.val, mul_ne_zero n.property m.property⟩ : FixedSResidue.NonzeroSInteger A) a ha
  exact congrArg (fun b : A.Exterior => b.val) hh

def exteriorCoefficient (A : SArithmeticData F) (f : Ideal (𝓞 F))
    (omega : RayClassCharacter F f) (sigma : FixedSResidue.FullLocalCharacters A)
    (n : FixedSResidue.NonzeroSInteger A) : ℂ :=
  omega (numeratorExterior A n).val / FixedSResidue.localInverseProduct A sigma n

theorem exteriorCoefficient_mul (A : SArithmeticData F) (f : Ideal (𝓞 F))
    (omega : RayClassCharacter F f) (sigma : FixedSResidue.FullLocalCharacters A)
    (n m : FixedSResidue.NonzeroSInteger A) :
    exteriorCoefficient A f omega sigma ⟨n.val*m.val, mul_ne_zero n.property m.property⟩ =
      exteriorCoefficient A f omega sigma n * exteriorCoefficient A f omega sigma m := by
  simp only [exteriorCoefficient, numeratorExterior_mul, omega.map_mul', localInverseProduct_mul]
  exact div_mul_div_comm _ _ _ _ |>.symm

theorem exteriorCoefficient_one (A : SArithmeticData F) (f : Ideal (𝓞 F))
    (omega : RayClassCharacter F f) (sigma : FixedSResidue.FullLocalCharacters A) :
    exteriorCoefficient A f omega sigma ⟨1, one_ne_zero⟩ = 1 := by
  have hn : (numeratorExterior A ⟨1, one_ne_zero⟩).val = ⊤ := by
    let a : A.Exterior := ⟨⊤, top_ne_bot, by simp⟩
    have ha : Ideal.span {(1 : A.R)} = A.extendIdeal a := by
      simp [a, SArithmeticData.extendIdeal, Ideal.map_top]
    have hh := numeratorExterior_unique A ⟨1, one_ne_zero⟩ a ha
    exact congrArg (fun b : A.Exterior => b.val) hh
  have hfield : FixedSResidue.fieldUnit A ⟨1, one_ne_zero⟩ = 1 := by
    apply Units.ext
    rfl
  simp only [exteriorCoefficient, hn, omega.map_top', localInverseProduct_eq,
    hfield, map_one, Units.val_one, div_one]

theorem exterior_coprime_sfactor (A : SArithmeticData F) (f fS qO : Ideal (𝓞 F))
    (hsplit : FixedSResidue.ConductorSplit A f fS qO) (a : A.Exterior) :
    a.val ⊔ fS = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (a.val ⊔ fS) hne
  have hM0 : M ≠ ⊥ := ne_bot_of_le_ne_bot a.property.1 (le_sup_left.trans hle)
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hM0⟩
  have hv : v ∈ A.Sf := hsplit.2.2.2.2.1 v (le_sup_right.trans hle)
  have hc : A.cS ≤ M := by
    change A.Sf.prod (fun w => w.asIdeal) ≤ v.asIdeal
    exact (Ideal.prod_le_inf : A.Sf.prod (fun w => w.asIdeal) ≤ A.Sf.inf (fun w => w.asIdeal)).trans
      (Finset.inf_le hv)
  have htop : (⊤ : Ideal (𝓞 F)) ≤ M := by
    rw [← a.property.2]
    exact sup_le (le_sup_left.trans hle) hc
  exact hM.ne_top (top_unique htop)

theorem exterior_character_eq_zero_iff (A : SArithmeticData F) (f fS qO : Ideal (𝓞 F))
    (omega : RayClassCharacter F f) (hsplit : FixedSResidue.ConductorSplit A f fS qO)
    (a : A.Exterior) : omega a.val = 0 ↔ a.val ⊔ qO ≠ ⊤ := by
  rw [omega.eq_zero_iff']
  simp only [a.property.1, false_or]
  have hs : IsCoprime a.val fS := Ideal.isCoprime_iff_sup_eq.mpr (exterior_coprime_sfactor A f fS qO hsplit a)
  have he : a.val ⊔ f = ⊤ ↔ a.val ⊔ qO = ⊤ := by
    rw [hsplit.2.2.2.1]
    constructor
    · intro h
      exact top_unique (h.symm.le.trans (sup_le_sup_left Ideal.mul_le_right _))
    · intro h
      exact Ideal.isCoprime_iff_sup_eq.mp (hs.mul_right (Ideal.isCoprime_iff_sup_eq.mpr h))
  exact not_congr he

theorem exteriorCoefficient_nonunit (A : SArithmeticData F) (f fS qO : Ideal (𝓞 F))
    (omega : RayClassCharacter F f) (hsplit : FixedSResidue.ConductorSplit A f fS qO)
    (sigma : FixedSResidue.FullLocalCharacters A) (n : FixedSResidue.NonzeroSInteger A)
    (hn : ¬ IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO) n.val)) :
    exteriorCoefficient A f omega sigma n = 0 := by
  have hz : omega (numeratorExterior A n).val = 0 := by
    rw [exterior_character_eq_zero_iff A f fS qO omega hsplit]
    intro hc
    apply hn
    have hsup : Ideal.span {n.val} ⊔ FixedSResidue.residueModulus A qO = ⊤ := by
      have hh := congrArg (Ideal.map (algebraMap (𝓞 F) A.R)) hc
      rw [← numeratorExterior_generates A n]
      simpa only [Ideal.map_sup, Ideal.map_top, SArithmeticData.extendIdeal,
        FixedSResidue.residueModulus] using hh
    have hm := congrArg (Ideal.map (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO))) hsup
    simp only [Ideal.map_sup, Ideal.map_top, Ideal.map_quotient_self, sup_bot_eq,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top] at hm
    exact hm
  simp [exteriorCoefficient, hz]

theorem exists_residue_character_of_coefficient (A : SArithmeticData F) (q : Ideal A.R)
    (c : A.R → ℂ) (hone : c 1 = 1) (hmul : ∀ x y, c (x*y) = c x * c y)
    (hfiber : ∀ x y, Ideal.Quotient.mk q x = Ideal.Quotient.mk q y → c x = c y)
    (hzero : ∀ x, ¬ IsUnit (Ideal.Quotient.mk q x) → c x = 0) :
    ∃ lam : FixedSResidue.ResidueCharacter A q,
      ∀ x, FixedSResidue.residueZeroExtension A q lam (Ideal.Quotient.mk q x) = c x := by
  let rep : A.R ⧸ q → A.R := fun x => (Ideal.Quotient.mk_surjective x).choose
  have hrep (x : A.R ⧸ q) : Ideal.Quotient.mk q (rep x) = x :=
    (Ideal.Quotient.mk_surjective x).choose_spec
  let chi : MulChar (A.R ⧸ q) ℂ :=
    { toFun := fun x => c (rep x)
      map_one' := by
        exact (hfiber _ 1 (by simpa using hrep 1)).trans hone
      map_mul' := by
        intro x y
        calc
          c (rep (x*y)) = c (rep x * rep y) := hfiber _ _ (by simp [hrep])
          _ = c (rep x) * c (rep y) := hmul _ _
      map_nonunit' := by
        intro x hx
        exact hzero _ (by simpa only [hrep] using hx) }
  refine ⟨chi.toUnitHom, ?_⟩
  intro x
  have he : MulChar.ofUnitHom chi.toUnitHom = chi := MulChar.equivToUnitHom.symm_apply_apply chi
  change MulChar.ofUnitHom chi.toUnitHom (Ideal.Quotient.mk q x) = c x
  rw [he]
  exact hfiber _ _ (hrep _)

theorem exists_exterior_residue_character_of_coefficient_congr
    (A : SArithmeticData F) (f fS qO : Ideal (𝓞 F))
    (omega : RayClassCharacter F f) (hsplit : FixedSResidue.ConductorSplit A f fS qO)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hcongr : ∀ n m : FixedSResidue.NonzeroSInteger A,
      Ideal.Quotient.mk (FixedSResidue.residueModulus A qO) n.val =
        Ideal.Quotient.mk (FixedSResidue.residueModulus A qO) m.val →
      exteriorCoefficient A f omega sigma n = exteriorCoefficient A f omega sigma m) :
    ∃ lam : FixedSResidue.ResidueCharacter A (FixedSResidue.residueModulus A qO),
      FixedSResidue.ExteriorDecomposition A f omega sigma (FixedSResidue.residueModulus A qO) lam := by
  let q := FixedSResidue.residueModulus A qO
  suffices hres : ∃ lam : FixedSResidue.ResidueCharacter A q,
      ∀ n : FixedSResidue.NonzeroSInteger A,
        FixedSResidue.residueZeroExtension A q lam (Ideal.Quotient.mk q n.val) =
          exteriorCoefficient A f omega sigma n by
    obtain ⟨lam, hlam⟩ := hres
    refine ⟨lam, ?_⟩
    intro a n hn
    have he := numeratorExterior_unique A n a hn
    rw [hlam]
    change omega a.val = FixedSResidue.localInverseProduct A sigma n *
      (omega (numeratorExterior A n).val / FixedSResidue.localInverseProduct A sigma n)
    rw [he]
    exact (mul_div_cancel₀ _ (localInverseProduct_ne_zero A sigma n)).symm
  by_cases htop : q = ⊤
  · have hcongrTop : ∀ n m : FixedSResidue.NonzeroSInteger A,
        exteriorCoefficient A f omega sigma n = exteriorCoefficient A f omega sigma m := by
      intro n m
      apply hcongr
      change Ideal.Quotient.mk q n.val = Ideal.Quotient.mk q m.val
      rw [htop]
      exact Subsingleton.elim _ _
    rw [htop]
    refine ⟨1, ?_⟩
    intro n
    rw [FixedSResidue.residueZeroExtension_top]
    exact ((hcongrTop n ⟨1, one_ne_zero⟩).trans (exteriorCoefficient_one A f omega sigma)).symm
  have hzero : ¬ IsUnit (Ideal.Quotient.mk q (0 : A.R)) := by
    rw [map_zero, isUnit_zero_iff]
    intro h
    apply htop
    apply (Ideal.eq_top_iff_one q).mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h.symm)
  let c : A.R → ℂ := fun x => if hx : x = 0 then 0 else
    exteriorCoefficient A f omega sigma ⟨x, hx⟩
  have hc (n : FixedSResidue.NonzeroSInteger A) : c n.val = exteriorCoefficient A f omega sigma n := by
    simp [c, n.property]
  have hc0 : c 0 = 0 := by simp [c]
  have hcunit : ∀ x, ¬ IsUnit (Ideal.Quotient.mk q x) → c x = 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using hc0
    · rw [hc ⟨x, hx0⟩]
      exact exteriorCoefficient_nonunit A f fS qO omega hsplit sigma ⟨x, hx0⟩ hx
  have hcmul : ∀ x y, c (x*y) = c x * c y := by
    intro x y
    by_cases hx : x = 0
    · simp [hx, hc0]
    by_cases hy : y = 0
    · simp [hy, hc0]
    rw [hc ⟨x*y, mul_ne_zero hx hy⟩, hc ⟨x,hx⟩, hc ⟨y,hy⟩]
    exact exteriorCoefficient_mul A f omega sigma ⟨x,hx⟩ ⟨y,hy⟩
  have hcfiber : ∀ x y, Ideal.Quotient.mk q x = Ideal.Quotient.mk q y → c x = c y := by
    intro x y hxy
    by_cases hx : x = 0
    · subst x
      rw [hc0, hcunit y (by rw [← hxy]; exact hzero)]
    by_cases hy : y = 0
    · subst y
      rw [hcunit x (by rw [hxy]; exact hzero), hc0]
    rw [hc ⟨x,hx⟩, hc ⟨y,hy⟩]
    exact hcongr ⟨x,hx⟩ ⟨y,hy⟩ hxy
  obtain ⟨lam, hlam⟩ := exists_residue_character_of_coefficient A q c
    (by rw [hc ⟨1,one_ne_zero⟩]; exact exteriorCoefficient_one A f omega sigma)
    hcmul hcfiber hcunit
  exact ⟨lam, fun n => (hlam n.val).trans (hc n)⟩

theorem numeratorExterior_eq_top_of_isUnit (A : SArithmeticData F)
    (n : FixedSResidue.NonzeroSInteger A) (hn : IsUnit n.val) :
    (numeratorExterior A n).val = ⊤ := by
  let a : A.Exterior := ⟨⊤, top_ne_bot, by simp⟩
  have ha : Ideal.span {n.val} = A.extendIdeal a := by
    simpa [a, SArithmeticData.extendIdeal, Ideal.map_top,
      Ideal.span_singleton_eq_top] using hn
  exact congrArg (fun b : A.Exterior => b.val) (numeratorExterior_unique A n a ha)

theorem exteriorCoefficient_ne_zero_of_isUnit (A : SArithmeticData F)
    (f : Ideal (𝓞 F)) (omega : RayClassCharacter F f)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (n : FixedSResidue.NonzeroSInteger A) (hn : IsUnit n.val) :
    exteriorCoefficient A f omega sigma n ≠ 0 := by
  rw [exteriorCoefficient, numeratorExterior_eq_top_of_isUnit A n hn, omega.map_top']
  exact div_ne_zero one_ne_zero (localInverseProduct_ne_zero A sigma n)

theorem exists_common_integral_numerators (A : SArithmeticData F)
    (n m : FixedSResidue.NonzeroSInteger A) :
    ∃ (d : FixedSResidue.NonzeroSInteger A) (a b : 𝓞 F),
      IsUnit d.val ∧ a ≠ 0 ∧ b ≠ 0 ∧
      algebraMap (𝓞 F) A.R a = d.val * n.val ∧
      algebraMap (𝓞 F) A.R b = d.val * m.val := by
  obtain ⟨N, a, ha⟩ := SIntegerLocalization.exists_denominator_power A.Sf n.val
  obtain ⟨M, b, hb⟩ := SIntegerLocalization.exists_denominator_power A.Sf m.val
  let t := SIntegerLocalization.denominator A.Sf
  let d : A.R := algebraMap (𝓞 F) A.R (t ^ (N + M))
  have ht : IsUnit (algebraMap (𝓞 F) A.R t) := by
    letI := SIntegerLocalization.isLocalization_away A.Sf
    exact IsLocalization.Away.algebraMap_isUnit t
  have hd : IsUnit d := by simpa only [d, map_pow] using ht.pow (N+M)
  have hd0 : d ≠ 0 := hd.ne_zero
  have har : algebraMap (𝓞 F) A.R (t^M*a) = d*n.val := by
    apply Subtype.ext
    change algebraMap (𝓞 F) F (t^M*a) = algebraMap (𝓞 F) F (t^(N+M)) * (n.val : F)
    rw [map_mul, map_pow, ha, map_pow, pow_add]
    ring
  have hbr : algebraMap (𝓞 F) A.R (t^N*b) = d*m.val := by
    apply Subtype.ext
    change algebraMap (𝓞 F) F (t^N*b) = algebraMap (𝓞 F) F (t^(N+M)) * (m.val : F)
    rw [map_mul, map_pow, hb, map_pow, pow_add]
    ring
  refine ⟨⟨d, hd0⟩, t^M*a, t^N*b, hd, ?_, ?_, har, hbr⟩
  · intro ha0
    rw [ha0, map_zero] at har
    exact mul_ne_zero hd0 n.property har.symm
  · intro hb0
    rw [hb0, map_zero] at hbr
    exact mul_ne_zero hd0 m.property hbr.symm

theorem exteriorCoefficient_congr_of_integral_congr (A : SArithmeticData F)
    (f : Ideal (𝓞 F)) (omega : RayClassCharacter F f)
    (sigma : FixedSResidue.FullLocalCharacters A) (q : Ideal A.R)
    (hcongr : ∀ (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0),
      Ideal.Quotient.mk q (algebraMap (𝓞 F) A.R a) =
        Ideal.Quotient.mk q (algebraMap (𝓞 F) A.R b) →
      exteriorCoefficient A f omega sigma
        ⟨algebraMap (𝓞 F) A.R a, (FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne ha⟩ =
      exteriorCoefficient A f omega sigma
        ⟨algebraMap (𝓞 F) A.R b, (FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne hb⟩) :
    ∀ n m : FixedSResidue.NonzeroSInteger A,
      Ideal.Quotient.mk q n.val = Ideal.Quotient.mk q m.val →
      exteriorCoefficient A f omega sigma n = exteriorCoefficient A f omega sigma m := by
  intro n m hnm
  obtain ⟨d, a, b, hd, ha, hb, han, hbm⟩ := exists_common_integral_numerators A n m
  have hab : Ideal.Quotient.mk q (algebraMap (𝓞 F) A.R a) =
      Ideal.Quotient.mk q (algebraMap (𝓞 F) A.R b) := by rw [han, hbm, map_mul, map_mul, hnm]
  have he := hcongr a b ha hb hab
  have hea : (⟨algebraMap (𝓞 F) A.R a,
      (FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne ha⟩ : FixedSResidue.NonzeroSInteger A) =
      ⟨d.val*n.val, mul_ne_zero d.property n.property⟩ := Subtype.ext han
  have heb : (⟨algebraMap (𝓞 F) A.R b,
      (FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne hb⟩ : FixedSResidue.NonzeroSInteger A) =
      ⟨d.val*m.val, mul_ne_zero d.property m.property⟩ := Subtype.ext hbm
  rw [hea, heb, exteriorCoefficient_mul, exteriorCoefficient_mul] at he
  exact mul_left_cancel₀ (exteriorCoefficient_ne_zero_of_isUnit A f omega sigma d hd) he

end

theorem exists_exterior_residue_character
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (omega : PrimitiveFrequencyCharacter F)
    (fS qO : Ideal (𝓞 F))
    (hsplit : FixedSResidue.ConductorSplit A omega.conductor fS qO)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hinfinite : ∀ w : InfinitePlace F, sigma.1 w = 1)
    (hlocal : ∀ v : {v // v ∈ A.Sf},
      ∃ delta : (v.val.adicCompletion F)ˣ →ₜ* ℂˣ,
        delta.toMonoidHom = sigma.2 v ∧
          IsFrequencyLocalComponent F omega v.val delta) :
    ∃ lam : FixedSResidue.ResidueCharacter A (FixedSResidue.residueModulus A qO),
      FixedSResidue.ExteriorDecomposition A omega.conductor omega.character sigma
        (FixedSResidue.residueModulus A qO) lam := by
  apply exists_exterior_residue_character_of_coefficient_congr A omega.conductor fS qO
    omega.character hsplit sigma
  apply exteriorCoefficient_congr_of_integral_congr
  intro a b ha hb hab
  let n : FixedSResidue.NonzeroSInteger A :=
    ⟨algebraMap (𝓞 F) A.R a, (FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne ha⟩
  let m : FixedSResidue.NonzeroSInteger A :=
    ⟨algebraMap (𝓞 F) A.R b, (FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne hb⟩
  change exteriorCoefficient A omega.conductor omega.character sigma n =
    exteriorCoefficient A omega.conductor omega.character sigma m
  by_cases hn : IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO) n.val)
  · have hm : IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO) m.val) := by
      change IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
        (algebraMap (𝓞 F) A.R b))
      rw [← hab]
      exact hn
    have habO : a - b ∈ qO :=
      (ExteriorCharacterSteps.integral_residue_congr_iff F A qO
        hsplit.2.2.1 hsplit.2.2.2.2.2 a b).mp hab
    obtain ⟨c, hc, hca, hcS, hcext⟩ :=
      ExteriorCharacterSteps.exists_exterior_crt_representative F A
        omega.conductor fS qO hsplit a
    have hcb : c - b ∈ qO := by
      simpa only [sub_add_sub_cancel] using qO.add_mem hca habO
    have hna := ExteriorCharacterSteps.integral_exterior_crt_transfer F A omega fS qO
      hsplit sigma hinfinite hlocal a c ha hc hn hca hcS hcext
      (numeratorExterior A n) (numeratorExterior_generates A n).symm
    have hmb := ExteriorCharacterSteps.integral_exterior_crt_transfer F A omega fS qO
      hsplit sigma hinfinite hlocal b c hb hc hm hcb hcS hcext
      (numeratorExterior A m) (numeratorExterior_generates A m).symm
    change omega.character (numeratorExterior A n).val =
      FixedSResidue.localInverseProduct A sigma n * omega.character (Ideal.span {c}) at hna
    change omega.character (numeratorExterior A m).val =
      FixedSResidue.localInverseProduct A sigma m * omega.character (Ideal.span {c}) at hmb
    rw [exteriorCoefficient, exteriorCoefficient, hna, hmb]
    rw [mul_div_cancel_left₀ _ (localInverseProduct_ne_zero A sigma n),
      mul_div_cancel_left₀ _ (localInverseProduct_ne_zero A sigma m)]
  · have hm : ¬ IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO) m.val) := by
      change ¬ IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
        (algebraMap (𝓞 F) A.R b))
      rw [← hab]
      exact hn
    rw [exteriorCoefficient_nonunit A omega.conductor fS qO omega.character hsplit sigma n hn,
      exteriorCoefficient_nonunit A omega.conductor fS qO omega.character hsplit sigma m hm]

end DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter

end
