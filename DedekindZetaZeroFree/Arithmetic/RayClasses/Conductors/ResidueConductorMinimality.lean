module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.SIntegerResidueCharacters
public import DedekindZetaZeroFree.CharacterSums.Gauss.PrimitiveResidueCharacters
public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerPrincipalIdealIndex

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.Detector.FixedSResidue

noncomputable section

variable {F : Type} [Field F] [NumberField F]

def unitReduction (A : SArithmeticData F) (q q' : Ideal A.R)
    (hqq' : q ≤ q') : (A.R ⧸ q)ˣ →* (A.R ⧸ q')ˣ :=
  Units.map (Ideal.Quotient.factor hqq').toMonoidHom

def FactorsThrough (A : SArithmeticData F) (q q' : Ideal A.R)
    (hqq' : q ≤ q') (lam : ResidueCharacter A q) : Prop :=
  ∃ lam' : ResidueCharacter A q',
    ∀ u : (A.R ⧸ q)ˣ, lam u = lam' (unitReduction A q q' hqq' u)

def IsConductorMinimal (A : SArithmeticData F) (q : Ideal A.R)
    (lam : ResidueCharacter A q) : Prop :=
  ∀ (q' : Ideal A.R) (hqq' : q < q'),
    ¬ FactorsThrough A q q' hqq'.le lam

def SLocalConductorTrivial (A : SArithmeticData F)
    (fS : Ideal (𝓞 F)) (sigma : FullLocalCharacters A) : Prop :=
  ∀ (alpha : 𝓞 F) (n : NonzeroSInteger A),
    (n.val : F) = (alpha : F) → alpha - 1 ∈ fS →
      Ideal.span {alpha} ⊔ A.cS = ⊤ → localInverseProduct A sigma n = 1

private theorem unit_mk_of_coprime {R : Type*} [CommRing R]
    (q : Ideal R) (x : R) (hc : Ideal.span {x} ⊔ q = ⊤) :
    IsUnit (Ideal.Quotient.mk q x) := by
  have h : Ideal.map (Ideal.Quotient.mk q) (Ideal.span {x}) = ⊤ := by
    have hh := congrArg (Ideal.map (Ideal.Quotient.mk q)) hc
    simpa only [Ideal.map_sup, Ideal.map_top, Ideal.map_quotient_self, sup_bot_eq] using hh
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top] at h
  exact h

theorem exterior_principal_value_one_of_factorization
    (A : SArithmeticData F) (f fS qO : Ideal (𝓞 F))
    (omega : RayClassCharacter F f)
    (sigma : FullLocalCharacters A)
    (lam : ResidueCharacter A (residueModulus A qO))
    (hdecomp : ExteriorDecomposition A f omega sigma (residueModulus A qO) lam)
    (hlocal : SLocalConductorTrivial A fS sigma)
    (q' : Ideal A.R) (hqq' : residueModulus A qO ≤ q')
    (hfactor : FactorsThrough A (residueModulus A qO) q' hqq' lam)
    (alpha : 𝓞 F) (ha : alpha ≠ 0) (haS : Ideal.span {alpha} ⊔ A.cS = ⊤)
    (hafS : alpha - 1 ∈ fS)
    (haq : Ideal.span {alpha} ⊔ qO = ⊤)
    (haq' : algebraMap (𝓞 F) A.R (alpha - 1) ∈ q') :
    omega (Ideal.span {alpha}) = 1 := by
  let n : NonzeroSInteger A := ⟨algebraMap (𝓞 F) A.R alpha, by
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne ha⟩
  let a : A.Exterior := ⟨Ideal.span {alpha}, Ideal.span_singleton_eq_bot.not.mpr ha, haS⟩
  have he : Ideal.span {n.val} = A.extendIdeal a := by
    simp [SArithmeticData.extendIdeal, a, n, Ideal.map_span]
  have hv := hdecomp a n he
  have hl := hlocal alpha n rfl hafS haS
  have hc : Ideal.span {n.val} ⊔ residueModulus A qO = ⊤ := by
    have hh := congrArg (Ideal.map (algebraMap (𝓞 F) A.R)) haq
    simpa only [Ideal.map_sup, Ideal.map_top, Ideal.map_span, Set.image_singleton, n, residueModulus] using hh
  obtain ⟨u, hu⟩ := unit_mk_of_coprime (residueModulus A qO) n.val hc
  have hr : unitReduction A (residueModulus A qO) q' hqq' u = 1 := by
    apply Units.ext
    change Ideal.Quotient.factor hqq' (u : A.R ⧸ residueModulus A qO) = 1
    rw [hu]
    change Ideal.Quotient.mk q' n.val = Ideal.Quotient.mk q' 1
    apply Ideal.Quotient.eq.mpr
    simpa [n] using haq'
  obtain ⟨lam', hlam'⟩ := hfactor
  have hlu : lam u = 1 := by rw [hlam', hr, map_one]
  change omega (Ideal.span {alpha}) = _ at hv
  rw [hl, one_mul, ← hu, residueZeroExtension_unit, hlu] at hv
  exact hv.trans (by simp)

private theorem lift_divisor (A : SArithmeticData F) (qO : Ideal (𝓞 F))
    (hq0 : qO ≠ ⊥) (hq : qO ⊔ A.cS = ⊤) (q' : Ideal A.R)
    (hlt : residueModulus A qO < q') :
    ∃ Q : Ideal (𝓞 F), qO < Q ∧ residueModulus A Q = q' := by
  let qo : A.Exterior := ⟨qO, hq0, hq⟩
  have hq' : q' ≠ ⊥ := ne_bot_of_gt (lt_of_le_of_lt bot_le hlt)
  let Q := A.exteriorIdealEquiv.symm ⟨q', hq'⟩
  have heQ : A.extendIdeal Q = q' := by
    rw [← A.exteriorIdealEquiv_apply Q]
    exact congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply ⟨q', hq'⟩)
  let B : A.Exterior := ⟨qO ⊔ Q.val, ne_bot_of_le_ne_bot hq0 le_sup_left,
    (le_antisymm le_top (by calc
      ⊤ = qO ⊔ A.cS := hq.symm
      _ ≤ (qO ⊔ Q.val) ⊔ A.cS := sup_le_sup_right le_sup_left _))⟩
  have heB : A.extendIdeal B = q' := by
    change Ideal.map _ (qO ⊔ Q.val) = q'
    rw [Ideal.map_sup]
    change residueModulus A qO ⊔ A.extendIdeal Q = q'
    rw [heQ, sup_eq_right.mpr hlt.le]
  have hBQ : B = Q := A.exteriorIdealEquiv.injective (Subtype.ext (by
    rw [A.exteriorIdealEquiv_apply, A.exteriorIdealEquiv_apply, heB, heQ]))
  have hle : qO ≤ Q.val := (show qO ≤ B.val from le_sup_left).trans_eq
    (congrArg Subtype.val hBQ)
  refine ⟨Q.val, lt_of_le_of_ne hle ?_, heQ⟩
  intro he
  apply ne_of_lt hlt
  exact (congrArg (residueModulus A) he).trans heQ

private theorem coprime_of_sub_one_mem {R : Type*} [CommRing R]
    (m : Ideal R) (a : R) (h : a - 1 ∈ m) : Ideal.span {a} ⊔ m = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have ha : a ∈ Ideal.span {a} ⊔ m := Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)
  have hb : a - 1 ∈ Ideal.span {a} ⊔ m := Ideal.mem_sup_right h
  simpa using (Ideal.span {a} ⊔ m).sub_mem ha hb

private theorem exterior_representative (A : SArithmeticData F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊤) (a : 𝓞 F)
    (hc : Ideal.span {a} ⊔ f = ⊤) :
    ∃ b : 𝓞 F, b ≠ 0 ∧ b - a ∈ f ∧ Ideal.span {b} ⊔ A.cS = ⊤ := by
  let s := A.Sf.filter (fun v => ¬ f ≤ v.asIdeal)
  let B : Ideal (𝓞 F) := ∏ v ∈ s, v.asIdeal
  have hcop : f ⊔ B = ⊤ := by
    apply Ideal.sup_prod_eq_top
    intro v hv
    have hn : ¬ f ≤ v.asIdeal := (Finset.mem_filter.mp hv).2
    rw [sup_comm]
    exact (Ideal.isMaximal_def.mp v.isMaximal).2 _
      (lt_of_le_of_ne le_sup_left (fun he => hn (he ▸ le_sup_right)))
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp
    (show (1 : 𝓞 F) ∈ f ⊔ B by rw [hcop]; trivial)
  let b : 𝓞 F := a * y + x
  have hba : b - a ∈ f := by
    have he : b - a = (1 - a) * x := by dsimp [b]; linear_combination a * hxy
    rw [he]
    exact f.mul_mem_left _ hx
  have hb1 : b - 1 ∈ B := by
    have he : b - 1 = (a - 1) * y := by dsimp [b]; linear_combination hxy
    rw [he]
    exact B.mul_mem_left _ hy
  have hbc : Ideal.span {b} ⊔ f = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hab : a ∈ Ideal.span {b} ⊔ f := by
      have h1 : b ∈ Ideal.span {b} ⊔ f := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
      have h2 : b - a ∈ Ideal.span {b} ⊔ f := Ideal.mem_sup_right hba
      simpa using (Ideal.span {b} ⊔ f).sub_mem h1 h2
    have hle : Ideal.span {a} ⊔ f ≤ Ideal.span {b} ⊔ f :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hab) le_sup_right
    exact hle (by rw [hc]; trivial)
  have hb0 : b ≠ 0 := by
    intro hb
    apply hf
    simpa [hb] using hbc
  refine ⟨b, hb0, hba, ?_⟩
  apply Ideal.sup_prod_eq_top
  intro v hv
  by_cases hfv : f ≤ v.asIdeal
  · apply top_unique
    calc
      ⊤ = Ideal.span {b} ⊔ f := hbc.symm
      _ ≤ Ideal.span {b} ⊔ v.asIdeal := sup_le_sup_left hfv _
  · apply coprime_of_sub_one_mem
    have hvB : B ≤ v.asIdeal := by
      apply le_trans (Ideal.prod_le_inf (s := s) (f := fun w => w.asIdeal))
      exact Finset.inf_le (by simp [s, hfv, hv])
    exact hvB hb1

private theorem no_real_embedding (A : SArithmeticData F) (phi : F →+* ℝ) : False := by
  have hp : phi A.zeta12 ^ 6 = -1 := by simpa using congrArg phi A.zeta12_pow_six
  have hn := sq_nonneg (phi A.zeta12 ^ 3)
  rw [← pow_mul] at hn
  norm_num at hn
  linarith

 theorem principal_value_congr
    (A : SArithmeticData F) (f : Ideal (𝓞 F)) (omega : RayClassCharacter F f)
    (alpha beta : 𝓞 F) (ha : alpha ≠ 0) (hb : beta ≠ 0)
    (hac : Ideal.span {alpha} ⊔ f = ⊤) (hc : alpha - beta ∈ f) :
    omega (Ideal.span {alpha}) = omega (Ideal.span {beta}) := by
  have hpos (x : 𝓞 F) : ∀ phi : F →+* ℝ, 0 < phi (x : F) := by
    intro phi
    exact (no_real_embedding A phi).elim
  by_cases hft : f = ⊤
  · rw [omega.map_span' alpha ha (by simp [hft]) (hpos alpha),
        omega.map_span' beta hb (by simp [hft]) (hpos beta)]
  obtain ⟨u, hu⟩ := unit_mk_of_coprime f alpha hac
  obtain ⟨gamma, hg⟩ := Ideal.Quotient.mk_surjective (u⁻¹ : (𝓞 F ⧸ f)ˣ).val
  have haeq : Ideal.Quotient.mk f (alpha * gamma) = 1 := by
    rw [map_mul, ← hu, hg]
    exact u.val_inv
  have hag : alpha * gamma - 1 ∈ f := Ideal.Quotient.eq.mp (by simpa using haeq)
  have hg0 : gamma ≠ 0 := by
    intro h
    subst gamma
    have h1 : (1 : 𝓞 F) ∈ f := by simpa using f.neg_mem hag
    exact hft (Ideal.eq_top_of_isUnit_mem f h1 isUnit_one)
  have hbeq : Ideal.Quotient.mk f beta = Ideal.Quotient.mk f alpha :=
    (Ideal.Quotient.eq.mpr hc).symm
  have hbg : beta * gamma - 1 ∈ f := by
    apply Ideal.Quotient.eq.mp
    simpa only [map_mul, map_one, hbeq] using haeq
  have hoa : omega (Ideal.span {alpha * gamma}) = 1 :=
    omega.map_span' _ (mul_ne_zero ha hg0) hag (hpos _)
  have hob : omega (Ideal.span {beta * gamma}) = 1 :=
    omega.map_span' _ (mul_ne_zero hb hg0) hbg (hpos _)
  rw [← Ideal.span_singleton_mul_span_singleton, omega.map_mul'] at hoa hob
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one hoa) (hoa.trans hob.symm)

theorem hecke_conductor_implies_residue_minimality
    (A : SArithmeticData F) (f fS qO : Ideal (𝓞 F))
    (omega : RayClassCharacter F f) (hprimitive : omega.IsPrimitive)
    (hsplit : ConductorSplit A f fS qO)
    (sigma : FullLocalCharacters A) (horder : HasFiniteOrder A sigma)
    (lam : ResidueCharacter A (residueModulus A qO))
    (hdecomp : ExteriorDecomposition A f omega sigma (residueModulus A qO) lam)
    (hlocal : SLocalConductorTrivial A fS sigma) :
    IsConductorMinimal A (residueModulus A qO) lam := by
  intro q' hlt hfactor
  obtain ⟨hf0, hfS0, hqO0, hsplit, hS, hqS⟩ := hsplit
  obtain ⟨Q, hQ, heQ⟩ := lift_divisor A qO hqO0 hqS q' hlt
  have hff' : f < fS * Q := by
    rw [hsplit]
    exact mul_lt_mul_of_pos_left hQ (bot_lt_iff_ne_bot.mpr hfS0)
  have hf : f ≠ ⊤ := ne_top_of_lt hff'
  obtain ⟨a, ha, ham, hpos, hc, hne⟩ := hprimitive (fS * Q) hff'
  obtain ⟨b, hb, hba, hbS⟩ := exterior_representative A f hf a hc
  have hbf : Ideal.span {b} ⊔ f = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hab : a ∈ Ideal.span {b} ⊔ f := by
      have h1 : b ∈ Ideal.span {b} ⊔ f := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
      have h2 : b - a ∈ Ideal.span {b} ⊔ f := Ideal.mem_sup_right hba
      simpa using (Ideal.span {b} ⊔ f).sub_mem h1 h2
    have hle : Ideal.span {a} ⊔ f ≤ Ideal.span {b} ⊔ f :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hab) le_sup_right
    exact hle (by rw [hc]; trivial)
  have hbm : b - 1 ∈ fS * Q := by
    have hba' : b - a ∈ fS * Q := hff'.le hba
    convert (fS * Q).add_mem hba' ham using 1 <;> ring
  have hbq : Ideal.span {b} ⊔ qO = ⊤ := by
    apply top_unique
    calc
      ⊤ = Ideal.span {b} ⊔ f := hbf.symm
      _ ≤ Ideal.span {b} ⊔ qO := sup_le_sup_left (by rw [hsplit]; exact Ideal.mul_le_right) _
  have hone : omega (Ideal.span {b}) = 1 :=
    exterior_principal_value_one_of_factorization A f fS qO omega sigma lam hdecomp hlocal
      q' hlt.le hfactor b hb hbS (Ideal.mul_le_left hbm) hbq (by
        rw [← heQ]
        exact Ideal.mem_map_of_mem (algebraMap (𝓞 F) A.R) (Ideal.mul_le_right hbm))
  exact hne ((principal_value_congr A f omega a b ha hb hc (by simpa using f.neg_mem hba)).trans hone)

theorem nonunit_stabilizer_witness (A : SArithmeticData F) (q : Ideal A.R)
    [Finite (A.R ⧸ q)] (lam : ResidueCharacter A q)
    (hminimal : IsConductorMinimal A q lam)
    (x : A.R ⧸ q) (hx : ¬ IsUnit x) :
    ∃ u : (A.R ⧸ q)ˣ, (u : A.R ⧸ q) * x = x ∧ lam u ≠ 1 := by
  let J : Ideal (A.R ⧸ q) :=
    (Submodule.span (A.R ⧸ q) {x}).annihilator
  have hJ (y : A.R ⧸ q) : y ∈ J ↔ y * x = 0 := by
    exact Submodule.mem_annihilator_span_singleton x y
  let q' : Ideal A.R := Ideal.comap (Ideal.Quotient.mk q) J
  have hle : q ≤ q' := by
    intro y hy
    change Ideal.Quotient.mk q y ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    exact J.zero_mem
  have hlt : q < q' := by
    refine lt_of_le_of_ne hle ?_
    intro he
    apply hx
    apply IsRightRegular.isUnit_of_finite
    intro a b hab
    change a * x = b * x at hab
    have hz : (a - b) * x = 0 := by rw [sub_mul, hab, sub_self]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (a - b)
    have hymem : y ∈ q' := (hJ _).mpr (hy.symm ▸ hz)
    rw [← he] at hymem
    have : a - b = 0 := hy.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hymem)
    exact sub_eq_zero.mp this
  by_contra hn
  have htrivial : ∀ u : (A.R ⧸ q)ˣ, (u : A.R ⧸ q) * x = x → lam u = 1 := by
    intro u hu
    by_contra hl
    exact hn ⟨u, hu, hl⟩
  let rho := unitReduction A q q' hle
  have hker : rho.ker ≤ lam.ker := by
    intro u hu
    apply htrivial u
    change rho u = 1 at hu
    have hval := congrArg (fun v : (A.R ⧸ q')ˣ => (v : A.R ⧸ q')) hu
    have hmem : (u : A.R ⧸ q) - 1 ∈ J := by
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : A.R ⧸ q)
      have he : Ideal.Quotient.mk q' y = Ideal.Quotient.mk q' 1 := by
        simpa [rho, unitReduction, ← hy] using hval
      have hm : y - 1 ∈ q' := Ideal.Quotient.eq.mp he
      change Ideal.Quotient.mk q (y - 1) ∈ J at hm
      simpa [hy] using hm
    have hz := (hJ _).mp hmem
    rw [sub_mul, one_mul] at hz
    exact sub_eq_zero.mp hz
  let rr := rho.rangeRestrict
  have hker' : rr.ker ≤ lam.ker := by simpa [rr] using hker
  let lc : rho.range →* ℂˣ := rr.liftOfSurjective rho.rangeRestrict_surjective ⟨lam, hker'⟩
  letI : Finite (A.R ⧸ q') :=
    Finite.of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  obtain ⟨lext, hext⟩ := MonoidHom.domRestrict_surjective (G := (A.R ⧸ q')ˣ) ℂ rho.range lc
  apply hminimal q' hlt
  refine ⟨lext, ?_⟩
  intro u
  have he := congrArg (fun c : rho.range →* ℂˣ => c (rr u)) hext
  have hlc : lc (rr u) = lam u :=
    rr.liftOfRightInverse_comp_apply _ _ _ _
  exact hlc.symm.trans he.symm

private theorem finite_residueModulus (A : SArithmeticData F)
    (qO : Ideal (NumberField.RingOfIntegers F)) (hqO : qO ≠ ⊥) :
    Finite (A.R ⧸ residueModulus A qO) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hqO
  let b : A.R := algebraMap (𝓞 F) A.R a
  have hb : b ≠ 0 := by
    intro h
    apply ha0
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) A.R) h
  letI := (sProductModulus_eq_principalIdeal_index F A.Sf b hb).1
  have hle : Ideal.span {b} ≤ residueModulus A qO := by
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact Ideal.mem_map_of_mem (algebraMap (𝓞 F) A.R) ha
  exact Finite.of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)

theorem hecke_nonunit_stabilizer_witness
    (A : SArithmeticData F) (f fS qO : Ideal (𝓞 F))
    (omega : RayClassCharacter F f) (hprimitive : omega.IsPrimitive)
    (hsplit : ConductorSplit A f fS qO)
    (sigma : FullLocalCharacters A) (horder : HasFiniteOrder A sigma)
    (lam : ResidueCharacter A (residueModulus A qO))
    (hdecomp : ExteriorDecomposition A f omega sigma (residueModulus A qO) lam)
    (hlocal : SLocalConductorTrivial A fS sigma)
    (x : A.R ⧸ residueModulus A qO) (hx : ¬ IsUnit x) :
    ∃ u : (A.R ⧸ residueModulus A qO)ˣ,
      (u : A.R ⧸ residueModulus A qO) * x = x ∧ lam u ≠ 1 := by
  letI := finite_residueModulus A qO hsplit.2.2.1
  exact nonunit_stabilizer_witness A (residueModulus A qO) lam
    (hecke_conductor_implies_residue_minimality A f fS qO omega hprimitive
      hsplit sigma horder lam hdecomp hlocal) x hx

theorem hecke_zeroExtension_isPrimitiveResidueCharacter
    (A : SArithmeticData F) (f fS qO : Ideal (𝓞 F))
    (omega : RayClassCharacter F f) (hprimitive : omega.IsPrimitive)
    (hsplit : ConductorSplit A f fS qO)
    (sigma : FullLocalCharacters A) (horder : HasFiniteOrder A sigma)
    (lam : ResidueCharacter A (residueModulus A qO))
    (hdecomp : ExteriorDecomposition A f omega sigma (residueModulus A qO) lam)
    (hlocal : SLocalConductorTrivial A fS sigma) :
    IsPrimitiveResidueCharacter (residueZeroExtension A (residueModulus A qO) lam) := by
  intro x hx
  obtain ⟨u, hu, hlu⟩ := hecke_nonunit_stabilizer_witness
    A f fS qO omega hprimitive hsplit sigma horder lam hdecomp hlocal x hx
  refine ⟨u, ?_, ?_⟩
  · rw [residueZeroExtension_unit]
    intro h
    apply hlu
    exact Units.ext h
  · rw [mul_sub, mul_one, mul_comm x (u : A.R ⧸ residueModulus A qO), hu, sub_self]

end
end DedekindZetaZeroFree.Detector.FixedSResidue
