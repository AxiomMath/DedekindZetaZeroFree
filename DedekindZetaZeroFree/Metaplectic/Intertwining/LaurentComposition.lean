module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ArithmeticInducingData
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ConditionalCubicResidueReduction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellRestriction

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse
open KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPRankOneShellContinuation KPRankOneGenericComposition
open KPRankOneReverseRegulatorShells
open scoped TensorProduct
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

private theorem rational_eq_of_regular_infinite
    (R T : RatFunc ℂ) (u : Set ℂ) (hu : u.Infinite)
    (he : ∀ w ∈ u, R.denom.eval w ≠ 0 ∧ T.denom.eval w ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) w R = RatFunc.eval (RingHom.id ℂ) w T) : R=T := by
  have hp : R.num*T.denom=T.num*R.denom := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hu.mono
    intro w hw
    obtain ⟨hR,hT,h⟩ := he w hw
    simp only [RatFunc.eval,Polynomial.eval₂_id] at h
    change Polynomial.eval w (R.num*T.denom) = Polynomial.eval w (T.num*R.denom)
    simpa only [Polynomial.eval_mul] using (div_eq_div_iff hR hT).mp h
  have hh := (RatFunc.num_mul_eq_mul_denom_iff (RatFunc.denom_ne_zero T)).mp hp
  rwa [RatFunc.num_div_denom] at hh

private lemma scalar_regular (c : ℂ) (R : RatFunc ℂ) (w : ℂ)
    (hR : R.denom.eval w ≠ 0) :
    (c • R).denom.eval w ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) w (c • R) = c * RatFunc.eval (RingHom.id ℂ) w R := by
  rw [RatFunc.smul_eq_C_mul]
  refine ⟨?_, by rw [RatFunc.eval_mul _ _ (by simp) hR, RatFunc.eval_C]; rfl⟩
  intro h
  have hh := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd (RatFunc.C c) R) h
  exact hR (by simpa using hh)

private lemma sum_regular {ι : Type*} (s : Finset ι) (a : ι → RatFunc ℂ) (w : ℂ)
    (ha : ∀ i ∈ s, (a i).denom.eval w ≠ 0) :
    (∑ i ∈ s, a i).denom.eval w ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) w (∑ i ∈ s, a i) =
        ∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨hs,es⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    have hiR := ha i (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    refine ⟨?_, by rw [RatFunc.eval_add _ _ hiR hs,es]⟩
    intro h
    apply mul_ne_zero hiR hs
    simpa only [Polynomial.eval_mul] using
      Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd (a i) (∑ j ∈ s,a j)) h

set_option maxHeartbeats 800000 in

private theorem rational_sum_scalar {ι V : Type*} [AddCommMonoid V] [Module ℂ V]
    (s : Finset ι) (a : ι → RatFunc ℂ) (M : ι → Module.End ℂ V) (c : RatFunc ℂ)
    (U : Set ℂ) (hU : U.Infinite)
    (ha : ∀ w ∈ U, ∀ i ∈ s, (a i).denom.eval w ≠ 0)
    (hc : ∀ w ∈ U, c.denom.eval w ≠ 0)
    (hn : ∀ w ∈ U, (∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w (a i) • M i) =
      RatFunc.eval (RingHom.id ℂ) w c • LinearMap.id) :
    (∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) = c • LinearMap.id := by
  classical
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let b := Module.Free.chooseBasis ℂ V
  let e := TensorProduct.equivFinsuppOfBasisRight (M := RatFunc ℂ) b
  apply TensorProduct.AlgebraTensorModule.ext
  intro f v
  suffices h : (∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) (1 ⊗ₜ[ℂ] v) =
      (c • LinearMap.id) (1 ⊗ₜ[ℂ] v) by
    calc
      _ = f • (∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) (1 ⊗ₜ[ℂ] v) := by
        rw [← map_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
      _ = f • (c • LinearMap.id) (1 ⊗ₜ[ℂ] v) := congrArg (fun x => f • x) h
      _ = _ := by rw [← map_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  apply e.injective
  ext j
  change (e ((∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) (1 ⊗ₜ[ℂ] v))) j =
    (e ((c • LinearMap.id) (1 ⊗ₜ[ℂ] v))) j
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul,mul_one, map_sum, LinearMap.id_apply,
    Finsupp.finsetSum_apply,TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  dsimp only [e]
  simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  apply rational_eq_of_regular_infinite _ _ U hU
  intro w hw
  have hs := sum_regular s (fun i => (b.repr (M i v)) j • a i) w
    (fun i hi => (scalar_regular _ _ _ (ha w hw i hi)).1)
  have ht := scalar_regular ((b.repr v) j) c w (hc w hw)
  refine ⟨hs.1,ht.1,?_⟩
  rw [hs.2,ht.2]
  have hev : (∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w ((b.repr (M i v)) j • a i)) =
      ∑ i ∈ s, (b.repr (M i v)) j * RatFunc.eval (RingHom.id ℂ) w (a i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (scalar_regular _ _ _ (ha w hw i hi)).2
  rw [hev]
  have hh := congrArg (fun L : Module.End ℂ V => (b.repr (L v)) j) (hn w hw)
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_smul,
    Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,mul_comm] using hh

private lemma product_regular (a b : RatFunc ℂ) (w : ℂ)
    (ha : a.denom.eval w ≠ 0) (hb : b.denom.eval w ≠ 0) :
    (a*b).denom.eval w ≠ 0 := by
  intro h
  apply mul_ne_zero ha hb
  simpa only [Polynomial.eval_mul] using
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd a b) h

private theorem rational_rectangular_composition {ι κ V W : Type*}
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    (s : Finset ι) (t : Finset κ) (a : ι → RatFunc ℂ) (b : κ → RatFunc ℂ)
    (A : ι → V →ₗ[ℂ] W) (B : κ → W →ₗ[ℂ] V) (c : RatFunc ℂ)
    (U : Set ℂ) (hU : U.Infinite)
    (ha : ∀ w ∈ U, ∀ i ∈ s, (a i).denom.eval w ≠ 0)
    (hb : ∀ w ∈ U, ∀ j ∈ t, (b j).denom.eval w ≠ 0)
    (hc : ∀ w ∈ U, c.denom.eval w ≠ 0)
    (hn : ∀ w ∈ U,
      (∑ j ∈ t, RatFunc.eval (RingHom.id ℂ) w (b j) • B j).comp
        (∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w (a i) • A i) =
      RatFunc.eval (RingHom.id ℂ) w c • LinearMap.id) :
    (∑ j ∈ t, b j • (B j).baseChange (RatFunc ℂ)).comp
      (∑ i ∈ s, a i • (A i).baseChange (RatFunc ℂ)) = c • LinearMap.id := by
  classical
  have hh := rational_sum_scalar (t ×ˢ s) (fun ji => b ji.1 * a ji.2)
    (fun ji => (B ji.1).comp (A ji.2)) c U hU
    (fun w hw ji hji => product_regular _ _ w
      (hb w hw ji.1 (Finset.mem_product.mp hji).1)
      (ha w hw ji.2 (Finset.mem_product.mp hji).2)) hc ?_
  · apply LinearMap.ext
    intro v
    have hhv := LinearMap.congr_fun hh v
    simp only [Finset.sum_product,LinearMap.comp_apply,LinearMap.sum_apply,
      LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_smul,Finset.smul_sum,
      smul_smul,LinearMap.baseChange_comp] at hhv ⊢
    rw [Finset.sum_comm]
    simpa only [mul_comm] using hhv
  · intro w hw
    have he (ji : κ × ι) (hji : ji ∈ t ×ˢ s) :
        RatFunc.eval (RingHom.id ℂ) w (b ji.1 * a ji.2) =
          RatFunc.eval (RingHom.id ℂ) w (b ji.1) * RatFunc.eval (RingHom.id ℂ) w (a ji.2) :=
      RatFunc.eval_mul _ _ (hb w hw ji.1 (Finset.mem_product.mp hji).1)
        (ha w hw ji.2 (Finset.mem_product.mp hji).2)
    rw [Finset.sum_congr rfl (fun ji hji => congrArg (fun z => z • ((B ji.1).comp (A ji.2))) (he ji hji))]
    apply LinearMap.ext
    intro v
    have hhv := LinearMap.congr_fun (hn w hw) v
    simp only [Finset.sum_product,LinearMap.comp_apply,LinearMap.sum_apply,
      LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_smul,Finset.smul_sum,
      smul_smul] at hhv ⊢
    rw [Finset.sum_comm]
    simpa only [mul_comm] using hhv

 def Numeric (w : ℂ) (R : RatFunc ℂ) (c : ℂ) : Prop :=
  R.denom.eval w ≠ 0 ∧ RatFunc.eval (RingHom.id ℂ) w R = c
private lemma numeric_const (w c : ℂ) : Numeric w (RatFunc.C c) c := by simp [Numeric]
private lemma numeric_X (w : ℂ) : Numeric w RatFunc.X w := by simp [Numeric]
private lemma numeric_mul {w a b : ℂ} {A B : RatFunc ℂ}
    (ha : Numeric w A a) (hb : Numeric w B b) : Numeric w (A*B) (a*b) := by
  refine ⟨?_, by rw [RatFunc.eval_mul _ _ ha.1 hb.1,ha.2,hb.2]⟩
  intro h
  apply mul_ne_zero ha.1 hb.1
  simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd A B) h
private lemma numeric_add {w a b : ℂ} {A B : RatFunc ℂ}
    (ha : Numeric w A a) (hb : Numeric w B b) : Numeric w (A+B) (a+b) := by
  refine ⟨?_, by rw [RatFunc.eval_add _ _ ha.1 hb.1,ha.2,hb.2]⟩
  intro h
  apply mul_ne_zero ha.1 hb.1
  simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd A B) h
private lemma numeric_sub {w a b : ℂ} {A B : RatFunc ℂ}
    (ha : Numeric w A a) (hb : Numeric w B b) : Numeric w (A-B) (a-b) := by
  simpa [sub_eq_add_neg] using numeric_add ha (numeric_mul (numeric_const w (-1)) hb)
private lemma numeric_inv {w a : ℂ} {A : RatFunc ℂ}
    (ha : Numeric w A a) (ha0 : a ≠ 0) : Numeric w A⁻¹ a⁻¹ := by
  have hA0 : A ≠ 0 := by intro h; subst A; simp [Numeric] at ha; exact ha0 ha.symm
  have hi : A⁻¹.denom.eval w ≠ 0 := by
    intro h
    have hn := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_inv_dvd hA0) h
    apply ha0
    rw [← ha.2,RatFunc.eval,Polynomial.eval₂_id,hn,zero_div]
  refine ⟨hi,?_⟩
  have he := RatFunc.eval_mul (RingHom.id ℂ) w ha.1 hi
  rw [mul_inv_cancel₀ hA0,RatFunc.eval_one,ha.2] at he
  exact eq_inv_of_mul_eq_one_right he.symm
private lemma numeric_pow {w a : ℂ} {A : RatFunc ℂ}
    (ha : Numeric w A a) (n : ℕ) : Numeric w (A^n) (a^n) := by
  induction n with
  | zero => simpa using numeric_const w 1
  | succ n hn => simpa [pow_succ] using numeric_mul hn ha
private lemma numeric_zpow {w a : ℂ} {A : RatFunc ℂ}
    (ha : Numeric w A a) (ha0 : a ≠ 0) (n : ℤ) : Numeric w (A^n) (a^n) := by
  cases n with
  | ofNat n => simpa using numeric_pow ha n
  | negSucc n => simpa [zpow_negSucc,← inv_pow] using numeric_pow (numeric_inv ha ha0) (n+1)

private theorem actual_rational_coefficient_numeric
    (α w : ℂ) (r₀ : ℂˣ) (hr₀ : (r₀ : ℂ) = α*w)
    (ε : Sign) (hd : denominator (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀) ≠ 0)
    (n : ℤ) :
    Numeric w
      ((rationalDenominator (KPExceptionalRaw.LocalField F q) ε (RatFunc.C α*RatFunc.X))⁻¹ *
        (if ε = .plus then RatFunc.C α*RatFunc.X else (RatFunc.C α*RatFunc.X)⁻¹)^n)
      ((denominator (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀))⁻¹ *
        (evaluationUnit (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀) : ℂ)^n) := by
  have hv : Numeric w (RatFunc.C α*RatFunc.X) (r₀ : ℂ) := by
    rw [hr₀]; exact numeric_mul (numeric_const w α) (numeric_X w)
  have hi := numeric_inv hv r₀.ne_zero
  have hroot := root_parameter_additiveParameter F q r₀
  have hdv : Numeric w (rationalDenominator (KPExceptionalRaw.LocalField F q) ε (RatFunc.C α*RatFunc.X))
      (denominator (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀)) := by
    cases ε
    · simpa only [KPRankOneGenericComposition.rationalDenominator,map_one,denominator,ite_true,KPRankOneRootParameter.t,hroot] using
        numeric_sub (numeric_const w 1)
          (numeric_mul (numeric_const w (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)⁻¹) (numeric_pow hv 6))
    · simpa only [KPRankOneGenericComposition.rationalDenominator,map_one,denominator,show Sign.minus ≠ Sign.plus from by decide,ite_false,hroot] using
        numeric_sub (numeric_const w 1)
          (numeric_mul (numeric_const w (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)) (numeric_pow hi 6))
  apply numeric_mul (numeric_inv hdv hd)
  have hunit : (evaluationUnit (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀) : ℂ) =
      if ε = .plus then (r₀ : ℂ) else (r₀ : ℂ)⁻¹ := by
    cases ε <;> simp [evaluationUnit,rUnit,hroot]
  rw [hunit]
  cases ε
  · simpa using numeric_zpow hv r₀.ne_zero n
  · simpa using numeric_zpow hi (inv_ne_zero r₀.ne_zero) n

private theorem both_standard_denominators_regular
    (α w : ℂ) (hα : α^6=(residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ))
    (hw0 : w ≠ 0) (hw6 : w^6 ≠ 1) :
    ∃ r₀ : ℂˣ, (r₀ : ℂ)=α*w ∧
      denominator (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀) ≠ 0 ∧
      denominator (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀) ≠ 0 := by
  have hq0 : (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (KPExceptionalRaw.LocalField F q))))).ne'
  have hα0 : α ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide)] at hα
    exact hq0 hα.symm
  let r₀ := Units.mk0 (α*w) (mul_ne_zero hα0 hw0)
  have hroot := root_parameter_additiveParameter F q r₀
  have h6 : (r₀ : ℂ)^6 = (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)*w^6 := by
    change (α*w)^6 = _
    rw [mul_pow,hα]
  have h6ne : (r₀ : ℂ)^6 ≠ (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) := by
    rw [h6]
    intro he
    exact hw6 ((mul_left_cancel₀ hq0) (by simpa using he))
  refine ⟨r₀,rfl,?_,?_⟩
  · simp only [denominator,ite_true, KPRankOneRootParameter.t,hroot]
    apply sub_ne_zero.mpr
    intro he
    apply h6ne
    exact ((inv_mul_eq_one₀ hq0).mp he.symm).symm
  · simp only [denominator,show Sign.minus ≠ Sign.plus from by decide,ite_false,hroot]
    apply sub_ne_zero.mpr
    intro he
    apply h6ne
    have he' : (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)*((r₀ : ℂ)^6)⁻¹ = 1 := by
      simpa only [inv_pow] using he.symm
    exact ((mul_inv_eq_one₀ (pow_ne_zero _ r₀.ne_zero)).mp he').symm

private theorem scalar_regular_locus_infinite
    (C : RatFunc ℂ) :
    {w : ℂ | w ≠ 0 ∧ w^6 ≠ 1 ∧ C.denom.eval w ≠ 0}.Infinite := by
  let bad : Set ℂ := {0} ∪ {w | w^6=1} ∪ {w | C.denom.IsRoot w}
  have hp : (Polynomial.X^6-1 : Polynomial ℂ) ≠ 0 := by
    intro he
    have hv := congrArg (Polynomial.eval (0 : ℂ)) he
    norm_num at hv
  have hroots : {w : ℂ | w^6=1}.Finite := by
    convert Polynomial.finite_setOfPred_isRoot hp using 1
    ext w
    simp [Polynomial.IsRoot,sub_eq_zero]
  have hb : bad.Finite := ((Set.finite_singleton 0).union hroots).union
    (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero C))
  have hi := Set.infinite_univ.sdiff hb
  apply hi.mono
  intro w hw
  rcases hw with ⟨_,hw⟩
  exact ⟨fun h => hw (Or.inl (Or.inl h)),
    fun h => hw (Or.inl (Or.inr h)),fun h => hw (Or.inr h)⟩

set_option maxHeartbeats 8000000 in
set_option backward.isDefEq.respectTransparency false in

theorem rational_composition_of_regular_values
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (α : ℂ) (hα : α ^ 6 = (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ))
    (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q))
    (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus)
    (pRev : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus)
    (C : RatFunc ℂ) (ε : Sign)
    (hn : ∀ w : ℂ, w ≠ 0 → w ^ 6 ≠ 1 → C.denom.eval w ≠ 0 →
      ∀ r₀ : ℂˣ, (r₀ : ℂ) = α * w →
      if ε = .plus then
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
          (additiveParameter F q r₀)).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
            (additiveParameter F q r₀)) =
          RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id
      else
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
          (additiveParameter F q r₀)).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
            (additiveParameter F q r₀)) =
          RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id) :
    if ε = .plus then
      (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
        (RatFunc.C α * RatFunc.X)).comp
        (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
          (RatFunc.C α * RatFunc.X)) = C • LinearMap.id
    else
      (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
        (RatFunc.C α * RatFunc.X)).comp
        (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
          (RatFunc.C α * RatFunc.X)) = C • LinearMap.id := by
  classical
  let v : RatFunc ℂ := RatFunc.C α*RatFunc.X
  let a : ℤ → RatFunc ℂ := fun n =>
    (rationalDenominator (KPExceptionalRaw.LocalField F q) .plus v)⁻¹ * v^n
  let b : ℤ → RatFunc ℂ := fun n =>
    (rationalDenominator (KPExceptionalRaw.LocalField F q) .minus v)⁻¹ * v⁻¹^n
  let U : Set ℂ := {w | w ≠ 0 ∧ w^6 ≠ 1 ∧ C.denom.eval w ≠ 0}
  have hU : U.Infinite := scalar_regular_locus_infinite C
  have hr (w : ℂ) (hw : w ∈ U) := both_standard_denominators_regular F q α w hα hw.1 hw.2.1
  have ha : ∀ w ∈ U, ∀ n ∈ p.support, (a n).denom.eval w ≠ 0 := by
    intro w hw n _
    obtain ⟨r₀,he,hp,hm⟩ := hr w hw
    exact (actual_rational_coefficient_numeric F q α w r₀ he .plus hp n).1
  have hb : ∀ w ∈ U, ∀ n ∈ pRev.support, (b n).denom.eval w ≠ 0 := by
    intro w hw n _
    obtain ⟨r₀,he,hp,hm⟩ := hr w hw
    exact (actual_rational_coefficient_numeric F q α w r₀ he .minus hm n).1
  cases ε with
  | plus =>
    have hn' : ∀ w : ℂ, w ≠ 0 → w^6 ≠ 1 → C.denom.eval w ≠ 0 →
        ∀ r₀ : ℂˣ, (r₀ : ℂ) = α*w →
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
          (additiveParameter F q r₀)).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
            (additiveParameter F q r₀)) =
          RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id := by
      intro w hw hw6 hC r₀ hr₀
      simpa only [ite_true] using hn w hw hw6 hC r₀ hr₀
    have hspec : ∀ w ∈ U,
        (∑ j ∈ pRev.support, RatFunc.eval (RingHom.id ℂ) w (b j) • pRev j).comp
          (∑ i ∈ p.support, RatFunc.eval (RingHom.id ℂ) w (a i) • p i) =
        RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id := by
      intro w hw
      obtain ⟨r₀,he,hp,hm⟩ := hr w hw
      have ea (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (a n) =
          (denominator (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀))⁻¹ *
            (evaluationUnit (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀) : ℂ)^n :=
        (actual_rational_coefficient_numeric F q α w r₀ he .plus hp n).2
      have eb (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (b n) =
          (denominator (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀))⁻¹ *
            (evaluationUnit (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀) : ℂ)^n :=
        (actual_rational_coefficient_numeric F q α w r₀ he .minus hm n).2
      have ep : (∑ n ∈ p.support, RatFunc.eval (RingHom.id ℂ) w (a n) • p n) =
          continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
            (additiveParameter F q r₀) := by
        simp only [ea,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
      have em : (∑ n ∈ pRev.support, RatFunc.eval (RingHom.id ℂ) w (b n) • pRev n) =
          continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
            (additiveParameter F q r₀) := by
        simp only [eb,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
      rw [ep,em]
      exact hn' w hw.1 hw.2.1 hw.2.2 r₀ he
    have hh := rational_rectangular_composition p.support pRev.support a b p pRev
      C U hU ha hb (fun _ hw => hw.2.2) hspec
    simp only [ite_true]
    simpa only [rationalStandard,Finsupp.sum,Finset.smul_sum,smul_smul,
      ite_true,ite_eq_right (show Sign.minus ≠ Sign.plus from by decide)] using hh
  | minus =>
    have hn' : ∀ w : ℂ, w ≠ 0 → w^6 ≠ 1 → C.denom.eval w ≠ 0 →
        ∀ r₀ : ℂˣ, (r₀ : ℂ) = α*w →
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
          (additiveParameter F q r₀)).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
            (additiveParameter F q r₀)) =
          RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id := by
      intro w hw hw6 hC r₀ hr₀
      simpa only [show Sign.minus ≠ Sign.plus from by decide, ite_false] using hn w hw hw6 hC r₀ hr₀
    have hspec : ∀ w ∈ U,
        (∑ j ∈ p.support, RatFunc.eval (RingHom.id ℂ) w (a j) • p j).comp
          (∑ i ∈ pRev.support, RatFunc.eval (RingHom.id ℂ) w (b i) • pRev i) =
        RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id := by
      intro w hw
      obtain ⟨r₀,he,hp,hm⟩ := hr w hw
      have ea (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (a n) =
          (denominator (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀))⁻¹ *
            (evaluationUnit (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀) : ℂ)^n :=
        (actual_rational_coefficient_numeric F q α w r₀ he .plus hp n).2
      have eb (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (b n) =
          (denominator (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀))⁻¹ *
            (evaluationUnit (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀) : ℂ)^n :=
        (actual_rational_coefficient_numeric F q α w r₀ he .minus hm n).2
      have ep : (∑ n ∈ p.support, RatFunc.eval (RingHom.id ℂ) w (a n) • p n) =
          continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
            (additiveParameter F q r₀) := by
        simp only [ea,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
      have em : (∑ n ∈ pRev.support, RatFunc.eval (RingHom.id ℂ) w (b n) • pRev n) =
          continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
            (additiveParameter F q r₀) := by
        simp only [eb,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
      rw [ep,em]
      exact hn' w hw.1 hw.2.1 hw.2.2 r₀ he
    have hh := rational_rectangular_composition pRev.support p.support b a pRev p
      C U hU hb ha (fun _ hw => hw.2.2) hspec
    simp only [show Sign.minus ≠ Sign.plus from by decide, ite_false]
    simpa only [rationalStandard,Finsupp.sum,Finset.smul_sum,smul_smul,
      ite_true,ite_eq_right (show Sign.minus ≠ Sign.plus from by decide)] using hh

end
end DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse
