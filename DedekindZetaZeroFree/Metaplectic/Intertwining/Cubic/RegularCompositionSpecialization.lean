module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ArithmeticInducingData

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPActualResidueSources

open KPActualScalarBinding KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter KPRankOneGeneric

noncomputable section

open scoped TensorProduct

 def Regular (a : ℂ) (f : RatFunc ℂ) : Prop := Polynomial.eval a f.denom ≠ 0
 lemma regular_zero (a : ℂ) : Regular a 0 := by simp [Regular]
private lemma regular_one (a : ℂ) : Regular a 1 := by simp [Regular]
 lemma regular_C (a c : ℂ) : Regular a (RatFunc.C c) := by simp [Regular]
private lemma regular_X (a : ℂ) : Regular a RatFunc.X := by simp [Regular]
 lemma regular_add {a : ℂ} {f g : RatFunc ℂ} (hf : Regular a f) (hg : Regular a g) :
    Regular a (f + g) := by
  intro h
  have H := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) a
    (RatFunc.denom_add_dvd f g) (by simpa using h)
  simp [Polynomial.eval₂_mul, Polynomial.eval₂_id, mul_ne_zero hf hg] at H
 lemma regular_mul {a : ℂ} {f g : RatFunc ℂ} (hf : Regular a f) (hg : Regular a g) :
    Regular a (f * g) := by
  intro h
  have H := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) a
    (RatFunc.denom_mul_dvd f g) (by simpa using h)
  simp [Polynomial.eval₂_mul, Polynomial.eval₂_id, mul_ne_zero hf hg] at H
private lemma regular_inv {a : ℂ} {f : RatFunc ℂ} (_hf : Regular a f)
    (hne : RatFunc.eval (RingHom.id ℂ) a f ≠ 0) : Regular a f⁻¹ := by
  have hf0 : f ≠ 0 := by intro h; simp [h] at hne
  intro h
  have H := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) a
    (RatFunc.denom_inv_dvd hf0) (by simpa using h)
  apply hne
  simp [RatFunc.eval, H]
 lemma eval_mul' {a : ℂ} {f g : RatFunc ℂ} (hf : Regular a f) (hg : Regular a g) :
    RatFunc.eval (RingHom.id ℂ) a (f * g) =
      RatFunc.eval (RingHom.id ℂ) a f * RatFunc.eval (RingHom.id ℂ) a g := by
  apply RatFunc.eval_mul <;> simpa [Regular, Polynomial.eval₂_id] using ‹Regular a _›
private lemma eval_inv' {a : ℂ} {f : RatFunc ℂ} (hf : Regular a f)
    (hne : RatFunc.eval (RingHom.id ℂ) a f ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) a f⁻¹ = (RatFunc.eval (RingHom.id ℂ) a f)⁻¹ := by
  have hf0 : f ≠ 0 := by intro h; simp [h] at hne
  apply (mul_left_cancel₀ hne)
  rw [← eval_mul' hf (regular_inv hf hne), mul_inv_cancel₀ hf0, RatFunc.eval_one,
    mul_inv_cancel₀ hne]
 def regularSpace (a : ℂ) : Submodule ℂ (RatFunc ℂ) where
  carrier := Regular a
  zero_mem' := regular_zero a
  add_mem' := regular_add
  smul_mem' c f hf := by
    change Regular a (c • f)
    rw [RatFunc.smul_eq_C_mul]
    exact regular_mul (regular_C a c) hf
 def regularEval (a : ℂ) : regularSpace a →ₗ[ℂ] ℂ where
  toFun f := RatFunc.eval (RingHom.id ℂ) a f
  map_add' f g := by
    exact RatFunc.eval_add (RingHom.id ℂ) a f.property g.property
  map_smul' c f := by
    change RatFunc.eval (RingHom.id ℂ) a (c • f.val) = _
    rw [RatFunc.smul_eq_C_mul]
    rw [eval_mul' (regular_C a c) f.property, RatFunc.eval_C]
    rfl

private lemma exists_eval_linear (a : ℂ) : ∃ E : RatFunc ℂ →ₗ[ℂ] ℂ,
    ∀ f, Regular a f → E f = RatFunc.eval (RingHom.id ℂ) a f := by
  obtain ⟨E, hE⟩ := (regularEval a).exists_extend
  exact ⟨E, fun f hf => congrArg (fun L => L ⟨f, hf⟩) hE⟩
private lemma regular_neg {a : ℂ} {f : RatFunc ℂ} (hf : Regular a f) : Regular a (-f) := by
  simpa using regular_mul (regular_C a (-1)) hf
private lemma eval_neg' {a : ℂ} {f : RatFunc ℂ} (hf : Regular a f) :
    RatFunc.eval (RingHom.id ℂ) a (-f) = -RatFunc.eval (RingHom.id ℂ) a f := by
  have H := eval_mul' (regular_C a (-1)) hf
  rw [RatFunc.eval_C] at H
  simpa using H
private lemma regular_pow {a : ℂ} {f : RatFunc ℂ} (hf : Regular a f) (n : ℕ) :
    Regular a (f ^ n) := by
  induction n with
  | zero => simpa using regular_one a
  | succ n hn => simpa [pow_succ] using regular_mul hn hf
private lemma eval_pow' {a : ℂ} {f : RatFunc ℂ} (hf : Regular a f) (n : ℕ) :
    RatFunc.eval (RingHom.id ℂ) a (f ^ n) = RatFunc.eval (RingHom.id ℂ) a f ^ n := by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, eval_mul' (regular_pow hf n) hf, hn, pow_succ]
private lemma regular_zpow {a : ℂ} {f : RatFunc ℂ} (hf : Regular a f)
    (hne : RatFunc.eval (RingHom.id ℂ) a f ≠ 0) (n : ℤ) : Regular a (f ^ n) := by
  cases n with
  | ofNat n => simpa using regular_pow hf n
  | negSucc n => simpa [zpow_negSucc, ← inv_pow] using regular_pow (regular_inv hf hne) (n + 1)
private lemma eval_zpow' {a : ℂ} {f : RatFunc ℂ} (hf : Regular a f)
    (hne : RatFunc.eval (RingHom.id ℂ) a f ≠ 0) (n : ℤ) :
    RatFunc.eval (RingHom.id ℂ) a (f ^ n) = RatFunc.eval (RingHom.id ℂ) a f ^ n := by
  cases n with
  | ofNat n => simpa using eval_pow' hf n
  | negSucc n =>
      simpa [zpow_negSucc, ← inv_pow, eval_inv' hf hne] using
        (eval_pow' (regular_inv hf hne) (n + 1))

private lemma specialize_scalar {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W]
    (p : ℤ →₀ (V →ₗ[ℂ] W)) (q : ℤ →₀ (W →ₗ[ℂ] V))
    (a b : ℤ → RatFunc ℂ) (c : RatFunc ℂ) (z : ℂ)
    (ha : ∀ n, Regular z (a n)) (hb : ∀ n, Regular z (b n)) (hc : Regular z c)
    (h : (q.sum fun n M => b n • M.baseChange (RatFunc ℂ)).comp
      (p.sum fun n M => a n • M.baseChange (RatFunc ℂ)) = c • LinearMap.id) :
    (q.sum fun n M => RatFunc.eval (RingHom.id ℂ) z (b n) • M).comp
      (p.sum fun n M => RatFunc.eval (RingHom.id ℂ) z (a n) • M) =
      RatFunc.eval (RingHom.id ℂ) z c • LinearMap.id := by
  obtain ⟨E, hE⟩ := exists_eval_linear z
  let L : RatFunc ℂ ⊗[ℂ] V →ₗ[ℂ] V :=
    (TensorProduct.lid ℂ V).toLinearMap.comp (TensorProduct.map E LinearMap.id)
  have hL (f : RatFunc ℂ) (v : V) : L (f ⊗ₜ[ℂ] v) = E f • v := by simp [L]
  ext v
  have H := congrArg (fun M => L (M ((1 : RatFunc ℂ) ⊗ₜ[ℂ] v))) h
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Finsupp.sum, LinearMap.sum_apply, map_sum, LinearMap.baseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one] at H
  simp only [hL] at H
  simp_rw [hE _ (regular_mul (hb _) (ha _)), eval_mul' (hb _) (ha _)] at H
  rw [hE c hc] at H
  simpa only [LinearMap.comp_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul, mul_comm] using H

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

private lemma denominator_regular_eval
    (α s w : ℂ) (hroot : α * w = r (KPExceptionalRaw.LocalField F q) s)
    (ε : Sign) :
    Regular w (rationalDenominator (KPExceptionalRaw.LocalField F q) ε
      (RatFunc.C α * RatFunc.X)) ∧
    RatFunc.eval (RingHom.id ℂ) w
      (rationalDenominator (KPExceptionalRaw.LocalField F q) ε
        (RatFunc.C α * RatFunc.X)) =
      denominator (KPExceptionalRaw.LocalField F q) ε s := by
  let K := KPExceptionalRaw.LocalField F q
  let v : RatFunc ℂ := RatFunc.C α * RatFunc.X
  have hv : Regular w v := regular_mul (regular_C w α) (regular_X w)
  have he : RatFunc.eval (RingHom.id ℂ) w v = r K s := by
    rw [eval_mul' (regular_C w α) (regular_X w), RatFunc.eval_C, RatFunc.eval_X]
    exact hroot
  have hx : RatFunc.eval (RingHom.id ℂ) w v ≠ 0 := by
    rw [he]
    exact Complex.exp_ne_zero _
  have hinv := regular_inv hv hx
  have epow := eval_pow' hv 6
  have einvpow := eval_pow' hinv 6
  cases ε <;> unfold rationalDenominator denominator
  · simp only [ite_true]
    have hr := regular_mul (regular_C w (residueCardinality K : ℂ)⁻¹)
      (regular_pow hv 6)
    refine ⟨by simpa only [sub_eq_add_neg] using regular_add (regular_one _) (regular_neg hr), ?_⟩
    rw [sub_eq_add_neg, RatFunc.eval_add (RingHom.id ℂ) w
      (regular_one _) (regular_neg hr), eval_neg' hr,
      eval_mul' (regular_C _ _) (regular_pow hv 6), epow, he]
    simp only [RatFunc.eval_C, RatFunc.eval_one, RingHom.id_apply,
      t, sub_eq_add_neg]
    rfl
  · simp only [show Sign.minus ≠ Sign.plus from by decide, ite_false]
    have hr := regular_mul (regular_C w (residueCardinality K : ℂ))
      (regular_pow hinv 6)
    refine ⟨by simpa only [sub_eq_add_neg] using regular_add (regular_one _) (regular_neg hr), ?_⟩
    rw [sub_eq_add_neg, RatFunc.eval_add (RingHom.id ℂ) w
      (regular_one _) (regular_neg hr), eval_neg' hr,
      eval_mul' (regular_C _ _) (regular_pow hinv 6), einvpow,
      eval_inv' hv hx, he]
    simp only [RatFunc.eval_C, RatFunc.eval_one, RingHom.id_apply, sub_eq_add_neg]
    rfl

private lemma coefficient_regular_eval
    (α s w : ℂ) (hroot : α * w = r (KPExceptionalRaw.LocalField F q) s)
    (ε : Sign) (hd : denominator (KPExceptionalRaw.LocalField F q) ε s ≠ 0)
    (n : ℤ) :
    Regular w
      ((rationalDenominator (KPExceptionalRaw.LocalField F q) ε
          (RatFunc.C α * RatFunc.X))⁻¹ *
        (if ε = .plus then RatFunc.C α * RatFunc.X
          else (RatFunc.C α * RatFunc.X)⁻¹) ^ n) ∧
    RatFunc.eval (RingHom.id ℂ) w
      ((rationalDenominator (KPExceptionalRaw.LocalField F q) ε
          (RatFunc.C α * RatFunc.X))⁻¹ *
        (if ε = .plus then RatFunc.C α * RatFunc.X
          else (RatFunc.C α * RatFunc.X)⁻¹) ^ n) =
      (denominator (KPExceptionalRaw.LocalField F q) ε s)⁻¹ *
        (evaluationUnit (KPExceptionalRaw.LocalField F q) ε s : ℂ) ^ n := by
  let K := KPExceptionalRaw.LocalField F q
  let v : RatFunc ℂ := RatFunc.C α * RatFunc.X
  have hv : Regular w v := regular_mul (regular_C w α) (regular_X w)
  have he : RatFunc.eval (RingHom.id ℂ) w v = r K s := by
    rw [eval_mul' (regular_C w α) (regular_X w), RatFunc.eval_C, RatFunc.eval_X]
    exact hroot
  have hx : RatFunc.eval (RingHom.id ℂ) w v ≠ 0 := by
    rw [he]
    exact Complex.exp_ne_zero _
  have hde := denominator_regular_eval F q α s w hroot ε
  have hdn : RatFunc.eval (RingHom.id ℂ) w
      (rationalDenominator K ε v) ≠ 0 := hde.2 ▸ hd
  have hf : Regular w (if ε = .plus then v else v⁻¹) := by
    split_ifs <;> first | exact hv | exact regular_inv hv hx
  have hfe : RatFunc.eval (RingHom.id ℂ) w (if ε = .plus then v else v⁻¹) =
      (evaluationUnit K ε s : ℂ) := by
    cases ε <;> simp [evaluationUnit, rUnit, eval_inv' hv hx, he] <;> rfl
  have hfn : RatFunc.eval (RingHom.id ℂ) w (if ε = .plus then v else v⁻¹) ≠ 0 := by
    rw [hfe]
    exact Units.ne_zero _
  refine ⟨regular_mul (regular_inv hde.1 hdn) (regular_zpow hf hfn n), ?_⟩
  rw [eval_mul' (regular_inv hde.1 hdn) (regular_zpow hf hfn n),
    eval_inv' hde.1 hdn, eval_zpow' hf hfn n, hde.2, hfe]

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in

theorem actual_level_composition_specialize_regular
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (KPExceptionalRaw.ActualCover F ζ hζ q)) ≤
      S.iwasawa.compact.toOpenSubgroup)
    (α : ℂ)
    (hα : α ^ 6 = (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ))
    (pplus : LevelLaurentOperator (KPExceptionalRaw.LocalField F q)
      S.borel P S.iwasawa J .plus)
    (pminus : LevelLaurentOperator (KPExceptionalRaw.LocalField F q)
      S.borel P S.iwasawa J .minus)
    (C : RatFunc ℂ) (ε : Sign) (s w : ℂ)
    (hw : w ≠ 0) (hroot : α * w = r (KPExceptionalRaw.LocalField F q) s)
    (hdplus : denominator (KPExceptionalRaw.LocalField F q) .plus s ≠ 0)
    (hdminus : denominator (KPExceptionalRaw.LocalField F q) .minus s ≠ 0)
    (hC : C.denom.eval w ≠ 0)
    (hcomp :
      if ε = .plus then
        (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J
            .minus pminus (RatFunc.C α * RatFunc.X)).comp
          (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J
            .plus pplus (RatFunc.C α * RatFunc.X)) = C • LinearMap.id
      else
        (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J
            .plus pplus (RatFunc.C α * RatFunc.X)).comp
          (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J
            .minus pminus (RatFunc.C α * RatFunc.X)) = C • LinearMap.id) :
    if ε = .plus then
      (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J
          .minus pminus s).comp
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J
          .plus pplus s) = RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id
    else
      (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J
          .plus pplus s).comp
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J
          .minus pminus s) = RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id := by
  cases ε
  · simp only [ite_true] at hcomp ⊢
    have h := hcomp
    dsimp only [LevelLaurentOperator, sourceSign, targetSign, id_eq] at pplus pminus
    dsimp only [rationalLevel, sourceSign, targetSign, id_eq] at h
    let K := KPExceptionalRaw.LocalField F q
    let v : RatFunc ℂ := RatFunc.C α * RatFunc.X
    let a : ℤ → RatFunc ℂ := fun n => (rationalDenominator K .plus v)⁻¹ * v ^ n
    let b : ℤ → RatFunc ℂ := fun n => (rationalDenominator K .minus v)⁻¹ * v⁻¹ ^ n
    have ha (n : ℤ) : Regular w (a n) :=
      (coefficient_regular_eval F q α s w hroot .plus hdplus n).1
    have hb (n : ℤ) : Regular w (b n) :=
      (coefficient_regular_eval F q α s w hroot .minus hdminus n).1
    have H := @specialize_scalar
      (compactLevel S.borel P S.iwasawa .plus J)
      (compactLevel S.borel P S.iwasawa .minus J)
      inferInstance inferInstance inferInstance inferInstance
      pplus pminus a b C w ha hb hC ?_
    · dsimp only [continuedLevel, sourceSign, targetSign, id_eq, evaluate] at ⊢
      have ea (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (a n) =
          (denominator K .plus s)⁻¹ * (evaluationUnit K .plus s : ℂ) ^ n :=
          (coefficient_regular_eval F q α s w hroot .plus hdplus n).2
      have eb (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (b n) =
          (denominator K .minus s)⁻¹ * (evaluationUnit K .minus s : ℂ) ^ n :=
          (coefficient_regular_eval F q α s w hroot .minus hdminus n).2
      apply LinearMap.ext
      intro x
      have Hx := congrArg (fun M => M x) H
      simpa only [ea, eb, Finsupp.sum, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.sum_apply, map_sum, map_smul, Finset.smul_sum, smul_smul] using Hx
    · simp only [rationalStandard, Finsupp.sum, Finset.smul_sum,
        smul_smul, ite_true, ite_eq_right (show Sign.minus ≠ Sign.plus from by decide)] at h
      change _ = _ at h
      convert h using 1
      simp only [Finsupp.sum, a, b]
      rfl
  · simp only [show Sign.minus ≠ Sign.plus from by decide, ite_false] at hcomp ⊢
    have h := hcomp
    dsimp only [LevelLaurentOperator, sourceSign, targetSign, id_eq] at pplus pminus
    dsimp only [rationalLevel, sourceSign, targetSign, id_eq] at h
    let K := KPExceptionalRaw.LocalField F q
    let v : RatFunc ℂ := RatFunc.C α * RatFunc.X
    let a : ℤ → RatFunc ℂ := fun n => (rationalDenominator K .plus v)⁻¹ * v ^ n
    let b : ℤ → RatFunc ℂ := fun n => (rationalDenominator K .minus v)⁻¹ * v⁻¹ ^ n
    have ha (n : ℤ) : Regular w (a n) :=
      (coefficient_regular_eval F q α s w hroot .plus hdplus n).1
    have hb (n : ℤ) : Regular w (b n) :=
      (coefficient_regular_eval F q α s w hroot .minus hdminus n).1
    have H := @specialize_scalar
      (compactLevel S.borel P S.iwasawa .minus J)
      (compactLevel S.borel P S.iwasawa .plus J)
      inferInstance inferInstance inferInstance inferInstance
      pminus pplus b a C w hb ha hC ?_
    · dsimp only [continuedLevel, sourceSign, targetSign, id_eq, evaluate] at ⊢
      have ea (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (a n) =
          (denominator K .plus s)⁻¹ * (evaluationUnit K .plus s : ℂ) ^ n :=
          (coefficient_regular_eval F q α s w hroot .plus hdplus n).2
      have eb (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (b n) =
          (denominator K .minus s)⁻¹ * (evaluationUnit K .minus s : ℂ) ^ n :=
          (coefficient_regular_eval F q α s w hroot .minus hdminus n).2
      apply LinearMap.ext
      intro x
      have Hx := congrArg (fun M => M x) H
      simpa only [ea, eb, Finsupp.sum, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.sum_apply, map_sum, map_smul, Finset.smul_sum, smul_smul] using Hx
    · simp only [rationalStandard, Finsupp.sum, Finset.smul_sum,
        smul_smul, ite_true, ite_eq_right (show Sign.minus ≠ Sign.plus from by decide)] at h
      change _ = _ at h
      convert h using 1
      simp only [Finsupp.sum, a, b]
      rfl

end
end DedekindZetaZeroFree.KPActualResidueSources
