module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CubicBetaAndMellinEvaluation
public import DedekindZetaZeroFree.Theta.Profiles.ShiftedCubicBetaIntegrability

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open scoped NumberField
set_option autoImplicit false
open scoped Classical
variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance : IsNonarchimedeanLocalField (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
local instance : MeasurableSpace (q.adicCompletion F) := borel (q.adicCompletion F)
local instance : BorelSpace (q.adicCompletion F) := ⟨rfl⟩

namespace ShiftedBetaAlgebra
open scoped Classical
 def Regular {F : Type*} [Field F] (u : F) (r : RatFunc F) : Prop :=
  r.denom.eval u ≠ 0

private lemma regular_C {F : Type*} [Field F] (u c : F) : Regular u (RatFunc.C c) := by
  simp [Regular]
private lemma regular_X {F : Type*} [Field F] (u : F) : Regular u (RatFunc.X : RatFunc F) := by
  simp [Regular]
private lemma regular_add {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : Regular u r) (hs : Regular u s) : Regular u (r+s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd r s) h)
private lemma regular_mul {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : Regular u r) (hs : Regular u s) : Regular u (r*s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd r s) h)
private lemma regular_inv {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (_hr : Regular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) : Regular u r⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  intro h
  have hn := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_inv_dvd hr0) h
  apply hv
  simp [RatFunc.eval, hn]
private lemma eval_inv {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (hr : Regular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) :
    RatFunc.eval (RingHom.id F) u r⁻¹ = (RatFunc.eval (RingHom.id F) u r)⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  have hm := RatFunc.eval_mul (f := RingHom.id F) (a := u) hr (regular_inv hr hv)
  rw [mul_inv_cancel₀ hr0, RatFunc.eval_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

 def Evaluates {F : Type*} [Field F] (u : F) (r : RatFunc F) (v : F) : Prop :=
  Regular u r ∧ RatFunc.eval (RingHom.id F) u r = v
private lemma Evaluates.const {F : Type*} [Field F] (u v : F) : Evaluates u (RatFunc.C v) v :=
  ⟨regular_C u v, by simp⟩
private lemma Evaluates.var {F : Type*} [Field F] (u : F) : Evaluates u RatFunc.X u :=
  ⟨regular_X u, by simp⟩
private lemma Evaluates.add {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r+s) (a+b) := by
  refine ⟨regular_add hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_add (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma Evaluates.mul {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r*s) (a*b) := by
  refine ⟨regular_mul hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_mul (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma Evaluates.neg {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) : Evaluates u (-r) (-a) := by
  simpa only [map_neg, map_one, neg_one_mul] using (Evaluates.const u (-1)).mul hr
private lemma Evaluates.sub {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r-s) (a-b) := by
  simpa only [sub_eq_add_neg] using hr.add hs.neg
private lemma Evaluates.inv {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) (ha : a ≠ 0) : Evaluates u r⁻¹ a⁻¹ := by
  have hv : RatFunc.eval (RingHom.id F) u r ≠ 0 := hr.2 ▸ ha
  exact ⟨regular_inv hr.1 hv, by rw [eval_inv hr.1 hv, hr.2]⟩
private lemma Evaluates.div {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) (hb : b ≠ 0) : Evaluates u (r/s) (a/b) := by
  simpa only [div_eq_mul_inv] using hr.mul (hs.inv hb)
private lemma Evaluates.pow {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) (n : ℕ) : Evaluates u (r^n) (a^n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using Evaluates.const u 1
  | succ n ih => simpa only [pow_succ] using ih.mul hr
private lemma Evaluates.zpow {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) (ha : a ≠ 0) (n : ℤ) : Evaluates u (r^n) (a^n) := by
  cases n with
  | ofNat n => simpa using hr.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hr.pow (n+1)).inv (pow_ne_zero _ ha)
private lemma Evaluates.sum {F I : Type*} [Field F] {u : F} (s : Finset I)
    {r : I → RatFunc F} {a : I → F} (h : ∀ i ∈ s, Evaluates u (r i) (a i)) :
    Evaluates u (∑ i ∈ s, r i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, map_zero] using Evaluates.const u 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

 def rationalR {E : Type*} [Field E] (a m b : E) (ram : Bool) (f : ℕ) : RatFunc E :=
  let A : RatFunc E := RatFunc.C a
  let B : RatFunc E := RatFunc.C b
  let Q : RatFunc E := RatFunc.X
  if ram then RatFunc.C m * A ^ f * Q ^ (1-(f : ℤ)) / (Q-A)
  else RatFunc.C m * (B-A) * (Q-A*B) / ((1-B)*(B-Q)*(Q-A))
private theorem rationalR_evaluates_one {E : Type*} [Field E] (a m b : E)
    (ha : a ≠ 1) (hb0 : b ≠ 0) (hb : b ≠ 1) (ram : Bool) (f : ℕ) :
    Evaluates (1 : E) (rationalR a m b ram f)
      (m / (1-a) * if ram then a^f else
        (1-a*b)*(1-a*b⁻¹)/((1-b)*(1-b⁻¹))) := by
  have hA := Evaluates.const (1 : E) a
  have hB := Evaluates.const (1 : E) b
  have hM := Evaluates.const (1 : E) m
  have hQ := Evaluates.var (1 : E)
  have h1 := Evaluates.const (1 : E) 1
  cases ram with
  | true =>
    have he := ((hM.mul (hA.pow f)).mul (hQ.zpow one_ne_zero (1-(f : ℤ)))).div
      (hQ.sub hA) (sub_ne_zero.mpr ha.symm)
    convert he using 1 <;> simp only [rationalR, ite_true, one_zpow, mul_one]
    ring
  | false =>
    have he := ((hM.mul (hB.sub hA)).mul (hQ.sub (hA.mul hB))).div
      (((h1.sub hB).mul (hB.sub hQ)).mul (hQ.sub hA))
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hb.symm) (sub_ne_zero.mpr hb)) (sub_ne_zero.mpr ha.symm))
    simp only [rationalR, Bool.false_eq_true, ite_false] at *
    convert he using 1 <;> try simp only [map_one]
    field_simp

private lemma Evaluates.ne_zero {E : Type*} [Field E] {u a : E} {r : RatFunc E}
    (hr : Evaluates u r a) (ha : a ≠ 0) : r ≠ 0 := by
  intro h
  exact ha (by simpa [h] using hr.2.symm)
 def Twice (z Q : ℂ) (r : RatFunc (RatFunc ℂ)) (a : ℂ) : Prop :=
  ∃ v : RatFunc ℂ, Evaluates (RatFunc.C Q) r v ∧ Evaluates z v a
private lemma Twice.const (z Q a : ℂ) : Twice z Q (RatFunc.C (RatFunc.C a)) a :=
  ⟨_, Evaluates.const _ _, Evaluates.const _ _⟩
private lemma Twice.parameter (z Q ε : ℂ) :
    Twice z Q (RatFunc.C (RatFunc.C ε*RatFunc.X)) (ε*z) :=
  ⟨_, Evaluates.const _ _, (Evaluates.const _ _).mul (Evaluates.var _)⟩
private lemma Twice.var (z Q : ℂ) : Twice z Q RatFunc.X Q :=
  ⟨_, Evaluates.var _, Evaluates.const _ _⟩
private lemma Twice.mul {z Q a b : ℂ} {r s : RatFunc (RatFunc ℂ)}
    (hr : Twice z Q r a) (hs : Twice z Q s b) : Twice z Q (r*s) (a*b) := by
  obtain ⟨v,hv,ev⟩ := hr
  obtain ⟨w,hw,ew⟩ := hs
  exact ⟨v*w,hv.mul hw,ev.mul ew⟩
private lemma Twice.add {z Q a b : ℂ} {r s : RatFunc (RatFunc ℂ)}
    (hr : Twice z Q r a) (hs : Twice z Q s b) : Twice z Q (r+s) (a+b) := by
  obtain ⟨v,hv,ev⟩ := hr
  obtain ⟨w,hw,ew⟩ := hs
  exact ⟨v+w,hv.add hw,ev.add ew⟩
private lemma Twice.sub {z Q a b : ℂ} {r s : RatFunc (RatFunc ℂ)}
    (hr : Twice z Q r a) (hs : Twice z Q s b) : Twice z Q (r-s) (a-b) := by
  obtain ⟨v,hv,ev⟩ := hr
  obtain ⟨w,hw,ew⟩ := hs
  exact ⟨v-w,hv.sub hw,ev.sub ew⟩
private lemma Twice.div {z Q a b : ℂ} {r s : RatFunc (RatFunc ℂ)}
    (hr : Twice z Q r a) (hs : Twice z Q s b) (hb : b ≠ 0) : Twice z Q (r/s) (a/b) := by
  obtain ⟨v,hv,ev⟩ := hr
  obtain ⟨w,hw,ew⟩ := hs
  exact ⟨v/w,hv.div hw (ew.ne_zero hb),ev.div ew hb⟩
private lemma Twice.pow {z Q a : ℂ} {r : RatFunc (RatFunc ℂ)}
    (hr : Twice z Q r a) (n : ℕ) : Twice z Q (r^n) (a^n) := by
  obtain ⟨v,hv,ev⟩ := hr
  exact ⟨v^n,hv.pow n,ev.pow n⟩
private lemma Twice.zpow {z Q a : ℂ} {r : RatFunc (RatFunc ℂ)}
    (hr : Twice z Q r a) (ha : a ≠ 0) (n : ℤ) : Twice z Q (r^n) (a^n) := by
  obtain ⟨v,hv,ev⟩ := hr
  exact ⟨v^n,hv.zpow (ev.ne_zero ha) n,ev.zpow ha n⟩
private lemma Twice.sum {z Q : ℂ} {I : Type*} (s : Finset I)
    {r : I → RatFunc (RatFunc ℂ)} {a : I → ℂ} (h : ∀ i ∈ s, Twice z Q (r i) (a i)) :
    Twice z Q (∑ i ∈ s,r i) (∑ i ∈ s,a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,map_zero] using Twice.const z Q 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
private lemma Twice.eval {z Q a : ℂ} {r : RatFunc (RatFunc ℂ)} (hr : Twice z Q r a) :
    RatFunc.eval (RingHom.id ℂ) z (RatFunc.eval (RingHom.id (RatFunc ℂ)) (RatFunc.C Q) r) = a := by
  obtain ⟨v,ev,hv⟩ := hr
  rw [ev.2]
  exact hv.2

section
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
 def characterR (m : ℂ) (ξ : CubicUnitCharacters.Character K)
    (ε : CubicCharacters.Mu3) : RatFunc (RatFunc ℂ) :=
  let a : RatFunc (RatFunc ℂ) := RatFunc.C (RatFunc.C (CubicUnitCharacters.residueCard K : ℂ)⁻¹)
  let b : RatFunc (RatFunc ℂ) := RatFunc.C (RatFunc.C ((ε : ℂˣ) : ℂ) * RatFunc.X)
  let Q : RatFunc (RatFunc ℂ) := RatFunc.X
  if ξ = 1 then RatFunc.C (RatFunc.C m) * (b-a) * (Q-a*b) / ((1-b)*(b-Q)*(Q-a))
  else RatFunc.C (RatFunc.C m) * a ^ CubicUnitCharacters.conductor K ξ * Q ^ (1-(CubicUnitCharacters.conductor K ξ : ℤ)) / (Q-a)
private theorem characterR_one (m : ℂ) (ξ : CubicUnitCharacters.Character K) (ε : CubicCharacters.Mu3) :
    Evaluates (1 : RatFunc ℂ) (characterR K m ξ ε)
      (RatFunc.C (m/(1-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)) *
        KPRankoneCubicScalarSum.betaFactor K ξ (RatFunc.C ((ε : ℂˣ) : ℂ) * RatFunc.X)) := by
  let a : ℂ := (CubicUnitCharacters.residueCard K : ℂ)⁻¹
  let b : RatFunc ℂ := RatFunc.C ((ε : ℂˣ) : ℂ) * RatFunc.X
  have ha : (RatFunc.C a : RatFunc ℂ) ≠ 1 := by
    intro h
    have hq : 2 ≤ CubicUnitCharacters.residueCard K := KPCubicUnitIndices.two_le_residueCard K
    have ha0 : a ≠ 1 := by
      intro e
      have en : (CubicUnitCharacters.residueCard K : ℂ) = 1 := inv_eq_one.mp e
      have hn : CubicUnitCharacters.residueCard K = 1 := by exact_mod_cast en
      omega
    apply ha0
    exact RatFunc.C_injective (by simpa only [map_one] using h)
  have hb0 : b ≠ 0 := mul_ne_zero (by simpa using Units.ne_zero (ε : ℂˣ)) RatFunc.X_ne_zero
  have hb : b ≠ 1 := by
    intro h
    have he := congrArg (RatFunc.eval (RingHom.id ℂ) 0) h
    have hC : Regular (0 : ℂ) (RatFunc.C ((ε : ℂˣ) : ℂ)) := regular_C _ _
    have hX : Regular (0 : ℂ) (RatFunc.X : RatFunc ℂ) := regular_X _
    simp only [b,RatFunc.eval_mul (RingHom.id ℂ) 0 hC hX,RatFunc.eval_C,RatFunc.eval_X,
      RingHom.id_apply,mul_zero,RatFunc.eval_one] at he
    exact zero_ne_one he
  by_cases hξ : ξ = 1
  · have he := rationalR_evaluates_one (RatFunc.C a) (RatFunc.C m) b ha hb0 hb false
      (CubicUnitCharacters.conductor K ξ)
    convert he using 1
    · simp only [characterR,hξ,ite_true,rationalR,ite_false]
      rfl
    · simp only [KPRankoneCubicScalarSum.betaFactor,hξ,ite_true,
        KPRankoneCubicScalarSum.unramifiedFactor, map_natCast,map_inv₀,map_div,map_sub,map_one]
      simp [a,b, map_div, map_sub, map_natCast, map_inv₀]
  · have he := rationalR_evaluates_one (RatFunc.C a) (RatFunc.C m) b ha hb0 hb true
      (CubicUnitCharacters.conductor K ξ)
    convert he using 1
    · simp only [characterR,hξ,ite_false,rationalR,ite_true]
      rfl
    · simp only [KPRankoneCubicScalarSum.betaFactor,hξ,ite_false,map_natCast,map_inv₀,
        map_div,map_sub,map_one]
      simp [a,b, map_div, map_sub, map_natCast, map_inv₀]
 def shiftedModel (m : ℂ) (j : ℤ) (u : (ValuativeRel.valuation K).integerˣ) : RatFunc (RatFunc ℂ) :=
  (RatFunc.X : RatFunc (RatFunc ℂ)) ^ (-j) * (1-RatFunc.X) / 3 *
    ∑ᶠ ξ : CubicUnitCharacters.Character K, ∑ᶠ ε : CubicCharacters.Mu3,
      RatFunc.C ((RatFunc.C ((ε : ℂˣ) : ℂ) * RatFunc.X)^j * RatFunc.C ((ξ u : ℂˣ) : ℂ)) * characterR K m ξ ε
private theorem shiftedModel_one [Finite (CubicUnitCharacters.Character K)]
    (m : ℂ) (j : ℤ) (u : (ValuativeRel.valuation K).integerˣ) :
    Evaluates (1 : RatFunc ℂ) (shiftedModel K m j u) 0 := by
  letI : Fintype (CubicUnitCharacters.Character K) := Fintype.ofFinite _
  letI : Fintype CubicCharacters.Mu3 := Fintype.ofFinite _
  have hsum := Evaluates.sum (u := (1 : RatFunc ℂ)) Finset.univ (fun (ξ : CubicUnitCharacters.Character K) _ =>
    Evaluates.sum Finset.univ (fun (ε : CubicCharacters.Mu3) _ =>
      (Evaluates.const (1 : RatFunc ℂ)
        ((RatFunc.C ((ε : ℂˣ) : ℂ) * RatFunc.X)^j * RatFunc.C ((ξ u : ℂˣ) : ℂ))).mul
        (characterR_one K m ξ ε)))
  have hfac := (((Evaluates.var (1 : RatFunc ℂ)).zpow one_ne_zero (-j)).mul
      ((Evaluates.const (1 : RatFunc ℂ) 1).sub (Evaluates.var (1 : RatFunc ℂ)))).div
        (Evaluates.const (1 : RatFunc ℂ) 3) (by norm_num)
  have he := hfac.mul hsum
  simpa only [shiftedModel,finsum_eq_sum_of_fintype,sub_self,mul_zero,zero_mul,zero_div,one_zpow,map_one,map_ofNat] using he

private theorem characterR_twice (m z Q : ℂ) (hQ : Q ≠ 0)
    (ξ : CubicUnitCharacters.Character K) (ε : CubicCharacters.Mu3)
    (hA : Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹ ≠ 0)
    (hb : 1-((ε : ℂˣ) : ℂ)*z ≠ 0) (hbQ : ((ε : ℂˣ) : ℂ)*z-Q ≠ 0) :
    Twice z Q (characterR K m ξ ε)
      (if ξ = 1 then m*(((ε : ℂˣ) : ℂ)*z-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)*
        (Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹*(((ε : ℂˣ) : ℂ)*z))/
        ((1-((ε : ℂˣ) : ℂ)*z)*(((ε : ℂˣ) : ℂ)*z-Q)*(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹))
       else m*((CubicUnitCharacters.residueCard K : ℂ)⁻¹)^CubicUnitCharacters.conductor K ξ*
         Q^(1-(CubicUnitCharacters.conductor K ξ : ℤ))/(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)) := by
  have hM := Twice.const z Q m
  have hC := Twice.const z Q (CubicUnitCharacters.residueCard K : ℂ)⁻¹
  have hB := Twice.parameter z Q ((ε : ℂˣ) : ℂ)
  have hX := Twice.var z Q
  have h1 := Twice.const z Q 1
  by_cases hξ : ξ = 1
  · have he := ((hM.mul (hB.sub hC)).mul (hX.sub (hC.mul hB))).div
      (((h1.sub hB).mul (hB.sub hX)).mul (hX.sub hC))
      (mul_ne_zero (mul_ne_zero hb hbQ) hA)
    simpa only [characterR,hξ,ite_true,map_one] using he
  · have he := ((hM.mul (hC.pow (CubicUnitCharacters.conductor K ξ))).mul
      (hX.zpow hQ (1-(CubicUnitCharacters.conductor K ξ : ℤ)))).div (hX.sub hC) hA
    simpa only [characterR,hξ,ite_false] using he
private theorem shiftedModel_twice [Finite (CubicUnitCharacters.Character K)]
    (m z Q : ℂ) (hz : z ≠ 0) (hQ : Q ≠ 0) (j : ℤ) (u : (valuation K).integerˣ)
    (hA : Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹ ≠ 0)
    (hb : ∀ ε : CubicCharacters.Mu3, 1-((ε : ℂˣ) : ℂ)*z ≠ 0)
    (hbQ : ∀ ε : CubicCharacters.Mu3, ((ε : ℂˣ) : ℂ)*z-Q ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (RatFunc.eval (RingHom.id (RatFunc ℂ)) (RatFunc.C Q)
      (shiftedModel K m j u)) =
      Q^(-j)*(1-Q)/3 * ∑ᶠ ξ : CubicUnitCharacters.Character K, ∑ᶠ ε : CubicCharacters.Mu3,
        ((((ε : ℂˣ) : ℂ)*z)^j*((ξ u : ℂˣ) : ℂ)) *
          (if ξ = 1 then m*(((ε : ℂˣ) : ℂ)*z-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)*
            (Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹*(((ε : ℂˣ) : ℂ)*z))/
            ((1-((ε : ℂˣ) : ℂ)*z)*(((ε : ℂˣ) : ℂ)*z-Q)*(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹))
           else m*((CubicUnitCharacters.residueCard K : ℂ)⁻¹)^CubicUnitCharacters.conductor K ξ*
             Q^(1-(CubicUnitCharacters.conductor K ξ : ℤ))/(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)) := by
  letI : Fintype (CubicUnitCharacters.Character K) := Fintype.ofFinite _
  letI : Fintype CubicCharacters.Mu3 := Fintype.ofFinite _
  have hc (ξ : CubicUnitCharacters.Character K) (ε : CubicCharacters.Mu3) :
      Twice z Q (RatFunc.C ((RatFunc.C ((ε : ℂˣ) : ℂ)*RatFunc.X)^j*RatFunc.C ((ξ u : ℂˣ) : ℂ)))
        ((((ε : ℂˣ) : ℂ)*z)^j*((ξ u : ℂˣ) : ℂ)) := by
    have he := ((Evaluates.const z ((ε : ℂˣ) : ℂ)).mul (Evaluates.var z)).zpow
      (mul_ne_zero (Units.ne_zero _) hz) j
    exact ⟨_,Evaluates.const _ _,he.mul (Evaluates.const _ _)⟩
  have hsum := Twice.sum Finset.univ (fun (ξ : CubicUnitCharacters.Character K) _ =>
    Twice.sum Finset.univ (fun (ε : CubicCharacters.Mu3) _ =>
      (hc ξ ε).mul (characterR_twice K m z Q hQ ξ ε hA (hb ε) (hbQ ε))))
  have hfac := (((Twice.var z Q).zpow hQ (-j)).mul
      ((Twice.const z Q 1).sub (Twice.var z Q))).div (Twice.const z Q 3) (by norm_num)
  have he := (hfac.mul hsum).eval
  simpa only [shiftedModel,finsum_eq_sum_of_fintype,map_one,map_ofNat] using he

end
end ShiftedBetaAlgebra

namespace ShiftedBetaPower
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
private theorem absPower (ρ : ℂ) (x : Kˣ) :
    Complex.exp (-ρ * (Real.log (KPCubicHaar.abs K (x : K)) : ℂ)) =
      Complex.exp (-ρ * (Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ)) ^
        (-KPCubicExpansion.valuationExponent K x) := by
  rw [KPJointRegulator.MellinBetaIntegrability.abs_eq_rpow_valuationExponent]
  have hq : 0 < (CubicUnitCharacters.residueCard K : ℝ) := by
    exact_mod_cast (show 0 < CubicUnitCharacters.residueCard K from by
      have h : 2 ≤ CubicUnitCharacters.residueCard K := KPCubicUnitIndices.two_le_residueCard K
      omega)
  rw [Real.log_zpow]
  push_cast
  rw [← Complex.exp_int_mul]
  congr 1
  change _ = ((-KPCubicExpansion.valuationExponent K x : ℤ) : ℂ) *
    (-ρ * Complex.log (CubicUnitCharacters.residueCard K : ℂ))
  simp only [Int.cast_neg]
  push_cast
  ring
  rfl
private theorem ramified_shell_substitution {E : Type*} [Field E] (a m Q : E) (f : ℕ) (hf : 1 ≤ f)
    (hQ : Q ≠ 0) (hQA : Q-a ≠ 0) :
    m * (a/Q)^(f-1) * (a/Q-a) / (1-a/Q) =
      (1-Q) * (m * a^f * Q^(1-(f : ℤ)) / (Q-a)) := by
  have hpow : Q ^ (1-(f : ℤ)) = (Q^(f-1))⁻¹ := by
    rw [show 1-(f : ℤ) = -((f-1 : ℕ) : ℤ) by omega,zpow_neg,zpow_natCast]
  rw [hpow,div_pow]
  have haf : a^f = a^(f-1)*a := by
    conv_lhs => rw [show f = (f-1)+1 by omega]
    rw [pow_succ]
  rw [haf]
  field_simp
  <;> ring
private theorem unramified_shell_substitution {E : Type*} [Field E] (a m b Q : E)
    (hQ : Q ≠ 0) (hb : 1-b ≠ 0) (hbQ : b-Q ≠ 0) (hQA : Q-a ≠ 0)
    (ha : a ≠ 0) :
    m * ((1-a)*(b/(1-b)+(a/Q)/(1-a/Q)+a/(b*(a/Q)-a))+1-2*a) =
      (1-Q) * (m*(b-a)*(Q-a*b)/((1-b)*(b-Q)*(Q-a))) := by
  field_simp
  <;> ring

section
variable [MeasurableSpace K] [BorelSpace K]
private theorem prescribed_beta_cone
    (dx : Measure K) [dx.IsAddHaarMeasure] (π : Kˣ)
    (hπ : valuation K (π : K) = uniformizer K)
    (ξ : CubicUnitCharacters.Character K) (b : ℂˣ) (η : Kˣ →ₜ* ℂˣ)
    (hη : ∀ (j : ℤ) (u : (𝒪[K])ˣ),
      η (π^j*KPRankOneCubicProjection.unitInclusion K u) = b^j*(ξ u : ℂˣ))
    (ρ : ℂ) (hρ : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hblo : (CubicUnitCharacters.residueCard K : ℝ).rpow (-ρ.re) < ‖(b : ℂ)‖)
    (hbhi : ‖(b : ℂ)‖ < 1) :
    let A : ℂ := (CubicUnitCharacters.residueCard K : ℂ)⁻¹
    let Q := Complex.exp (-ρ*(Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
    let m : ℂ := (KPRankOneRamifiedBeta.m K dx : ℂ)
    Integrable (fun y : Kˣ => (η y : ℂ)*KPCubicExpansion.betaFunction K ρ y)
      (KPCubicHaar.multiplicativeHaar K dx) ∧
    (∫ y : Kˣ, (η y : ℂ)*KPCubicExpansion.betaFunction K ρ y
      ∂KPCubicHaar.multiplicativeHaar K dx) =
      (1-Q) * (if ξ = 1 then m*((b : ℂ)-A)*(Q-A*(b : ℂ))/((1-(b : ℂ))*((b : ℂ)-Q)*(Q-A))
        else m*A^CubicUnitCharacters.conductor K ξ*Q^(1-(CubicUnitCharacters.conductor K ξ : ℤ))/(Q-A)) := by
  dsimp only
  let q : ℝ := CubicUnitCharacters.residueCard K
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast (show 1 < CubicUnitCharacters.residueCard K from by
      have h : 2 ≤ CubicUnitCharacters.residueCard K := KPCubicUnitIndices.two_le_residueCard K
      omega)
  have hq0 := lt_trans zero_lt_one hq
  let Q := Complex.exp (-ρ*(Real.log q : ℂ))
  let u : ℂˣ := Units.mk0 (Complex.exp ((ρ-1)*(Real.log q : ℂ))) (Complex.exp_ne_zero _)
  have hu : (u : ℂ) = (q : ℂ)⁻¹ / Q := by
    change Complex.exp ((ρ-1)*(Real.log q : ℂ)) = _
    rw [show (ρ-1)*(Real.log q : ℂ) = -(Real.log q : ℂ) - (-ρ*(Real.log q : ℂ)) by ring,
      Complex.exp_sub,Complex.exp_neg]
    rw [← Complex.ofReal_exp, Real.exp_log hq0]
  obtain ⟨hb0,hb1,hu0,hu1⟩ := RegulatedResidue.joint_strip_geometric_bounds q hq ρ hρ1 b hblo hbhi
  have hun := RegulatedResidue.norm_beta_exp_parameter q hq0 ρ
  have hA : ‖KPRankOneRamifiedBeta.a K‖ = q⁻¹ := by
    simp only [KPRankOneRamifiedBeta.a,norm_inv]
    change ‖(q : ℂ)‖⁻¹ = q⁻¹
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq0]
  have hm : 0 < KPRankOneRamifiedBeta.m K dx := by
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    have hn : (𝒪[K] : Set K) ∈ nhds (0 : K) := by
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨(1 : (ValueGroupWithZero K)ˣ), ?_⟩
      intro x hx
      exact le_of_lt (by simpa using hx)
    exact ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds dx hn).ne'
      ((IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_ne_top)
  have hvol : dx (𝒪[K] : Set K) = ENNReal.ofReal (KPRankOneRamifiedBeta.m K dx) := by
    exact (ENNReal.ofReal_toReal ((IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_ne_top)).symm
  have hQn : Q ≠ 0 := Complex.exp_ne_zero _
  have hQnorm : ‖Q‖ = q.rpow (-ρ.re) := by
    rw [Complex.norm_exp]
    dsimp [Q]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [Real.rpow_def_of_pos hq0]
    rw [mul_comm]
  have hQA : Q-(q : ℂ)⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro e
    have he := congrArg norm e
    have hlt : q⁻¹ < q.rpow (-ρ.re) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
    rw [hQnorm,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq0] at he
    linarith
  have hbQ : (b : ℂ)-Q ≠ 0 := sub_ne_zero.mpr (by
    intro e
    have he := congrArg norm e
    rw [hQnorm] at he
    linarith)
  have hbN : 1-(b : ℂ) ≠ 0 := sub_ne_zero.mpr (by
    intro e
    have he := congrArg norm e
    rw [norm_one] at he
    linarith)
  by_cases hξ : ξ = 1
  · have heη := RegulatedResidue.character_eq_eta_of_coordinates K π hπ b η (by
      intro j v
      change η (π^j*KPRankOneCubicProjection.unitInclusion K v) = _
      rw [hη,hξ]
      simp)
    have hreg : KPRankOneUnramifiedBetaShells.ConvergenceRegion K (b : ℂ) (u : ℂ) := by
      change q⁻¹ < _ ∧ _ < 1 ∧ q⁻¹ / _ < _ ∧ _ < 1
      change q⁻¹ < _ ∧ _ < 1 ∧ q⁻¹ / _ < ‖Complex.exp ((ρ-1)*(Real.log q : ℂ))‖ ∧
        ‖Complex.exp ((ρ-1)*(Real.log q : ℂ))‖ < 1
      rw [hun]
      exact ⟨hb0,hb1,hu0,hu1⟩
    obtain ⟨hint,he⟩ := KPRankOneUnramifiedBetaShells.integral_three_region K dx _ hm hvol b u hreg
    have hfun : (fun y : Kˣ => (η y : ℂ)*KPCubicExpansion.betaFunction K ρ y) =
        KPRankOneUnramifiedBetaShells.integrand K b u := by
      funext y
      rw [heη]
      exact RegulatedResidue.betaFunction_eq_unramified_integrand K b ρ y
    refine ⟨hfun.symm ▸ hint, ?_⟩
    rw [hfun]
    change KPRankOneUnramifiedBetaShells.betaIntegral K dx b u = _
    rw [he]
    simp only [KPRankOneUnramifiedBetaShells.formula,hξ,ite_true]
    rw [hu]
    exact unramified_shell_substitution (q : ℂ)⁻¹ _ (b : ℂ) Q hQn hbN hbQ hQA
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr hq0.ne'))
  · obtain ⟨hint,he⟩ := betaIntegral_eq_rationalBeta K dx π hπ ξ hξ b η hη u
      (by rw [hA]; exact hb0) hb1 (by rw [hA]; change q⁻¹ / _ < ‖Complex.exp ((ρ-1)*(Real.log q : ℂ))‖; rw [hun]; exact hu0)
      (by change ‖Complex.exp ((ρ-1)*(Real.log q : ℂ))‖ < 1; rw [hun]; exact hu1)
    have hfun : (fun y : Kˣ => (η y : ℂ)*KPCubicExpansion.betaFunction K ρ y) =
        KPRankOneRamifiedBeta.betaIntegrand K η u := by
      funext y
      exact RegulatedResidue.betaFunction_eq_ramified_integrand K η ρ y
    refine ⟨hfun.symm ▸ hint, ?_⟩
    rw [hfun]
    change KPRankOneRamifiedBeta.betaIntegral K dx η u = _
    rw [he]
    simp only [KPRankOneRamifiedBeta.rationalBeta,hξ,ite_false]
    rw [hu]
    exact ramified_shell_substitution (q : ℂ)⁻¹ _ Q _ (KPRankOneRamifiedBeta.conductor_exact K ξ hξ).1 hQn hQA
end

 def shiftedTest (c : Kˣ) (ρ : ℂ) (v : Kˣ) : ℂ :=
  if (v : K)+(c : K)=0 then 0 else
    Complex.exp (-ρ*(Real.log (KPCubicHaar.abs K ((v : K)+(c : K))) : ℂ))
private theorem shiftedTest_mul (c : Kˣ) (ρ : ℂ) (y : Kˣ) :
    shiftedTest K c ρ (-c*y) =
      Complex.exp (-ρ*(Real.log (KPCubicHaar.abs K (c : K)) : ℂ))*
        KPCubicExpansion.betaFunction K ρ y := by
  have he : ((-c*y : Kˣ) : K)+(c : K) = (c : K)*(1-(y : K)) := by
    simp only [Units.val_mul,Units.val_neg]; ring
  have hc : 0 < KPCubicHaar.abs K (c : K) := KPCubicHaar.abs_pos K c.ne_zero
  by_cases hy : y = 1
  · simp [shiftedTest,KPCubicExpansion.betaFunction,hy]
  · have hy0 : 1-(y : K) ≠ 0 := sub_ne_zero.mpr (by
      intro e; apply hy; exact Units.ext e.symm)
    have hs : 0 < KPCubicHaar.abs K (1-(y : K)) := KPCubicHaar.abs_pos K hy0
    simp only [shiftedTest,he,mul_eq_zero, c.ne_zero,hy0,or_self,ite_false,
      KPCubicExpansion.betaFunction,ite_eq_right_iff]
    rw [if_neg hy,KPCubicHaar.abs_mul,Real.log_mul hc.ne' hs.ne',Complex.ofReal_add,
      mul_add,Complex.exp_add]
    congr 1
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne'),← Complex.ofReal_log hs.le]
    congr 1
    ring
section
variable [MeasurableSpace K] [BorelSpace K]
private theorem units_measurableMul : MeasurableMul Kˣ := by
  have hv : Measurable (fun x : Kˣ => (x : K)) := MeasurableSpace.le_map_comap
  constructor <;> intro a
  · change Measurable (fun x : Kˣ => a*x)
    rw [measurable_iff_comap_le]
    unfold Units.instMeasurableSpace
    rw [MeasurableSpace.comap_comp]
    exact (hv.const_mul (a : K)).comap_le
  · change Measurable (fun x : Kˣ => x*a)
    rw [measurable_iff_comap_le]
    unfold Units.instMeasurableSpace
    rw [MeasurableSpace.comap_comp]
    exact (hv.mul_const (a : K)).comap_le
private theorem shifted_character_integral
    (μ : Measure Kˣ) [μ.IsMulLeftInvariant] (c : Kˣ) (ρ : ℂ) (η : Kˣ →ₜ* ℂˣ)
    (hi : Integrable (fun y : Kˣ => (η y : ℂ)*KPCubicExpansion.betaFunction K ρ y) μ) :
    Integrable (fun v : Kˣ => (η v : ℂ)*shiftedTest K c ρ v) μ ∧
    (∫ v : Kˣ, (η v : ℂ)*shiftedTest K c ρ v ∂μ) =
      (η (-c) : ℂ)*Complex.exp (-ρ*(Real.log (KPCubicHaar.abs K (c : K)) : ℂ))*
        ∫ y : Kˣ, (η y : ℂ)*KPCubicExpansion.betaFunction K ρ y ∂μ := by
  letI := units_measurableMul K
  let d := (η (-c) : ℂ)*Complex.exp (-ρ*(Real.log (KPCubicHaar.abs K (c : K)) : ℂ))
  have he (y : Kˣ) : (η (-c*y) : ℂ)*shiftedTest K c ρ (-c*y) =
      d*((η y : ℂ)*KPCubicExpansion.betaFunction K ρ y) := by
    rw [shiftedTest_mul,map_mul,Units.val_mul]
    dsimp [d]; ring
  have ht : Integrable (fun y : Kˣ => (η (-c*y) : ℂ)*shiftedTest K c ρ (-c*y)) μ := by
    simp_rw [he]
    exact hi.const_mul d
  refine ⟨?_, ?_⟩
  · have hr := ht.comp_mul_left (-c)⁻¹
    simpa only [← mul_assoc,mul_inv_cancel,one_mul] using hr
  · rw [← integral_mul_left_eq_self (fun v : Kˣ => (η v : ℂ)*shiftedTest K c ρ v) (-c)]
    simp_rw [he]
    rw [integral_const_mul]
end

private theorem multiplicativeHaar_isHaar [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) [dx.IsAddHaarMeasure] :
    (KPCubicHaar.multiplicativeHaar K dx).IsHaarMeasure := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  have hn : (𝒪[K] : Set K) ∈ nhds (0 : K) := by
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨(1 : (ValueGroupWithZero K)ˣ), ?_⟩
    intro x hx
    exact le_of_lt (by simpa using hx)
  have hp := Measure.measure_pos_of_mem_nhds dx hn
  have hf : dx (𝒪[K] : Set K) ≠ ⊤ := (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_ne_top
  exact (kp_rankone_cubic_haar_power_measure K dx _ (ENNReal.toReal_pos hp.ne' hf)
    (ENNReal.ofReal_toReal hf).symm).1
end ShiftedBetaPower

theorem actual_shifted_beta_common_zero
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (dx : Measure (q.adicCompletion F)) [dx.IsAddHaarMeasure]
    (π : (q.adicCompletion F)ˣ)
    (hπ : valuation (q.adicCompletion F) (π : q.adicCompletion F) = uniformizer (q.adicCompletion F)) :
    let K := q.adicCompletion F
    let A : ℂ := (CubicUnitCharacters.residueCard K : ℂ)⁻¹
    let m : ℂ := (KPRankOneRamifiedBeta.m K dx : ℂ)
    let R : CubicUnitCharacters.Character K → ℂ → ℂ → ℂ := fun ξ b Q =>
      if ξ = 1 then m * (b-A) * (Q-A*b) / ((1-b)*(b-Q)*(Q-A))
      else m * A ^ CubicUnitCharacters.conductor K ξ * Q ^ (1-(CubicUnitCharacters.conductor K ξ : ℤ)) / (Q-A)
    let Rrat : CubicUnitCharacters.Character K → CubicCharacters.Mu3 → RatFunc (RatFunc ℂ) := fun ξ ε =>
      let a : RatFunc (RatFunc ℂ) := RatFunc.C (RatFunc.C A)
      let b : RatFunc (RatFunc ℂ) := RatFunc.C (RatFunc.C ((ε : ℂˣ) : ℂ) * RatFunc.X)
      let Q : RatFunc (RatFunc ℂ) := RatFunc.X
      if ξ = 1 then RatFunc.C (RatFunc.C m) * (b-a) * (Q-a*b) / ((1-b)*(b-Q)*(Q-a))
      else RatFunc.C (RatFunc.C m) * a ^ CubicUnitCharacters.conductor K ξ * Q ^ (1-(CubicUnitCharacters.conductor K ξ : ℤ)) / (Q-a)
    let betaRat : ℤ → (𝒪[K])ˣ → RatFunc (RatFunc ℂ) := fun j u =>
      (RatFunc.X : RatFunc (RatFunc ℂ)) ^ (-j) * (1-RatFunc.X) / 3 *
        ∑ᶠ ξ : CubicUnitCharacters.Character K, ∑ᶠ ε : CubicCharacters.Mu3,
          RatFunc.C ((RatFunc.C ((ε : ℂˣ) : ℂ) * RatFunc.X)^j * RatFunc.C ((ξ u : ℂˣ) : ℂ)) * Rrat ξ ε
    ∃ θ : CubicUnitCharacters.Character K → ℂˣ → (Kˣ →ₜ* ℂˣ),
      (∀ ξ b (j : ℤ) (u : (𝒪[K])ˣ),
        θ ξ b (π ^ j * KPRankOneCubicProjection.unitInclusion K u) = b ^ j * (ξ u : ℂˣ)) ∧
      (∀ (c : Kˣ) (t z : ℂˣ) (hz : z^3=t) (ρ : ℂ), KPJointRegulator.cone K t ρ →
        let Q := Complex.exp (-ρ * (Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
        Integrable (fun y : Kˣ => if (y : K)^3+(c : K)=0 then 0 else
          KPCubicExpansion.omega K t y * Complex.exp (-ρ * (Real.log (KPCubicHaar.abs K ((y : K)^3+(c : K))) : ℂ)))
          (KPCubicHaar.multiplicativeHaar K dx) ∧
        (∫ y : Kˣ, if (y : K)^3+(c : K)=0 then 0 else
          KPCubicExpansion.omega K t y * Complex.exp (-ρ * (Real.log (KPCubicHaar.abs K ((y : K)^3+(c : K))) : ℂ))
          ∂KPCubicHaar.multiplicativeHaar K dx) =
          Q ^ (-KPCubicExpansion.valuationExponent K c) * (1-Q) / 3 *
            ∑ᶠ ξ : CubicUnitCharacters.Character K, ∑ᶠ ε : CubicCharacters.Mu3,
              (θ ξ ((ε : ℂˣ)*z) (-c) : ℂ) * R ξ (((ε : ℂˣ) : ℂ)*(z : ℂ)) Q) ∧
      (∀ ξ ε, (Rrat ξ ε).denom.eval (1 : RatFunc ℂ) ≠ 0 ∧
        RatFunc.eval (RingHom.id (RatFunc ℂ)) 1 (Rrat ξ ε) =
          RatFunc.C (m/(1-A)) * KPRankoneCubicScalarSum.betaFactor K ξ
            (RatFunc.C ((ε : ℂˣ) : ℂ) * RatFunc.X)) ∧
      (∀ (j : ℤ) (u : (𝒪[K])ˣ),
        (betaRat j u).denom.eval (1 : RatFunc ℂ) ≠ 0 ∧
        RatFunc.eval (RingHom.id (RatFunc ℂ)) 1 (betaRat j u) = 0) ∧
      (∀ (c : Kˣ) (j : ℤ) (u : (𝒪[K])ˣ),
        -c = π ^ j * KPRankOneCubicProjection.unitInclusion K u →
        ∀ (t z : ℂˣ), z^3=t → ∀ (ρ : ℂ), KPJointRegulator.cone K t ρ →
        let Q := Complex.exp (-ρ * (Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
        (∫ y : Kˣ, if (y : K)^3+(c : K)=0 then 0 else
          KPCubicExpansion.omega K t y * Complex.exp (-ρ * (Real.log (KPCubicHaar.abs K ((y : K)^3+(c : K))) : ℂ))
          ∂KPCubicHaar.multiplicativeHaar K dx) =
          RatFunc.eval (RingHom.id ℂ) (z : ℂ)
            (RatFunc.eval (RingHom.id (RatFunc ℂ)) (RatFunc.C Q) (betaRat j u))) := by
  dsimp only
  let K := q.adicCompletion F
  have hext (ξ : CubicUnitCharacters.Character K) (b : ℂˣ) :=
    exists_eta_uniformizer_extension K π hπ ξ b
  choose θ hθ using hext
  haveI := KPCubicHaar.cubeUnits_finiteIndex (K := K)
  haveI : Finite (CubicUnitCharacters.Character K) := Nat.finite_of_card_ne_zero (by
    rw [KPCubicExpansion.card_unit_cubic_characters]
    exact Subgroup.index_ne_zero_of_finite)
  have hformula (c : Kˣ) (t z : ℂˣ) (hz : z^3=t) (ρ : ℂ) (hcone : KPJointRegulator.cone K t ρ) :
      let Q := Complex.exp (-ρ*(Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
      (∫ y : Kˣ, if (y : K)^3+(c : K)=0 then 0 else
        KPCubicExpansion.omega K t y*Complex.exp (-ρ*(Real.log (KPCubicHaar.abs K ((y : K)^3+(c : K))) : ℂ))
        ∂KPCubicHaar.multiplicativeHaar K dx) =
        Q^(-KPCubicExpansion.valuationExponent K c)*(1-Q)/3*
          ∑ᶠ ξ : CubicUnitCharacters.Character K, ∑ᶠ ε : CubicCharacters.Mu3,
            (θ ξ ((ε : ℂˣ)*z) (-c) : ℂ)*
              (if ξ = 1 then (KPRankOneRamifiedBeta.m K dx : ℂ)*
                (((ε : ℂˣ) : ℂ)*(z : ℂ)-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)*
                (Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹*(((ε : ℂˣ) : ℂ)*(z : ℂ)))/
                ((1-((ε : ℂˣ) : ℂ)*(z : ℂ))*(((ε : ℂˣ) : ℂ)*(z : ℂ)-Q)*(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹))
               else (KPRankOneRamifiedBeta.m K dx : ℂ)*((CubicUnitCharacters.residueCard K : ℂ)⁻¹)^CubicUnitCharacters.conductor K ξ*
                Q^(1-(CubicUnitCharacters.conductor K ξ : ℤ))/(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)) := by
    have hp := hζ.pow (by norm_num : 0 < 12) (by norm_num : 12 = 4*3)
    have hpK : IsPrimitiveRoot (algebraMap F K (ζ^4)) 3 :=
      hp.map_of_injective (algebraMap F K).injective
    have hv : valuation K (algebraMap F K (ζ^4)) = 1 := by
      apply (pow_eq_one_iff_of_nonneg zero_le (by norm_num : (3:ℕ)≠0)).mp
      rw [← map_pow,hpK.pow_eq_one,map_one]
    let κ : 𝒪[K] := ⟨_,hv.le⟩
    have hκ : IsPrimitiveRoot κ 3 := hpK.of_map_of_injective
      (f := (𝒪[K]).subtype) Subtype.val_injective
    letI := ShiftedBetaPower.multiplicativeHaar_isHaar K dx
    obtain ⟨_,χ,hχ,_,habs,_⟩ := kp_rankone_cubic_character_expansion K κ hκ dx π hπ t z hz
    have hχeq (ξ : CubicUnitCharacters.Character K) (ε : CubicCharacters.Mu3) :
        χ ξ ε = θ ξ ((ε : ℂˣ)*z) := by
      apply ContinuousMonoidHom.ext
      intro y
      obtain ⟨j,u,rfl⟩ := RegulatedResidue.uniformizer_unit_decomposition K π hπ y
      rw [hχ]
      exact (hθ ξ ((ε : ℂˣ)*z) j u).symm
    let qsize : ℝ := CubicUnitCharacters.residueCard K
    have hq : 1 < qsize := by
      dsimp only [qsize]
      exact_mod_cast (show 1 < CubicUnitCharacters.residueCard K from by
        have h : 2 ≤ CubicUnitCharacters.residueCard K := KPCubicUnitIndices.two_le_residueCard K
        omega)
    obtain ⟨hzlo,hzhi⟩ := RegulatedResidue.cube_root_norm_bounds qsize (zero_lt_one.trans hq) t z ρ hz
      hcone.2.2.1 hcone.2.2.2
    have hbet (ξ : CubicUnitCharacters.Character K) (ε : CubicCharacters.Mu3) :=
      ShiftedBetaPower.prescribed_beta_cone K dx π hπ ξ ((ε : ℂˣ)*z) (χ ξ ε) (hχ ξ ε) ρ
        hcone.1 hcone.2.1 (by
          rw [Units.val_mul,norm_mul,Complex.norm_eq_one_of_mem_rootsOfUnity ε.property,one_mul]
          exact hzlo) (by
          rw [Units.val_mul,norm_mul,Complex.norm_eq_one_of_mem_rootsOfUnity ε.property,one_mul]
          exact hzhi)
    have hshift (ξ : CubicUnitCharacters.Character K) (ε : CubicCharacters.Mu3) :=
      ShiftedBetaPower.shifted_character_integral K (KPCubicHaar.multiplicativeHaar K dx) c ρ (χ ξ ε) (hbet ξ ε).1
    have hi : Integrable (fun y : Kˣ => KPCubicExpansion.omega K t y *
        ShiftedBetaPower.shiftedTest K c ρ (y^3)) (KPCubicHaar.multiplicativeHaar K dx) := by
      have hi := KPActualFullKernelArithmetic.actual_shifted_beta_integrable F q dx c t ρ hcone
      convert hi using 1
      funext y
      unfold ShiftedBetaPower.shiftedTest
      simp only [Units.val_pow_eq_pow_val]
      split_ifs <;> simp <;> rfl
    have he := habs (ShiftedBetaPower.shiftedTest K c ρ) hi (fun ξ ε => (hshift ξ ε).1)
    change (∫ y : Kˣ, KPCubicExpansion.omega K t y * ShiftedBetaPower.shiftedTest K c ρ (y^3)
      ∂KPCubicHaar.multiplicativeHaar K dx) = _ at he
    have eorig : (fun y : Kˣ => if (y : K)^3+(c : K)=0 then 0 else
        KPCubicExpansion.omega K t y * Complex.exp (-ρ*(Real.log (KPCubicHaar.abs K ((y : K)^3+(c : K))) : ℂ))) =
      (fun y => KPCubicExpansion.omega K t y * ShiftedBetaPower.shiftedTest K c ρ (y^3)) := by
      funext y
      unfold ShiftedBetaPower.shiftedTest
      simp only [Units.val_pow_eq_pow_val]
      split_ifs <;> simp
    rw [eorig,he]
    have es (ξ : CubicUnitCharacters.Character K) (ε : CubicCharacters.Mu3) := (hshift ξ ε).2
    simp_rw [es,(hbet _ _).2, hχeq,ShiftedBetaPower.absPower K ρ c]
    letI : Fintype (CubicUnitCharacters.Character K) := Fintype.ofFinite _
    letI : Fintype CubicCharacters.Mu3 := Fintype.ofFinite _
    simp only [finsum_eq_sum_of_fintype,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ hξ
    apply Finset.sum_congr rfl
    intro ε hε
    simp only [Units.val_mul]
    split_ifs <;> ring
  refine ⟨θ, hθ, ?_, ?_, ?_, ?_⟩
  · intro c t z hz ρ hcone
    exact ⟨KPActualFullKernelArithmetic.actual_shifted_beta_integrable F q dx c t ρ hcone,
      hformula c t z hz ρ hcone⟩
  · intro ξ ε
    exact ShiftedBetaAlgebra.characterR_one K (KPRankOneRamifiedBeta.m K dx : ℂ) ξ ε
  · intro j u
    exact ShiftedBetaAlgebra.shiftedModel_one K (KPRankOneRamifiedBeta.m K dx : ℂ) j u
  · intro c j u hcu t z hz ρ hcone
    let Q := Complex.exp (-ρ*(Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
    let qsize : ℝ := CubicUnitCharacters.residueCard K
    have hq : 1 < qsize := by
      dsimp only [qsize]
      exact_mod_cast (show 1 < CubicUnitCharacters.residueCard K from by
        have h : 2 ≤ CubicUnitCharacters.residueCard K := KPCubicUnitIndices.two_le_residueCard K
        omega)
    have hq0 := zero_lt_one.trans hq
    obtain ⟨hzlo,hzhi⟩ := RegulatedResidue.cube_root_norm_bounds qsize hq0 t z ρ hz
      hcone.2.2.1 hcone.2.2.2
    have hQn : Q ≠ 0 := Complex.exp_ne_zero _
    have hQnorm : ‖Q‖ = qsize.rpow (-ρ.re) := by
      rw [Complex.norm_exp]
      dsimp [Q]
      simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      rw [Real.rpow_def_of_pos hq0,mul_comm]
    have hQA : Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹ ≠ 0 := by
      apply sub_ne_zero.mpr
      intro e
      have he := congrArg norm e
      have hlt : qsize⁻¹ < qsize.rpow (-ρ.re) := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_lt_rpow_of_exponent_lt hq (by linarith [hcone.2.1])
      rw [hQnorm,norm_inv] at he
      have hnormq : ‖(CubicUnitCharacters.residueCard K : ℂ)‖ = qsize := by
        change ‖(qsize : ℂ)‖ = qsize
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq0]
      rw [hnormq] at he
      linarith
    have hn (ε : CubicCharacters.Mu3) : ‖((ε : ℂˣ) : ℂ)*(z : ℂ)‖ = ‖(z : ℂ)‖ := by
      rw [norm_mul,Complex.norm_eq_one_of_mem_rootsOfUnity ε.property,one_mul]
    have hb (ε : CubicCharacters.Mu3) : 1-((ε : ℂˣ) : ℂ)*(z : ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro e
      have he := congrArg norm e
      rw [norm_one,hn] at he
      linarith
    have hbQ (ε : CubicCharacters.Mu3) : ((ε : ℂˣ) : ℂ)*(z : ℂ)-Q ≠ 0 := by
      apply sub_ne_zero.mpr
      intro e
      have he := congrArg norm e
      rw [hn,hQnorm] at he
      linarith
    have ev := ShiftedBetaAlgebra.shiftedModel_twice K (KPRankOneRamifiedBeta.m K dx : ℂ)
      (z : ℂ) Q z.ne_zero hQn j u hQA hb hbQ
    change _ = RatFunc.eval (RingHom.id ℂ) (z : ℂ)
      (RatFunc.eval (RingHom.id (RatFunc ℂ)) (RatFunc.C Q)
        (ShiftedBetaAlgebra.shiftedModel K (KPRankOneRamifiedBeta.m K dx : ℂ) j u))
    rw [ev,hformula c t z hz ρ hcone]
    have hj : KPCubicExpansion.valuationExponent K c = j := by
      have he := congrArg (KPCubicExpansion.valuationExponent K) hcu
      rw [KPCubicExpansion.valuationExponent_mul,KPCubicExpansion.valuationExponent_zpow,
        KPCubicExpansion.valuationExponent_uniformizer π hπ] at he
      have hu0 : KPCubicExpansion.valuationExponent K (KPRankOneCubicProjection.unitInclusion K u) = 0 :=
        KPCubicExpansion.valuationExponent_unit u
      rw [hu0,mul_one,add_zero] at he
      have hc0 : KPCubicExpansion.valuationExponent K (-c) = KPCubicExpansion.valuationExponent K c := by
        simp [KPCubicExpansion.valuationExponent,Units.val_neg,Valuation.map_neg]
      rw [hc0] at he
      exact he
    rw [hj]
    congr 1
    apply finsum_congr
    intro ξ
    apply finsum_congr
    intro ε
    rw [hcu,hθ,Units.val_mul,Units.val_zpow_eq_zpow_val,Units.val_mul]

end DedekindZetaZeroFree

end
