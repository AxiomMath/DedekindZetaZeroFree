module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.CubicResidueRegularValues

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps

open KPLocalStoneVonNeumann KPRankOneCubicResidueReduction
open KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneGenericComposition KPRankOneRootParameter

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

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
private lemma regular_mul_eval {F : Type*} [Field F] {u : F} {r s : RatFunc F}
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
  refine ⟨regular_mul_eval hr.1 hs.1, ?_⟩
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
private lemma Evaluates.sum {F I : Type*} [Field F] {u : F} (s : Finset I)
    {r : I → RatFunc F} {a : I → F} (h : ∀ i ∈ s, Evaluates u (r i) (a i)) :
    Evaluates u (∑ i ∈ s, r i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, map_zero] using Evaluates.const u 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma betaFactor_evaluates
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ξ : CubicUnitCharacters.Character K)
    (w : ℂ) (B : RatFunc ℂ) (b : ℂ) (hB : Evaluates w B b) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    Evaluates w (KPRankoneCubicScalarSum.betaFactor K ξ B)
      (KPRankoneCubicScalarSum.betaFactor K ξ b) := by
  classical
  have hA := (Evaluates.const w (CubicUnitCharacters.residueCard K : ℂ)⁻¹)
  have h1 := Evaluates.const w 1
  by_cases hξ : ξ=1
  · have hBi := hB.inv hb0
    have hden : (1-b)*(1-b⁻¹) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hb1.symm)
        (sub_ne_zero.mpr (by intro h; exact hb1 (inv_eq_one.mp h.symm)))
    have h := ((h1.sub (hA.mul hB)).mul (h1.sub (hA.mul hBi))).div
      ((h1.sub hB).mul (h1.sub hBi)) hden
    simpa only [KPRankoneCubicScalarSum.betaFactor,hξ,ite_true,
      KPRankoneCubicScalarSum.unramifiedFactor,map_one,map_inv₀,map_natCast] using h
  · simpa only [KPRankoneCubicScalarSum.betaFactor,hξ,ite_false,map_natCast,map_inv₀] using
      hA.pow (CubicUnitCharacters.conductor K ξ)

private theorem residue_scalar_regular_eval
    (dx : Measure (KPExceptionalRaw.LocalField F q))
    (w : ℂ) (hw0 : w ≠ 0) (hw6 : w^6 ≠ 1) :
    Evaluates w (rationalResidueScalar (KPExceptionalRaw.LocalField F q) dx)
      (residueScalar (KPExceptionalRaw.LocalField F q) dx (w^2)) := by
  classical
  let K := KPExceptionalRaw.LocalField F q
  haveI := KPCubicHaar.cubeUnits_finiteIndex (K := K)
  haveI : Finite (CubicUnitCharacters.Character K) :=
    Nat.finite_of_card_ne_zero (by
      rw [KPCubicExpansion.card_unit_cubic_characters]
      exact Subgroup.index_ne_zero_of_finite)
  letI := Fintype.ofFinite (CubicUnitCharacters.Character K)
  letI := Fintype.ofFinite CubicCharacters.Mu3
  have hb (ε : CubicCharacters.Mu3) := (Evaluates.const w ((ε : ℂˣ) : ℂ)).mul ((Evaluates.var w).pow 2)
  have hb0 (ε : CubicCharacters.Mu3) : ((ε : ℂˣ) : ℂ)*w^2 ≠ 0 :=
    mul_ne_zero (ε : ℂˣ).ne_zero (pow_ne_zero _ hw0)
  have hb1 (ε : CubicCharacters.Mu3) : ((ε : ℂˣ) : ℂ)*w^2 ≠ 1 := by
    intro he
    have hp := congrArg (fun z : ℂ => z^3) he
    have hε : (((ε : ℂˣ) : ℂ))^3 = 1 := by
      exact congrArg Units.val ((mem_rootsOfUnity 3 (ε : ℂˣ)).mp ε.property)
    rw [mul_pow,hε,one_mul,← pow_mul,one_pow] at hp
    exact hw6 hp
  have hs := Evaluates.sum Finset.univ (fun ξ _ => Evaluates.sum Finset.univ (fun ε _ =>
    betaFactor_evaluates K ξ w _ _ (hb ε) (hb0 ε) (hb1 ε)))
  have h := (Evaluates.const w (((integerMass K dx^2*KPCubicHaar.abs K (3 : K) : ℝ) : ℂ)/9)).mul hs
  simpa only [rationalResidueScalar,residueScalar,KPRankoneCubicScalarSum.finiteScalar,
    finsum_eq_sum_of_fintype] using h

theorem regular_point_residue
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (hμ : 0 < integerMass (KPExceptionalRaw.LocalField F q) dx)
    (ω : (valuation (KPExceptionalRaw.LocalField F q)).integer)
    (hω : IsPrimitiveRoot ω 3) :
    ∀ (s z : ℂ), z ≠ 0 → z ^ 3 = t (KPExceptionalRaw.LocalField F q) s →
      denominator (KPExceptionalRaw.LocalField F q) .plus s ≠ 0 →
      denominator (KPExceptionalRaw.LocalField F q) .minus s ≠ 0 →
      ∀ (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q)),
        (J.toOpenSubgroup : Subgroup (KPExceptionalRaw.ActualCover F ζ hζ q)) ≤
          S.iwasawa.compact.toOpenSubgroup →
        ∀ (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus)
          (pRev : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus),
        IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .plus p →
        IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .minus pRev →
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev s).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p s) =
            residueScalar (KPExceptionalRaw.LocalField F q) dx z • LinearMap.id ∧
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p s).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev s) =
            residueScalar (KPExceptionalRaw.LocalField F q) dx z • LinearMap.id := by
  intro s z hz hzt hdplus hdminus J hJ p pRev hp hpRev
  let K := KPExceptionalRaw.LocalField F q
  obtain ⟨α,hα⟩ := IsAlgClosed.exists_pow_nat_eq (residueCardinality K : ℂ) (by decide : 0 < 6)
  have hq0 : (residueCardinality K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField (Valuation.integer (valuation K)))).ne'
  have hα0 : α ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide)] at hα
    exact hq0 hα.symm
  let w := r K s / α
  have hr0 : r K s ≠ 0 := Complex.exp_ne_zero _
  have hw0 : w ≠ 0 := div_ne_zero hr0 hα0
  have hroot : α * w = r K s := by dsimp [w]; field_simp
  have htw : w^6 = t K s := by
    dsimp [w]
    rw [div_pow,hα]
    unfold t
    ring
  have ht1 : t K s ≠ 1 := by
    intro he
    apply hdplus
    change 1 - t K s = 0
    rw [he,sub_self]
  have hw6 : w^6 ≠ 1 := htw ▸ ht1
  have hsc := residue_scalar_regular_eval F q dx w hw0 hw6
  have hsz : residueScalar K dx (w^2) = residueScalar K dx z := by
    unfold residueScalar
    exact KPRankoneCubicScalarSum.finiteScalar_cube_root_independent K ω.val
      (hω.map_of_injective (f := (valuation K).integer.subtype) Subtype.val_injective) (integerMass K dx) (KPCubicHaar.abs K (3 : K))
      (w^2) z (t K s) (pow_ne_zero _ hw0) hz (by rw [← pow_mul]; exact htw) hzt ht1
  have hforward := forward_two_cell_residue F ζ hζ q S P dx hμ ω hω α hα J hJ p pRev hp hpRev
  have hreverse := reverse_two_cell_residue F ζ hζ q S P dx hμ ω hω α hα J hJ p pRev hp hpRev
  have hplus := KPActualResidueSources.actual_level_composition_specialize_regular
    F ζ hζ q S P dx J hJ α hα p pRev (rationalResidueScalar K dx) .plus s w
      hw0 hroot hdplus hdminus hsc.1 (by simpa only [ite_true, KPRankOneGenericComposition.rationalStandard, KPRankOneGeneric.rationalStandard, KPRankOneGenericComposition.rationalDenominator, KPRankOneGeneric.rationalDenominator] using hforward)
  have hminus := KPActualResidueSources.actual_level_composition_specialize_regular
    F ζ hζ q S P dx J hJ α hα p pRev (rationalResidueScalar K dx) .minus s w
      hw0 hroot hdplus hdminus hsc.1 (by simpa only [show Sign.minus ≠ Sign.plus from by decide,ite_false, KPRankOneGenericComposition.rationalStandard, KPRankOneGeneric.rationalStandard, KPRankOneGenericComposition.rationalDenominator, KPRankOneGeneric.rationalDenominator] using hreverse)
  rw [hsc.2,hsz] at hplus hminus
  exact ⟨hplus,hminus⟩

end
end DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps
