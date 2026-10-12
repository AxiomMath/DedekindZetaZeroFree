module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.CubicBruhatResidue
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.RegularCompositionSpecialization
public import DedekindZetaZeroFree.Metaplectic.Intertwining.WeightedNumeratorNaturality
public import DedekindZetaZeroFree.Metaplectic.Intertwining.LaurentComposition

@[expose] public section

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse
open KPLocalPrincipalSeries KPRankOneRootParameter KPRankOneShellContinuation
open KPRankOneReverseRegulatorShells
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))

private lemma reflected_t (s : ℂ) :
    KPRankOneRootParameter.t (KPExceptionalRaw.LocalField F q) (-s-1/3) =
      (KPRankOneRootParameter.t (KPExceptionalRaw.LocalField F q) s)⁻¹ := by
  let Q : ℂ := (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)
  let L : ℂ := ((Real.log (residueCardinality (KPExceptionalRaw.LocalField F q) : ℝ) : ℂ))
  have hQ : 0 < (residueCardinality (KPExceptionalRaw.LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (KPExceptionalRaw.LocalField F q)))))
  have he : Complex.exp L = Q := by
    dsimp only [L, Q]
    rw [← Complex.ofReal_exp, Real.exp_log hQ]
    norm_cast
  change Q⁻¹ * Complex.exp (-(-s-1/3)*L)^6 = (Q⁻¹ * Complex.exp (-s*L)^6)⁻¹
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, mul_inv_rev, inv_inv,
    ← Complex.exp_neg, ← he, ← Complex.exp_neg, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  ring

theorem reflected_regular_dictionary
    (α w : ℂ)
    (hα : α ^ 6 = (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ))
    (hw : w ≠ 0) (hw6 : w ^ 6 ≠ 1)
    (r₀ : ℂˣ) (hr₀ : (r₀ : ℂ) = α * w) :
    let s := additiveParameter F q r₀
    denominator (KPExceptionalRaw.LocalField F q) .minus s ≠ 0 ∧
    denominator (KPExceptionalRaw.LocalField F q) .plus s ≠ 0 ∧
    denominator (KPExceptionalRaw.LocalField F q) .minus (-s-1/3) ≠ 0 ∧
    denominator (KPExceptionalRaw.LocalField F q) .plus (-s-1/3) ≠ 0 ∧
    (w ^ 2) ^ 3 = t (KPExceptionalRaw.LocalField F q) s ∧
    t (KPExceptionalRaw.LocalField F q) s ≠ 1 ∧
    ∃ z' : ℂ, z' ≠ 0 ∧
      z' ^ 3 = (t (KPExceptionalRaw.LocalField F q) s)⁻¹ ∧
      z' ^ 3 = t (KPExceptionalRaw.LocalField F q) (-s-1/3) := by
  dsimp only
  set s : ℂ := additiveParameter F q r₀ with hs
  have hQc : (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) ≠ 0 := by
    have hQ : 0 < (residueCardinality (KPExceptionalRaw.LocalField F q) : ℝ) := by
      exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
        (Valuation.integer (valuation (KPExceptionalRaw.LocalField F q)))))
    exact_mod_cast hQ.ne'

  have hrs : KPRankOneRootParameter.r (KPExceptionalRaw.LocalField F q) s = α * w := by
    rw [hs, root_parameter_additiveParameter F q r₀, hr₀]
  have h6s : (KPRankOneRootParameter.r (KPExceptionalRaw.LocalField F q) s) ^ 6 =
      (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) * w ^ 6 := by
    rw [hrs, mul_pow, hα]
  have hts : KPRankOneRootParameter.t (KPExceptionalRaw.LocalField F q) s = w ^ 6 := by
    simp only [KPRankOneRootParameter.t]
    rw [h6s, ← mul_assoc, inv_mul_cancel₀ hQc, one_mul]
  have htneg : KPRankOneRootParameter.t (KPExceptionalRaw.LocalField F q) (-s-1/3) =
      (w ^ 6)⁻¹ := by
    rw [reflected_t F q s, hts]
  have hw6inv : (w ^ 6)⁻¹ ≠ 1 := fun h => hw6 (inv_eq_one.mp h)
  have h6neg : (KPRankOneRootParameter.r (KPExceptionalRaw.LocalField F q) (-s-1/3)) ^ 6 =
      (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) * (w ^ 6)⁻¹ := by
    have h := congrArg
      (fun z : ℂ => (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) * z) htneg
    simp only [KPRankOneRootParameter.t] at h
    rw [← mul_assoc, mul_inv_cancel₀ hQc, one_mul] at h
    exact h
  have hdm : denominator (KPExceptionalRaw.LocalField F q) .minus s = 1 - (w ^ 6)⁻¹ := by
    rw [show denominator (KPExceptionalRaw.LocalField F q) .minus s =
        1 - (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) *
          (KPRankOneRootParameter.r (KPExceptionalRaw.LocalField F q) s)⁻¹ ^ 6 from rfl]
    rw [inv_pow, h6s, mul_inv_rev, mul_comm (w ^ 6)⁻¹, ← mul_assoc,
      mul_inv_cancel₀ hQc, one_mul]
  have hdp : denominator (KPExceptionalRaw.LocalField F q) .plus s = 1 - w ^ 6 := by
    rw [show denominator (KPExceptionalRaw.LocalField F q) .plus s =
        1 - KPRankOneRootParameter.t (KPExceptionalRaw.LocalField F q) s from rfl, hts]
  have hdm2 : denominator (KPExceptionalRaw.LocalField F q) .minus (-s-1/3) = 1 - w ^ 6 := by
    rw [show denominator (KPExceptionalRaw.LocalField F q) .minus (-s-1/3) =
        1 - (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) *
          (KPRankOneRootParameter.r (KPExceptionalRaw.LocalField F q) (-s-1/3))⁻¹ ^ 6 from rfl]
    rw [inv_pow, h6neg]
    field_simp
  have hdp2 : denominator (KPExceptionalRaw.LocalField F q) .plus (-s-1/3) = 1 - (w ^ 6)⁻¹ := by
    rw [show denominator (KPExceptionalRaw.LocalField F q) .plus (-s-1/3) =
        1 - KPRankOneRootParameter.t (KPExceptionalRaw.LocalField F q) (-s-1/3) from rfl, htneg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdm]; exact sub_ne_zero.mpr hw6inv.symm
  · rw [hdp]; exact sub_ne_zero.mpr hw6.symm
  · rw [hdm2]; exact sub_ne_zero.mpr hw6.symm
  · rw [hdp2]; exact sub_ne_zero.mpr hw6inv.symm
  · rw [← pow_mul]; exact hts.symm
  · rw [hts]; exact hw6
  · exact ⟨(w ^ 2)⁻¹, inv_ne_zero (pow_ne_zero 2 hw), by rw [inv_pow, ← pow_mul, hts],
      by rw [inv_pow, ← pow_mul, htneg]⟩

end
end DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse

end

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse
open KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneCubicResidueReduction KPRankOneRootParameter KPRankOneShellContinuation
open KPRankOneGenericComposition
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

 def CubicResidueDenomRegular {F : Type*} [Field F] (u : F) (r : RatFunc F) : Prop :=
  r.denom.eval u ≠ 0

private lemma cubicResidueDenomRegular_constant {F : Type*} [Field F] (u c : F) : CubicResidueDenomRegular u (RatFunc.C c) := by
  simp [CubicResidueDenomRegular]
private lemma cubicResidueDenomRegular_coordinate {F : Type*} [Field F] (u : F) : CubicResidueDenomRegular u (RatFunc.X : RatFunc F) := by
  simp [CubicResidueDenomRegular]
private lemma cubicResidueDenomRegular_add {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : CubicResidueDenomRegular u r) (hs : CubicResidueDenomRegular u s) : CubicResidueDenomRegular u (r+s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd r s) h)
private lemma cubicResidueDenomRegular_mul {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : CubicResidueDenomRegular u r) (hs : CubicResidueDenomRegular u s) : CubicResidueDenomRegular u (r*s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd r s) h)
private lemma cubicResidueDenomRegular_inv_of_value_ne_zero {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (_hr : CubicResidueDenomRegular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) : CubicResidueDenomRegular u r⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  intro h
  have hn := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_inv_dvd hr0) h
  apply hv
  simp [RatFunc.eval, hn]
private lemma cubicResidue_eval_inv_of_denom_regular_of_value_ne_zero {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (hr : CubicResidueDenomRegular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) :
    RatFunc.eval (RingHom.id F) u r⁻¹ = (RatFunc.eval (RingHom.id F) u r)⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  have hm := RatFunc.eval_mul (f := RingHom.id F) (a := u) hr (cubicResidueDenomRegular_inv_of_value_ne_zero hr hv)
  rw [mul_inv_cancel₀ hr0, RatFunc.eval_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

 def CubicResidueRegularValue {F : Type*} [Field F] (u : F) (r : RatFunc F) (v : F) : Prop :=
  CubicResidueDenomRegular u r ∧ RatFunc.eval (RingHom.id F) u r = v
private lemma CubicResidueRegularValue.const {F : Type*} [Field F] (u v : F) : CubicResidueRegularValue u (RatFunc.C v) v :=
  ⟨cubicResidueDenomRegular_constant u v, by simp⟩
private lemma CubicResidueRegularValue.var {F : Type*} [Field F] (u : F) : CubicResidueRegularValue u RatFunc.X u :=
  ⟨cubicResidueDenomRegular_coordinate u, by simp⟩
private lemma CubicResidueRegularValue.add {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : CubicResidueRegularValue u r a) (hs : CubicResidueRegularValue u s b) : CubicResidueRegularValue u (r+s) (a+b) := by
  refine ⟨cubicResidueDenomRegular_add hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_add (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma CubicResidueRegularValue.mul {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : CubicResidueRegularValue u r a) (hs : CubicResidueRegularValue u s b) : CubicResidueRegularValue u (r*s) (a*b) := by
  refine ⟨cubicResidueDenomRegular_mul hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_mul (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma CubicResidueRegularValue.neg {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : CubicResidueRegularValue u r a) : CubicResidueRegularValue u (-r) (-a) := by
  simpa only [map_neg, map_one, neg_one_mul] using (CubicResidueRegularValue.const u (-1)).mul hr
private lemma CubicResidueRegularValue.sub {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : CubicResidueRegularValue u r a) (hs : CubicResidueRegularValue u s b) : CubicResidueRegularValue u (r-s) (a-b) := by
  simpa only [sub_eq_add_neg] using hr.add hs.neg
private lemma CubicResidueRegularValue.inv {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : CubicResidueRegularValue u r a) (ha : a ≠ 0) : CubicResidueRegularValue u r⁻¹ a⁻¹ := by
  have hv : RatFunc.eval (RingHom.id F) u r ≠ 0 := hr.2 ▸ ha
  exact ⟨cubicResidueDenomRegular_inv_of_value_ne_zero hr.1 hv, by rw [cubicResidue_eval_inv_of_denom_regular_of_value_ne_zero hr.1 hv, hr.2]⟩
private lemma CubicResidueRegularValue.div {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : CubicResidueRegularValue u r a) (hs : CubicResidueRegularValue u s b) (hb : b ≠ 0) : CubicResidueRegularValue u (r/s) (a/b) := by
  simpa only [div_eq_mul_inv] using hr.mul (hs.inv hb)
private lemma CubicResidueRegularValue.pow {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : CubicResidueRegularValue u r a) (n : ℕ) : CubicResidueRegularValue u (r^n) (a^n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using CubicResidueRegularValue.const u 1
  | succ n ih => simpa only [pow_succ] using ih.mul hr
private lemma CubicResidueRegularValue.sum {F I : Type*} [Field F] {u : F} (s : Finset I)
    {r : I → RatFunc F} {a : I → F} (h : ∀ i ∈ s, CubicResidueRegularValue u (r i) (a i)) :
    CubicResidueRegularValue u (∑ i ∈ s, r i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, map_zero] using CubicResidueRegularValue.const u 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma cubicBetaFactor_regularValue_of_ne_zero_ne_one
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ξ : CubicUnitCharacters.Character K)
    (w : ℂ) (B : RatFunc ℂ) (b : ℂ) (hB : CubicResidueRegularValue w B b) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    CubicResidueRegularValue w (KPRankoneCubicScalarSum.betaFactor K ξ B)
      (KPRankoneCubicScalarSum.betaFactor K ξ b) := by
  classical
  have hA := (CubicResidueRegularValue.const w (CubicUnitCharacters.residueCard K : ℂ)⁻¹)
  have h1 := CubicResidueRegularValue.const w 1
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
    CubicResidueRegularValue w (rationalResidueScalar (KPExceptionalRaw.LocalField F q) dx)
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
  have hb (ε : CubicCharacters.Mu3) := (CubicResidueRegularValue.const w ((ε : ℂˣ) : ℂ)).mul ((CubicResidueRegularValue.var w).pow 2)
  have hb0 (ε : CubicCharacters.Mu3) : ((ε : ℂˣ) : ℂ)*w^2 ≠ 0 :=
    mul_ne_zero (ε : ℂˣ).ne_zero (pow_ne_zero _ hw0)
  have hb1 (ε : CubicCharacters.Mu3) : ((ε : ℂˣ) : ℂ)*w^2 ≠ 1 := by
    intro he
    have hp := congrArg (fun z : ℂ => z^3) he
    have hε : (((ε : ℂˣ) : ℂ))^3 = 1 := by
      exact congrArg Units.val ((mem_rootsOfUnity 3 (ε : ℂˣ)).mp ε.property)
    rw [mul_pow,hε,one_mul,← pow_mul,one_pow] at hp
    exact hw6 hp
  have hs := CubicResidueRegularValue.sum Finset.univ (fun ξ _ => CubicResidueRegularValue.sum Finset.univ (fun ε _ =>
    cubicBetaFactor_regularValue_of_ne_zero_ne_one K ξ w _ _ (hb ε) (hb0 ε) (hb1 ε)))
  have h := (CubicResidueRegularValue.const w (((integerMass K dx^2*KPCubicHaar.abs K (3 : K) : ℝ) : ℂ)/9)).mul hs
  simpa only [rationalResidueScalar,residueScalar,KPRankoneCubicScalarSum.finiteScalar,
    finsum_eq_sum_of_fintype] using h

theorem forward_regular_residue
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (hμ : 0 < integerMass (KPExceptionalRaw.LocalField F q) dx)
    (ω : (valuation (KPExceptionalRaw.LocalField F q)).integer)
    (hω : IsPrimitiveRoot ω 3)
    (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q))
    (hJ : J.toOpenSubgroup ≤ S.iwasawa.compact.toOpenSubgroup)
    (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus)
    (pRev : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus)
    (hp : IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .plus p)
    (hpRev : IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .minus pRev)
    (s z : ℂ) (hz : z ≠ 0) (hz3 : z ^ 3 = t (KPExceptionalRaw.LocalField F q) s)
    (hdp : denominator (KPExceptionalRaw.LocalField F q) .plus s ≠ 0)
    (hdm : denominator (KPExceptionalRaw.LocalField F q) .minus s ≠ 0) :
    (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev s).comp
      (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p s) =
        residueScalar (KPExceptionalRaw.LocalField F q) dx z • LinearMap.id := by
  classical
  let K := KPExceptionalRaw.LocalField F q

  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (residueCardinality K : ℂ) (by decide : 0 < 6)
  have hq0 : (residueCardinality K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation K)))).ne'
  have hα0 : α ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide)] at hα
    exact hq0 hα.symm
  let w := r K s / α
  have hr0 : r K s ≠ 0 := Complex.exp_ne_zero _
  have hw0 : w ≠ 0 := div_ne_zero hr0 hα0
  have hroot : α * w = r K s := by dsimp [w]; field_simp
  have htw : w^6 = t K s := by
    dsimp [w]
    rw [div_pow, hα]
    unfold t
    ring
  have ht1 : t K s ≠ 1 := by
    intro he
    apply hdp
    change 1 - t K s = 0
    rw [he, sub_self]
  have hw6 : w^6 ≠ 1 := htw ▸ ht1
  have hsc := residue_scalar_regular_eval F q dx w hw0 hw6

  have hsz : residueScalar K dx (w^2) = residueScalar K dx z := by
    unfold residueScalar
    exact KPRankoneCubicScalarSum.finiteScalar_cube_root_independent K ω.val
      (hω.map_of_injective (f := (valuation K).integer.subtype) Subtype.val_injective)
      (integerMass K dx) (KPCubicHaar.abs K (3 : K))
      (w^2) z (t K s) (pow_ne_zero _ hw0) hz
      (by rw [← pow_mul]; exact htw) hz3 ht1

  have hforward := forward_two_cell_residue F ζ hζ q S P dx hμ ω hω α hα J hJ p pRev hp hpRev
  have hplus := KPActualResidueSources.actual_level_composition_specialize_regular
    F ζ hζ q S P dx J hJ α hα p pRev (rationalResidueScalar K dx) .plus s w
      hw0 hroot hdp hdm hsc.1 (by simpa only [ite_true, KPRankOneGenericComposition.rationalStandard,
        KPRankOneGeneric.rationalStandard, KPRankOneGenericComposition.rationalDenominator,
        KPRankOneGeneric.rationalDenominator] using hforward)
  rw [hsc.2, hsz] at hplus
  exact hplus

end
end DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse

end

section

namespace DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse
open MeasureTheory ValuativeRel KPRankOneCubicResidueReduction
noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

 abbrev CubicResidueDenominatorRegular {F : Type*} [Field F] (u : F) (r : RatFunc F) : Prop :=
  r.denom.eval u ≠ 0

private lemma cubicResidueDenominatorRegular_constant {F : Type*} [Field F] (u c : F) : CubicResidueDenominatorRegular u (RatFunc.C c) := by
  simp [CubicResidueDenominatorRegular]
private lemma cubicResidueDenominatorRegular_indeterminate {F : Type*} [Field F] (u : F) : CubicResidueDenominatorRegular u (RatFunc.X : RatFunc F) := by
  simp [CubicResidueDenominatorRegular]
private lemma cubicResidueDenominatorRegular_add {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : CubicResidueDenominatorRegular u r) (hs : CubicResidueDenominatorRegular u s) : CubicResidueDenominatorRegular u (r+s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd r s) h)
private lemma cubicResidueDenominatorRegular_mul {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : CubicResidueDenominatorRegular u r) (hs : CubicResidueDenominatorRegular u s) : CubicResidueDenominatorRegular u (r*s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd r s) h)
private lemma cubicResidueDenominatorRegular_inv_of_value_ne_zero {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (_hr : CubicResidueDenominatorRegular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) : CubicResidueDenominatorRegular u r⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  intro h
  have hn := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_inv_dvd hr0) h
  apply hv
  simp [RatFunc.eval, hn]
private lemma cubicResidue_eval_inv_of_regular_nonzero {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (hr : CubicResidueDenominatorRegular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) :
    RatFunc.eval (RingHom.id F) u r⁻¹ = (RatFunc.eval (RingHom.id F) u r)⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  have hm := RatFunc.eval_mul (f := RingHom.id F) (a := u) hr (cubicResidueDenominatorRegular_inv_of_value_ne_zero hr hv)
  rw [mul_inv_cancel₀ hr0, RatFunc.eval_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

 abbrev cubicResidue_regularityAtValue {F : Type*} [Field F] (u : F) (r : RatFunc F) (v : F) : Prop :=
  CubicResidueDenominatorRegular u r ∧ RatFunc.eval (RingHom.id F) u r = v
private lemma cubicResidue_regularityAtValue.constant {F : Type*} [Field F] (u v : F) : cubicResidue_regularityAtValue u (RatFunc.C v) v :=
  ⟨cubicResidueDenominatorRegular_constant u v, by simp⟩
private lemma cubicResidue_regularityAtValue.indeterminate {F : Type*} [Field F] (u : F) : cubicResidue_regularityAtValue u RatFunc.X u :=
  ⟨cubicResidueDenominatorRegular_indeterminate u, by simp⟩
private lemma cubicResidue_regularityAtValue.add_values {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : cubicResidue_regularityAtValue u r a) (hs : cubicResidue_regularityAtValue u s b) : cubicResidue_regularityAtValue u (r+s) (a+b) := by
  refine ⟨cubicResidueDenominatorRegular_add hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_add (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma cubicResidue_regularityAtValue.mul_values {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : cubicResidue_regularityAtValue u r a) (hs : cubicResidue_regularityAtValue u s b) : cubicResidue_regularityAtValue u (r*s) (a*b) := by
  refine ⟨cubicResidueDenominatorRegular_mul hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_mul (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma cubicResidue_regularityAtValue.neg_value {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : cubicResidue_regularityAtValue u r a) : cubicResidue_regularityAtValue u (-r) (-a) := by
  simpa only [map_neg, map_one, neg_one_mul] using (cubicResidue_regularityAtValue.constant u (-1)).mul_values hr
private lemma cubicResidue_regularityAtValue.sub_values {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : cubicResidue_regularityAtValue u r a) (hs : cubicResidue_regularityAtValue u s b) : cubicResidue_regularityAtValue u (r-s) (a-b) := by
  simpa only [sub_eq_add_neg] using hr.add_values hs.neg_value
private lemma cubicResidue_regularityAtValue.inv_nonzero_value {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : cubicResidue_regularityAtValue u r a) (ha : a ≠ 0) : cubicResidue_regularityAtValue u r⁻¹ a⁻¹ := by
  have hv : RatFunc.eval (RingHom.id F) u r ≠ 0 := hr.2 ▸ ha
  exact ⟨cubicResidueDenominatorRegular_inv_of_value_ne_zero hr.1 hv, by rw [cubicResidue_eval_inv_of_regular_nonzero hr.1 hv, hr.2]⟩
private lemma cubicResidue_regularityAtValue.div_nonzero_value {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : cubicResidue_regularityAtValue u r a) (hs : cubicResidue_regularityAtValue u s b) (hb : b ≠ 0) : cubicResidue_regularityAtValue u (r/s) (a/b) := by
  simpa only [div_eq_mul_inv] using hr.mul_values (hs.inv_nonzero_value hb)
private lemma cubicResidue_regularityAtValue.nat_power {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : cubicResidue_regularityAtValue u r a) (n : ℕ) : cubicResidue_regularityAtValue u (r^n) (a^n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using cubicResidue_regularityAtValue.constant u 1
  | succ n ih => simpa only [pow_succ] using ih.mul_values hr
private lemma cubicResidue_regularityAtValue.finite_sum {F I : Type*} [Field F] {u : F} (s : Finset I)
    {r : I → RatFunc F} {a : I → F} (h : ∀ i ∈ s, cubicResidue_regularityAtValue u (r i) (a i)) :
    cubicResidue_regularityAtValue u (∑ i ∈ s, r i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, map_zero] using cubicResidue_regularityAtValue.constant u 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add_values (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma cubicBetaFactor_regularValue_of_nonzero_ne_one
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ξ : CubicUnitCharacters.Character K)
    (w : ℂ) (B : RatFunc ℂ) (b : ℂ) (hB : cubicResidue_regularityAtValue w B b) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    cubicResidue_regularityAtValue w (KPRankoneCubicScalarSum.betaFactor K ξ B)
      (KPRankoneCubicScalarSum.betaFactor K ξ b) := by
  classical
  have hA := (cubicResidue_regularityAtValue.constant w (CubicUnitCharacters.residueCard K : ℂ)⁻¹)
  have h1 := cubicResidue_regularityAtValue.constant w 1
  by_cases hξ : ξ=1
  · have hBi := hB.inv_nonzero_value hb0
    have hden : (1-b)*(1-b⁻¹) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hb1.symm)
        (sub_ne_zero.mpr (by intro h; exact hb1 (inv_eq_one.mp h.symm)))
    have h := ((h1.sub_values (hA.mul_values hB)).mul_values (h1.sub_values (hA.mul_values hBi))).div_nonzero_value
      ((h1.sub_values hB).mul_values (h1.sub_values hBi)) hden
    simpa only [KPRankoneCubicScalarSum.betaFactor,hξ,ite_true,
      KPRankoneCubicScalarSum.unramifiedFactor,map_one,map_inv₀,map_natCast] using h
  · simpa only [KPRankoneCubicScalarSum.betaFactor,hξ,ite_false,map_natCast,map_inv₀] using
      hA.nat_power (CubicUnitCharacters.conductor K ξ)

theorem residue_scalar_regular_evaluation
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
    (dx : Measure K) (w : ℂ) (hw : w ≠ 0) (hw6 : w ^ 6 ≠ 1) :
    (rationalResidueScalar K dx).denom.eval w ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) w (rationalResidueScalar K dx) =
        residueScalar K dx (w ^ 2) := by
  classical
  haveI := KPCubicHaar.cubeUnits_finiteIndex (K := K)
  haveI : Finite (CubicUnitCharacters.Character K) :=
    Nat.finite_of_card_ne_zero (by
      rw [KPCubicExpansion.card_unit_cubic_characters]
      exact Subgroup.index_ne_zero_of_finite)
  letI := Fintype.ofFinite (CubicUnitCharacters.Character K)
  letI := Fintype.ofFinite CubicCharacters.Mu3
  have hb (ε : CubicCharacters.Mu3) :=
    (cubicResidue_regularityAtValue.constant w ((ε : ℂˣ) : ℂ)).mul_values ((cubicResidue_regularityAtValue.indeterminate w).nat_power 2)
  have hb0 (ε : CubicCharacters.Mu3) : ((ε : ℂˣ) : ℂ)*w^2 ≠ 0 :=
    mul_ne_zero (ε : ℂˣ).ne_zero (pow_ne_zero _ hw)
  have hb1 (ε : CubicCharacters.Mu3) : ((ε : ℂˣ) : ℂ)*w^2 ≠ 1 := by
    intro he
    have hp := congrArg (fun z : ℂ => z^3) he
    have hε : (((ε : ℂˣ) : ℂ))^3 = 1 := by
      exact congrArg Units.val ((mem_rootsOfUnity 3 (ε : ℂˣ)).mp ε.property)
    rw [mul_pow,hε,one_mul,← pow_mul,one_pow] at hp
    exact hw6 hp
  have hs := cubicResidue_regularityAtValue.finite_sum Finset.univ (fun ξ _ => cubicResidue_regularityAtValue.finite_sum Finset.univ (fun ε _ =>
    cubicBetaFactor_regularValue_of_nonzero_ne_one K ξ w _ _ (hb ε) (hb0 ε) (hb1 ε)))
  have h := (cubicResidue_regularityAtValue.constant w (((integerMass K dx^2*KPCubicHaar.abs K (3 : K) : ℝ) : ℂ)/9)).mul_values hs
  simpa only [rationalResidueScalar,residueScalar,KPRankoneCubicScalarSum.finiteScalar,
    finsum_eq_sum_of_fintype] using h

end
end DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse

end

section

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

open KPLocalPrincipalSeries KPRankOneCenterInducedDiagonalComparison
open KPRankOneShellContinuation KPActualResidueSources
section WeightedContinuedTransport
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable (S : ActualKPBinding F ζ hζ q) (I : IwasawaData S.borel)
variable (E : CenterModule S.heisenberg ≃ₗ[ℂ] CenterModule S.heisenberg)
variable (hE : ∀ (f : CenterModule S.heisenberg) (h : KPExceptionalRaw.actualTorus F ζ hζ q),
  (E f).val h = normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) * f.val (S.borel.weyl h))
variable (J : CompactOpenLevel (KPRankOneOpenCellKernel.Cover F ζ hζ q))
variable (hJ : J.toOpenSubgroup ≤ I.compact.toOpenSubgroup)

private theorem continued_weighted_minus
    (μ : Measure (KPExceptionalRaw.LocalField F q))
    (p : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J .plus)
    (pRev : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J .minus)
    (hp : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ .plus p)
    (hpRev : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ .minus pRev)
    (s : ℂ)
    (hd : denominator (KPExceptionalRaw.LocalField F q) .minus s ≠ 0)
    (hd' : denominator (KPExceptionalRaw.LocalField F q) .plus (-s-1/3) ≠ 0)
    (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I .minus J) :
    actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .plus
      (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .minus pRev s φ) =
    centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .plus p (-s-1/3)
      (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .minus φ) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  apply Subtype.ext
  funext h
  have hn := actual_weighted_numerator_all_parameters F ζ hζ q S I E hE J hJ
    μ .minus pRev p hpRev hp s φ k h
  rw [actualWeightedLevelFlip_apply, hE]
  change normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) *
    ((denominator (KPExceptionalRaw.LocalField F q) .minus s)⁻¹ *
      ((centerEvaluate F ζ hζ q S.heisenberg S.borel I J .minus pRev
        (evaluationUnit (KPExceptionalRaw.LocalField F q) .minus s) φ).val.val k).val (S.borel.weyl h)) =
    (denominator (KPExceptionalRaw.LocalField F q) .plus (-s-1/3))⁻¹ *
      ((centerEvaluate F ζ hζ q S.heisenberg S.borel I J .plus p
        (evaluationUnit (KPExceptionalRaw.LocalField F q) .plus (-s-1/3))
        (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .minus φ)).val.val k).val h
  have cancel {a b c d e : ℂ} (hb : b ≠ 0) (hd : d ≠ 0)
      (hh : d*a*c=b*e) : a*(b⁻¹*c)=d⁻¹*e := by
    field_simp [hb,hd]
    linear_combination hh
  exact cancel hd hd' hn

private theorem continued_weighted_plus
    (μ : Measure (KPExceptionalRaw.LocalField F q))
    (p : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J .minus)
    (pRev : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J .plus)
    (hp : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ .minus p)
    (hpRev : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ .plus pRev)
    (s : ℂ)
    (hd : denominator (KPExceptionalRaw.LocalField F q) .plus s ≠ 0)
    (hd' : denominator (KPExceptionalRaw.LocalField F q) .minus (-s-1/3) ≠ 0)
    (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I .plus J) :
    actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .minus
      (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .plus pRev s φ) =
    centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .minus p (-s-1/3)
      (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .plus φ) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  apply Subtype.ext
  funext h
  have hn := actual_weighted_numerator_all_parameters F ζ hζ q S I E hE J hJ
    μ .plus pRev p hpRev hp s φ k h
  rw [actualWeightedLevelFlip_apply, hE]
  change normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) *
    ((denominator (KPExceptionalRaw.LocalField F q) .plus s)⁻¹ *
      ((centerEvaluate F ζ hζ q S.heisenberg S.borel I J .plus pRev
        (evaluationUnit (KPExceptionalRaw.LocalField F q) .plus s) φ).val.val k).val (S.borel.weyl h)) =
    (denominator (KPExceptionalRaw.LocalField F q) .minus (-s-1/3))⁻¹ *
      ((centerEvaluate F ζ hζ q S.heisenberg S.borel I J .minus p
        (evaluationUnit (KPExceptionalRaw.LocalField F q) .minus (-s-1/3))
        (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .plus φ)).val.val k).val h
  have cancel {a b c d e : ℂ} (hb : b ≠ 0) (hd : d ≠ 0)
      (hh : d*a*c=b*e) : a*(b⁻¹*c)=d⁻¹*e := by
    field_simp [hb,hd]
    linear_combination hh
  exact cancel hd hd' hn

include E hE hJ in

private theorem center_reverse_from_reflected_forward
    (μ : Measure (KPExceptionalRaw.LocalField F q))
    (p : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J .plus)
    (pRev : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J .minus)
    (hp : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ .plus p)
    (hpRev : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ .minus pRev)
    (s c : ℂ)
    (hd : denominator (KPExceptionalRaw.LocalField F q) .minus s ≠ 0)
    (hdp : denominator (KPExceptionalRaw.LocalField F q) .plus s ≠ 0)
    (hdu : denominator (KPExceptionalRaw.LocalField F q) .minus (-s-1/3) ≠ 0)
    (hdup : denominator (KPExceptionalRaw.LocalField F q) .plus (-s-1/3) ≠ 0)
    (hf : (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .minus pRev (-s-1/3)).comp
      (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .plus p (-s-1/3)) =
        c • LinearMap.id) :
    (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .plus p s).comp
      (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .minus pRev s) =
        c • LinearMap.id := by
  apply LinearMap.ext
  intro φ
  apply (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .minus).injective
  change actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .minus
    (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .plus p s
      (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I J .minus pRev s φ)) =
    actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .minus (c • φ)
  rw [continued_weighted_plus F ζ hζ q S I E hE J hJ μ pRev p hpRev hp s hdp hdu,
    continued_weighted_minus F ζ hζ q S I E hE J hJ μ p pRev hp hpRev s hd hdup]
  have h := congrArg (fun M => M (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .minus φ)) hf
  change _ = c • actualWeightedLevelFlip F ζ hζ q S I E hE J hJ .minus φ at h
  rw [map_smul]
  apply Subtype.ext
  exact congrArg Subtype.val h

end WeightedContinuedTransport

open scoped TensorProduct

private theorem transported_numerators
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q))
    (ε : Sign)
    (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J ε)
    (hp : IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx ε p) :
    IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel S.iwasawa J dx ε
      (centerLevelLaurentTransport F ζ hζ q S.heisenberg S.borel P S.iwasawa J ε p) := by
  classical
  obtain ⟨Jτ⟩ := KPRankOneShellContinuation.actual_exists_tauStandardFamily F ζ hζ q
    (KPLocalExceptionalConstruction.actualCanonicalInducing F ζ hζ q S) P dx
  exact centerLevelLaurentTransport_isNumerator F ζ hζ q S.heisenberg S.borel P
    S.iwasawa J dx Jτ ε p hp

private theorem forward_scalar_center_transport
    {Vp Vm W Cp Cm : Type*}
    [AddCommMonoid Vp] [Module ℂ Vp] [AddCommMonoid Vm] [Module ℂ Vm]
    [AddCommMonoid W] [Module ℂ W]
    [AddCommMonoid Cp] [Module ℂ Cp] [AddCommMonoid Cm] [Module ℂ Cm]
    (ep : Vp ⊗[ℂ] W ≃ₗ[ℂ] Cp) (em : Vm ⊗[ℂ] W ≃ₗ[ℂ] Cm)
    (A : Vp →ₗ[ℂ] Vm) (B : Vm →ₗ[ℂ] Vp) (c : ℂ)
    (hc : B.comp A = c • LinearMap.id) :
    (ep.toLinearMap.comp ((TensorProduct.map B LinearMap.id).comp em.symm.toLinearMap)).comp
      (em.toLinearMap.comp ((TensorProduct.map A LinearMap.id).comp ep.symm.toLinearMap)) =
        c • LinearMap.id := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change ep (((TensorProduct.map B LinearMap.id).comp (TensorProduct.map A LinearMap.id))
    (ep.symm f)) = _
  rw [← TensorProduct.map_comp, hc, LinearMap.id_comp, TensorProduct.map_smul_left]
  simp

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem continued_reverse_from_reflected_forward
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q))
    (hJ : J.toOpenSubgroup ≤ S.iwasawa.compact.toOpenSubgroup)
    (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus)
    (pRev : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus)
    (hp : IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .plus p)
    (hpRev : IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .minus pRev)
    (s c : ℂ)
    (hd : denominator (KPExceptionalRaw.LocalField F q) .minus s ≠ 0)
    (hdp : denominator (KPExceptionalRaw.LocalField F q) .plus s ≠ 0)
    (hdu : denominator (KPExceptionalRaw.LocalField F q) .minus (-s-1/3) ≠ 0)
    (hdup : denominator (KPExceptionalRaw.LocalField F q) .plus (-s-1/3) ≠ 0)
    (hf : (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev (-s-1/3)).comp
      (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p (-s-1/3)) =
        c • LinearMap.id) :
    (centerContinuedLevel F ζ hζ q S.heisenberg S.borel S.iwasawa J .plus
      (centerLevelLaurentTransport F ζ hζ q S.heisenberg S.borel P S.iwasawa J .plus p) s).comp
      (centerContinuedLevel F ζ hζ q S.heisenberg S.borel S.iwasawa J .minus
        (centerLevelLaurentTransport F ζ hζ q S.heisenberg S.borel P S.iwasawa J .minus pRev) s) =
        c • LinearMap.id := by
  obtain ⟨E,hE,_,_⟩ := actual_center_weighted_weyl F ζ hζ q S
  apply center_reverse_from_reflected_forward F ζ hζ q S S.iwasawa E hE J hJ dx _ _
    (transported_numerators F ζ hζ q S P dx J .plus p hp)
    (transported_numerators F ζ hζ q S P dx J .minus pRev hpRev) s c hd hdp hdu hdup
  rw [centerLevelLaurentTransport_continued, centerLevelLaurentTransport_continued]
  exact forward_scalar_center_transport
    (centerLevelTensorEquiv F ζ hζ q S.heisenberg S.borel P S.iwasawa .plus J)
    (centerLevelTensorEquiv F ζ hζ q S.heisenberg S.borel P S.iwasawa .minus J) _ _ c hf

private theorem scalar_of_tensor_map
    {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    (M : V →ₗ[ℂ] V) (c : ℂ)
    (hM : TensorProduct.map M (LinearMap.id : W →ₗ[ℂ] W) = c • LinearMap.id) :
    M = c • LinearMap.id := by
  obtain ⟨w,hw⟩ := exists_ne (0 : W)
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hw
  let E : V ⊗[ℂ] W →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap.comp
    (TensorProduct.map LinearMap.id ℓ)
  ext v
  have h := congrArg (fun N : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W => E (N (v ⊗ₜ[ℂ] w))) hM
  simp only [E,LinearMap.comp_apply,TensorProduct.map_tmul,LinearMap.id_apply,
    LinearMap.smul_apply,map_smul,hℓ] at h
  simpa only [LinearEquiv.coe_coe,TensorProduct.rid_tmul,one_smul,
    LinearMap.smul_apply,LinearMap.id_apply] using h

private theorem reverse_scalar_of_center_transport
    {Vp Vm W Cp Cm : Type*}
    [AddCommMonoid Vp] [Module ℂ Vp] [AddCommMonoid Vm] [Module ℂ Vm]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    [AddCommMonoid Cp] [Module ℂ Cp] [AddCommMonoid Cm] [Module ℂ Cm]
    (ep : Vp ⊗[ℂ] W ≃ₗ[ℂ] Cp) (em : Vm ⊗[ℂ] W ≃ₗ[ℂ] Cm)
    (A : Vp →ₗ[ℂ] Vm) (B : Vm →ₗ[ℂ] Vp) (c : ℂ)
    (hc : (em.toLinearMap.comp ((TensorProduct.map A LinearMap.id).comp ep.symm.toLinearMap)).comp
      (ep.toLinearMap.comp ((TensorProduct.map B LinearMap.id).comp em.symm.toLinearMap)) =
        c • LinearMap.id) : A.comp B = c • LinearMap.id := by
  apply scalar_of_tensor_map (W := W) (A.comp B) c
  apply LinearMap.ext
  intro t
  have h := congrArg (fun M => em.symm (M (em t))) hc
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
    LinearMap.smul_apply,LinearMap.id_apply,map_smul] at h
  change ((TensorProduct.map A LinearMap.id).comp (TensorProduct.map B LinearMap.id)) t = _ at h
  rw [← TensorProduct.map_comp] at h
  simpa only [LinearMap.id_comp,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.id_apply] using h

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem continued_reverse_scalar
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q))
    (hJ : J.toOpenSubgroup ≤ S.iwasawa.compact.toOpenSubgroup)
    (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus)
    (pRev : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus)
    (hp : IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .plus p)
    (hpRev : IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .minus pRev)
    (s c : ℂ)
    (hd : denominator (KPExceptionalRaw.LocalField F q) .minus s ≠ 0)
    (hdp : denominator (KPExceptionalRaw.LocalField F q) .plus s ≠ 0)
    (hdu : denominator (KPExceptionalRaw.LocalField F q) .minus (-s-1/3) ≠ 0)
    (hdup : denominator (KPExceptionalRaw.LocalField F q) .plus (-s-1/3) ≠ 0)
    (hf : (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev (-s-1/3)).comp
      (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p (-s-1/3)) =
        c • LinearMap.id) :
    (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p s).comp
      (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev s) =
        c • LinearMap.id := by
  have hc := continued_reverse_from_reflected_forward F ζ hζ q S P dx J hJ p pRev hp hpRev
    s c hd hdp hdu hdup hf
  rw [centerLevelLaurentTransport_continued, centerLevelLaurentTransport_continued] at hc
  haveI : Nontrivial (InducedModule P) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [tau_finrank_eq_index S.heisenberg P]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  letI : Nontrivial (Multiplicity S.heisenberg P) := inferInstance
  exact reverse_scalar_of_center_transport
    (centerLevelTensorEquiv F ζ hζ q S.heisenberg S.borel P S.iwasawa .plus J)
    (centerLevelTensorEquiv F ζ hζ q S.heisenberg S.borel P S.iwasawa .minus J) _ _ c hc

private theorem residue_scalar_inverse
    (dx : Measure (KPExceptionalRaw.LocalField F q))
    (ω : (valuation (KPExceptionalRaw.LocalField F q)).integer)
    (hω : IsPrimitiveRoot ω 3)
    (z z' t₀ : ℂ) (hz : z ≠ 0) (hz' : z' ≠ 0)
    (hzt : z ^ 3 = t₀) (hz't : z' ^ 3 = t₀⁻¹) (ht : t₀ ≠ 1) :
    residueScalar (KPExceptionalRaw.LocalField F q) dx z' =
      residueScalar (KPExceptionalRaw.LocalField F q) dx z := by
  have hω' : IsPrimitiveRoot (ω : KPExceptionalRaw.LocalField F q) 3 :=
    hω.map_of_injective (f := (valuation (KPExceptionalRaw.LocalField F q)).integer.subtype)
      Subtype.val_injective
  have hti : t₀⁻¹ ≠ 1 := by simpa using ht
  rw [residueScalar, residueScalar,
    KPRankoneCubicScalarSum.finiteScalar_eq _ _ hω' _ _ z' t₀⁻¹ hz' hz't hti,
    KPRankoneCubicScalarSum.finiteScalar_eq _ _ hω' _ _ z t₀ hz hzt ht,
    inv_inv]
  ring

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in

theorem reverse_two_cell_residue
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (hμ : 0 < integerMass (KPExceptionalRaw.LocalField F q) dx)
    (ω : (valuation (KPExceptionalRaw.LocalField F q)).integer)
    (hω : IsPrimitiveRoot ω 3)
    (α : ℂ) (hα : α ^ 6 = (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)) :
    ∀ (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q)),
      (J.toOpenSubgroup : Subgroup (KPExceptionalRaw.ActualCover F ζ hζ q)) ≤
        S.iwasawa.compact.toOpenSubgroup →
      ∀ (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus)
        (pRev : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus),
      IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .plus p →
      IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .minus pRev →
      (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
          (RatFunc.C α * RatFunc.X)).comp
        (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
          (RatFunc.C α * RatFunc.X)) =
        rationalResidueScalar (KPExceptionalRaw.LocalField F q) dx • LinearMap.id := by
  classical
  intro J hJ p pRev hp hpRev
  apply Reverse.rational_composition_of_regular_values F ζ hζ q S P α hα
    J p pRev (rationalResidueScalar (KPExceptionalRaw.LocalField F q) dx) .minus
  intro w hw hw6 hC r₀ hr₀
  simp only [show Sign.minus ≠ Sign.plus from by decide, ite_false]
  let s := KPRankOneReverseRegulatorShells.additiveParameter F q r₀
  obtain ⟨hd, hdp, hdu, hdup, hz3, ht, z', hz', hz'3, hz'u⟩ :=
    Reverse.reflected_regular_dictionary F q α w hα hw hw6 r₀ hr₀
  have hf := Reverse.forward_regular_residue F ζ hζ q S P dx hμ ω hω
    J hJ p pRev hp hpRev (-s-1/3) z' hz' hz'u hdup hdu
  have hc := continued_reverse_scalar F ζ hζ q S P dx J hJ p pRev hp hpRev
    s (residueScalar (KPExceptionalRaw.LocalField F q) dx z') hd hdp hdu hdup hf
  have hs := residue_scalar_inverse F q dx ω hω (w^2) z'
    (t (KPExceptionalRaw.LocalField F q) s) (pow_ne_zero _ hw) hz' hz3 hz'3 ht
  rw [hs, ← (Reverse.residue_scalar_regular_evaluation
    (KPExceptionalRaw.LocalField F q) dx w hw hw6).2] at hc
  exact hc

end
end DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps

end
