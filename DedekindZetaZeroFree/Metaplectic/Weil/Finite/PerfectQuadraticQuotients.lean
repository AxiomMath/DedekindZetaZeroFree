module

public import DedekindZetaZeroFree.Metaplectic.Weil.Finite.AdmissibleQuadraticBalls
public import DedekindZetaZeroFree.CharacterSums.Gauss.FiniteQuadraticNormalization

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

theorem localFiniteQuadraticPhase_respects
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (b : (v.adicCompletion F)ˣ) (hb : (b : v.adicCompletion F) = 2 * (a : v.adicCompletion F))
    (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m)
    (x y : localScaledBallDual F v b m)
    (hxy : QuotientAddGroup.leftRel
      ((finiteCompletionBall F v m).comap (localScaledBallDual F v b m).subtype) x y) :
    localFiniteCharacter F v ((a : v.adicCompletion F) * (x : v.adicCompletion F) ^ 2) =
      localFiniteCharacter F v ((a : v.adicCompletion F) * (y : v.adicCompletion F) ^ 2) := by
  have hh : -(x : v.adicCompletion F) + (y : v.adicCompletion F) ∈
      finiteCompletionBall F v m :=
    show -x + y ∈ (finiteCompletionBall F v m).comap
      (localScaledBallDual F v b m).subtype from QuotientAddGroup.leftRel_apply.mp hxy
  have hc : localFiniteCharacter F v
      ((-(x : v.adicCompletion F) + y) * ((b : v.adicCompletion F) * x)) = 1 :=
    (mem_localFiniteAnnihilator F v _ _).mp x.property _ hh
  have he : (a : v.adicCompletion F) * (y : v.adicCompletion F) ^ 2 =
      (a : v.adicCompletion F) * (x : v.adicCompletion F) ^ 2 +
      (a : v.adicCompletion F) * (-(x : v.adicCompletion F) + y) ^ 2 +
      (-(x : v.adicCompletion F) + y) * ((b : v.adicCompletion F) * x) := by
    rw [hb]
    ring
  rw [he, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hq _ hh, hc,
    mul_one, mul_one]

def localFinitePerfectQuadraticPhase
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (b : (v.adicCompletion F)ˣ) (hb : (b : v.adicCompletion F) = 2 * (a : v.adicCompletion F))
    (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m) :
    localScaledBallDualQuotient F v b m → Circle :=
  Quotient.lift
    (fun x : localScaledBallDual F v b m =>
      localFiniteCharacter F v ((a : v.adicCompletion F) * (x : v.adicCompletion F) ^ 2))
    (localFiniteQuadraticPhase_respects F v a b hb m hq hHL)

@[simp] theorem localFinitePerfectQuadraticPhase_mk
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (b : (v.adicCompletion F)ˣ) (hb : (b : v.adicCompletion F) = 2 * (a : v.adicCompletion F))
    (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m)
    (x : localScaledBallDual F v b m) :
    localFinitePerfectQuadraticPhase F v a b hb m hq hHL (QuotientAddGroup.mk x) =
      localFiniteCharacter F v ((a : v.adicCompletion F) * (x : v.adicCompletion F) ^ 2) := by
  rfl

def localFinitePerfectQuadraticPolar
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (b : (v.adicCompletion F)ˣ) (hb : (b : v.adicCompletion F) = 2 * (a : v.adicCompletion F))
    (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m)
    (x y : localScaledBallDualQuotient F v b m) : Circle :=
  finiteQuadraticPolarization (localFinitePerfectQuadraticPhase F v a b hb m hq hHL) x y

theorem localFinitePerfectQuadraticPolar_mk
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (b : (v.adicCompletion F)ˣ) (hb : (b : v.adicCompletion F) = 2 * (a : v.adicCompletion F))
    (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m)
    (x y : localScaledBallDual F v b m) :
    localFinitePerfectQuadraticPolar F v a b hb m hq hHL
        (QuotientAddGroup.mk x) (QuotientAddGroup.mk y) =
      localFiniteCharacter F v ((b : v.adicCompletion F) *
        (x : v.adicCompletion F) * (y : v.adicCompletion F)) := by
  have he : (a : v.adicCompletion F) * ((x : v.adicCompletion F) + y) ^ 2 =
      (a : v.adicCompletion F) * (x : v.adicCompletion F) ^ 2 +
      (a : v.adicCompletion F) * (y : v.adicCompletion F) ^ 2 +
      (b : v.adicCompletion F) * x * y := by
    rw [hb]
    ring
  simp only [localFinitePerfectQuadraticPolar, finiteQuadraticPolarization,
    ← QuotientAddGroup.mk_add, localFinitePerfectQuadraticPhase_mk,
    AddSubgroup.coe_add, he, AddChar.map_add_eq_mul]
  simp only [mul_div_cancel_left]

theorem weil_finite_perfect_quadratic_quotient
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (b : (v.adicCompletion F)ˣ) (hb : (b : v.adicCompletion F) = 2 * (a : v.adicCompletion F))
    (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m) :
    let G := localScaledBallDualQuotient F v b m
    let q := localFinitePerfectQuadraticPhase F v a b hb m hq hHL
    let B := localFinitePerfectQuadraticPolar F v a b hb m hq hHL
    q 0 = 1 ∧
      (∀ x x' y : G, B (x + x') y = B x y * B x' y) ∧
      (∀ x y y' : G, B x (y + y') = B x y * B x y') ∧
      (∀ x : G, (∀ y : G, B x y = 1) → x = 0) ∧
      (letI : Finite G := finite_localScaledBallDualQuotient F v b m hHL
       letI : Fintype G := Fintype.ofFinite G
       ‖((localNormalizedHaar F v
           (finiteCompletionBall F v m : Set (v.adicCompletion F))).toReal : ℂ) *
           ∑ g : G, (q g : ℂ)‖ = ‖(b : v.adicCompletion F)‖ ^ (-(1 / 2 : ℝ))) := by
  let G := localScaledBallDualQuotient F v b m
  let q := localFinitePerfectQuadraticPhase F v a b hb m hq hHL
  let B := localFinitePerfectQuadraticPolar F v a b hb m hq hHL
  have hzero : q 0 = 1 := by
    change localFinitePerfectQuadraticPhase F v a b hb m hq hHL
      (QuotientAddGroup.mk (0 : localScaledBallDual F v b m)) = 1
    rw [localFinitePerfectQuadraticPhase_mk]
    simp
  have hleft : ∀ x x' y : G, B (x + x') y = B x y * B x' y := by
    intro x x' y
    induction x using QuotientAddGroup.induction_on with | H x =>
      induction x' using QuotientAddGroup.induction_on with | H x' =>
        induction y using QuotientAddGroup.induction_on with | H y =>
          change localFinitePerfectQuadraticPolar F v a b hb m hq hHL _ _ = _
          rw [← QuotientAddGroup.mk_add]
          simp only [ localFinitePerfectQuadraticPolar_mk,
            AddSubgroup.coe_add, mul_add, add_mul, AddChar.map_add_eq_mul, B]
  have hright : ∀ x y y' : G, B x (y + y') = B x y * B x y' := by
    intro x y y'
    induction x using QuotientAddGroup.induction_on with | H x =>
      induction y using QuotientAddGroup.induction_on with | H y =>
        induction y' using QuotientAddGroup.induction_on with | H y' =>
          change localFinitePerfectQuadraticPolar F v a b hb m hq hHL _ _ = _
          rw [← QuotientAddGroup.mk_add]
          simp only [ localFinitePerfectQuadraticPolar_mk,
            AddSubgroup.coe_add, mul_add, AddChar.map_add_eq_mul, B]
  have hnondeg : ∀ x : G, (∀ y : G, B x y = 1) → x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with | H x =>
      intro hx
      apply (QuotientAddGroup.eq_zero_iff x).mpr
      change (x : v.adicCompletion F) ∈ finiteCompletionBall F v m
      rw [← localFiniteAnnihilator_map_localScaledBallDual F v b m,
        mem_localFiniteAnnihilator]
      intro z hz
      obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hz
      have ht := hx (QuotientAddGroup.mk (⟨y, hy⟩ : localScaledBallDual F v b m))
      change localFinitePerfectQuadraticPolar F v a b hb m hq hHL _ _ = 1 at ht
      rw [localFinitePerfectQuadraticPolar_mk] at ht
      convert ht using 1
      change localFiniteCharacter F v ((b : v.adicCompletion F) * y * x) = _
      congr 1
      ring
  refine ⟨hzero, hleft, hright, hnondeg, ?_⟩
  letI : Finite G := finite_localScaledBallDualQuotient F v b m hHL
  letI : Fintype G := Fintype.ofFinite G
  have hnd : ∀ x : G, x ≠ 0 → ∃ y : G, finiteQuadraticPolarization q x y ≠ 1 := by
    intro x hx
    by_contra hn
    apply hx
    apply hnondeg x
    change ∀ y : G, finiteQuadraticPolarization q x y = 1
    simpa only [not_exists, not_not] using hn
  have hgauss := weil_finite_quadratic_gauss_modulus q hzero hleft hright hnd
  let M := (localNormalizedHaar F v
    (finiteCompletionBall F v m : Set (v.adicCompletion F))).toReal
  let N := (localNormalizedHaar F v
    (localScaledBallDual F v b m : Set (v.adicCompletion F))).toReal
  have hM : 0 < M := (localScaledBallDual_masses_pos_finite F v b m).1
  have hcard : (Fintype.card G : ℝ) = N / M := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_localScaledBallDualQuotient F v b m hHL
  have hprod : M * N = ‖(b : v.adicCompletion F)‖⁻¹ :=
    localScaledBallDual_mass_product F v b m
  have hsq : ‖(M : ℂ) * ∑ g : G, (q g : ℂ)‖ ^ 2 =
      ‖(b : v.adicCompletion F)‖⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, mul_pow,
      hgauss, hcard]
    calc
      M ^ 2 * (N / M) = M * N := by
        field_simp [hM.ne']
        <;> ring
      _ = _ := hprod
  have hrpow : (‖(b : v.adicCompletion F)‖ ^ (-(1 / 2 : ℝ))) ^ 2 =
      ‖(b : v.adicCompletion F)‖⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    norm_num [Real.rpow_neg_one]
  have hrpos := Real.rpow_nonneg (norm_nonneg (b : v.adicCompletion F)) (-(1 / 2 : ℝ))
  change ‖(M : ℂ) * ∑ g : G, (q g : ℂ)‖ = _
  nlinarith [norm_nonneg ((M : ℂ) * ∑ g : G, (q g : ℂ))]

end DedekindZetaZeroFree

end
