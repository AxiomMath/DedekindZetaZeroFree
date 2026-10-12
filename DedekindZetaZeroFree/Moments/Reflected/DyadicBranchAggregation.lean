module

public import DedekindZetaZeroFree.Moments.Reflected.ActivePrimeSubpowerMass
public import DedekindZetaZeroFree.Arithmetic.Units.SUnitPowerQuotientCoordinates
public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.PowerfulIdeals
public import DedekindZetaZeroFree.LargeSieve.Bilinear.ProfiledDyadicBlock

@[expose] public section

section

namespace DedekindZetaZeroFree.RMDyadicSieveAggregation
noncomputable section
open scoped NumberField BigOperators Classical
open ThetaBranch ThetaPhaseSeparation

variable {F : Type} [Field F] [NumberField F]

private theorem unit_finite (A : SArithmeticData F) : Finite A.UnitQuotient := by
  letI := SArithmeticData.sunitSixthPowerQuotient_finite F A
  exact Finite.of_equiv (PowerQuotient A.Rˣ 6)
    (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv A.U A.Rˣ 6 A.unitEquiv).symm.toEquiv

 abbrev Active (A : SArithmeticData F) (h : A.Exterior) :=
  {f : ExteriorSquarefreeIdeal A.cS // f.val.val ∈ activeSquarefreeDivisors h.val}

private theorem active_finite (A : SArithmeticData F) (h : A.Exterior) :
    Finite (Active A h) := by
  apply Finite.of_injective (fun f : Active A h =>
    (⟨f.val.val.val, f.property⟩ : {f // f ∈ activeSquarefreeDivisors h.val}))
  intro i j hij
  have he : i.val.val.val = j.val.val.val := congrArg
    (fun f : {f // f ∈ activeSquarefreeDivisors h.val} => f.val) hij
  exact Subtype.ext (Subtype.ext (Subtype.ext he))

private theorem beta_zero {A : SArithmeticData F} (f : ExteriorSquarefreeIdeal A.cS)
    (a : supportedExteriorIdeals f) : betaIdealTerm f 0 a = betaIdeal f a.val.val := by
  simp [betaIdealTerm]

private theorem norm_bounds {A : SArithmeticData F} (a c n : A.Exterior)
    {R : ℝ} (hr : rowNorm a c n ≤ R) :
    idealNorm c.val ≤ R ∧ idealNorm n.val ≤ R := by
  have ha := idealNorm_ge_one a.val a.property.1
  have hc := idealNorm_ge_one c.val c.property.1
  have hn := idealNorm_ge_one n.val n.property.1
  have hn3 : 1 ≤ idealNorm n.val ^ 3 := one_le_pow₀ hn
  have hnn : idealNorm n.val ≤ idealNorm n.val ^ 3 := by
    calc idealNorm n.val = idealNorm n.val * 1 ^ 2 := by ring
         _ ≤ idealNorm n.val * idealNorm n.val ^ 2 := by gcongr
         _ = _ := by ring
  change idealNorm a.val * idealNorm c.val * idealNorm n.val ^ 3 ≤ R at hr
  constructor
  · apply le_trans _ hr
    calc idealNorm c.val = 1 * idealNorm c.val * 1 := by ring
         _ ≤ idealNorm a.val * idealNorm c.val * idealNorm n.val ^ 3 := by gcongr
  · apply le_trans hnn
    apply le_trans _ hr
    calc idealNorm n.val ^ 3 = 1 * 1 * idealNorm n.val ^ 3 := by ring
         _ ≤ idealNorm a.val * idealNorm c.val * idealNorm n.val ^ 3 := by gcongr

private theorem dyad_count (R : ℝ) (hR : 1 ≤ R) :
    (Nat.log 2 ⌊R⌋₊ + 1 : ℝ) ≤ Real.log (2 * R) / Real.log 2 := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor : ⌊R⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hR)
    omega
  have hp : (2 : ℝ) ^ Nat.log 2 ⌊R⌋₊ ≤ R := by
    calc
      (2 : ℝ) ^ Nat.log 2 ⌊R⌋₊ ≤ (⌊R⌋₊ : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 hfloor
      _ ≤ R := Nat.floor_le hRp.le
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 ⌊R⌋₊) hp
  rw [Real.log_pow] at hl
  rw [le_div_iff₀ hlog2, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRp.ne']
  nlinarith

private theorem active_sum_le (A : SArithmeticData F) (h : A.Exterior)
    (K b : ℝ) (hK : activeEulerSum h.val 0 ≤ K * Real.rpow (idealNorm h.val) b) :
    (∑' f : Active A h, eulerIdeal f.val 0) ≤ K * Real.rpow (idealNorm h.val) b := by
  letI := active_finite A h
  letI := Fintype.ofFinite (Active A h)
  rw [tsum_fintype]
  apply le_trans (b := activeEulerSum h.val 0) _ hK
  apply Finset.sum_le_sum_of_injOn (fun f : Active A h => f.val.val.val)
  · intro i _ j _ hij
    exact Subtype.ext (Subtype.ext (Subtype.ext hij))
  · intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    exact i.property
  · intro f _
    exact le_of_eq (activeEulerFactor_eq_eulerIdeal f.val 0).symm
  · intro f hf _
    exact activeEulerFactor_nonneg f
      ((mem_activeSquarefreeDivisors_iff h.val h.property.1 f).mp hf).1 0 (le_refl 0)

theorem frozen_dyadic_weight_bound (A : SArithmeticData F)
    (b : ℝ) (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ (h : A.Exterior) (R : ℝ)
      (s : Finset (RMSeparatedExpansion.Index A h)), 1 ≤ R →
      (∀ i ∈ s, rowNorm i.1.val.a i.2.val i.1.val.n ≤ R) →
      (∑ j ∈ s.image (fun i => (i.1, Nat.log 2 (Ideal.absNorm i.2.val.val))),
        betaIdeal (RMSeparatedExpansion.activeSupport A j.1.val) j.1.val.a.val /
          A.exteriorNorm j.1.val.n) ≤
        M * Real.rpow (A.exteriorNorm h) b * Real.log (2 * R) ^ 2 := by
  letI := unit_finite A
  letI := Fintype.ofFinite A.UnitQuotient
  obtain ⟨Ka, hKa, ha⟩ := active_subpower (F := F) b hb
  obtain ⟨K, Kn, hK, hKn, hn⟩ := ideal_counting_harmonic_bounds F
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let Cu : ℝ := Nat.card A.UnitQuotient + 1
  have hCu : 0 < Cu := by dsimp [Cu]; positivity
  refine ⟨Ka * Kn * Cu / Real.log 2, by positivity, ?_⟩
  intro h R s hR hs
  letI := active_finite A h
  letI := Fintype.ofFinite (Active A h)
  let N := ↥((Set.univ : Set (NonzeroIdeal F)) ∩ normBoundedIdeals F R)
  letI : Finite N := ((normBoundedIdeals_finite F R).subset Set.inter_subset_right).to_subtype
  letI := Fintype.ofFinite N
  let L := Nat.log 2 ⌊R⌋₊ + 1
  let Y := N × A.UnitQuotient × Fin L
  let J := Σ f : Active A h, Y × supportedExteriorIdeals f.val
  let g : Y → ℝ := fun y => (idealNorm y.1.val.val)⁻¹
  let W : J → ℝ := fun j => g j.2.1 * betaIdealTerm j.1.val 0 j.2.2
  have hg : ∀ y, 0 ≤ g y := by intro y; dsimp [g]; unfold idealNorm; positivity
  have hw : ∀ j, 0 ≤ W j := by
    intro j
    exact mul_nonneg (hg _) (betaIdealTerm_nonneg _ 0 (le_refl 0) _)
  have hws : Summable W := by
    apply (summable_sigma_of_nonneg hw).mpr
    refine ⟨?_, Summable.of_finite⟩
    intro f
    apply (summable_prod_of_nonneg (fun j => hw ⟨f, j⟩)).mpr
    exact ⟨fun y => (betaIdealTerm_summable f.val 0 (le_refl 0)).mul_left (g y),
      Summable.of_finite⟩
  have hwt : (∑' j, W j) =
      (∑' f : Active A h, eulerIdeal f.val 0) * (∑' y, g y) := by
    rw [hws.tsum_sigma]
    have he (f : Active A h) :
        (∑' z : Y × supportedExteriorIdeals f.val, W ⟨f, z⟩) =
          eulerIdeal f.val 0 * (∑' y, g y) := by
      have hz : Summable (fun z : Y × supportedExteriorIdeals f.val => W ⟨f,z⟩) :=
        ((summable_sigma_of_nonneg hw).mp hws).1 f
      rw [hz.tsum_prod]
      simp only [W, tsum_mul_left, betaIdealTerm_tsum _ 0 (le_refl 0)]
      rw [tsum_mul_right, mul_comm]
    simp only [he, tsum_mul_right]
  have hgt : (∑' y, g y) =
      (Nat.card A.UnitQuotient : ℝ) * L * idealHarmonicSum (Set.univ : Set (NonzeroIdeal F)) R := by
    rw [(Summable.of_finite (f := g)).tsum_prod]
    have he (n : N) : (∑' z : A.UnitQuotient × Fin L, g (n,z)) =
        (Nat.card A.UnitQuotient : ℝ) * L * (idealNorm n.val.val)⁻¹ := by
      simp [g, tsum_fintype, Fintype.sum_prod_type, ← Nat.card_eq_fintype_card,
        Nat.card_fin, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    simp only [he, tsum_mul_left]
    rfl
  let t := s.image (fun i => (i.1, Nat.log 2 (Ideal.absNorm i.2.val.val)))
  let e : t → J := fun j =>
    ⟨⟨RMSeparatedExpansion.activeSupport A j.val.1.val,
      (mem_activeSquarefreeDivisors_iff h.val h.property.1 _).mpr
        ⟨j.val.1.val.f.property.1, j.val.1.val.f_squarefree,
          by simpa only [RMSeparatedExpansion.activeSupport, j.val.1.property] using j.val.1.val.f_divides_radical⟩⟩,
      ((⟨⟨j.val.1.val.n.val, j.val.1.val.n.property.1⟩, by
        obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp j.property
        have hn' := (norm_bounds i.1.val.a i.2.val i.1.val.n (hs i hi)).2
        refine ⟨Set.mem_univ _, ?_⟩
        change idealNorm j.val.1.val.n.val ≤ R
        simpa only [← hij] using hn'⟩,
        j.val.1.val.epsilon, ⟨j.val.2, by
          obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp j.property
          have hc' := (norm_bounds i.1.val.a i.2.val i.1.val.n (hs i hi)).1
          have hk := Nat.log_monotone (b := 2) (Nat.le_floor hc')
          change j.val.2 < Nat.log 2 ⌊R⌋₊ + 1
          simpa only [← hij] using Nat.lt_succ_of_le hk⟩),
        ⟨j.val.1.val.a, j.val.1.val.a_supported⟩)⟩
  have hei : Function.Injective e := by
    intro i j hij
    have hf : i.val.1.val.f = j.val.1.val.f :=
      congrArg (fun x : J => x.1.val.val) hij
    have ha' : i.val.1.val.a = j.val.1.val.a :=
      congrArg (fun x : J => x.2.2.val) hij
    have hn' : i.val.1.val.n = j.val.1.val.n := by
      apply Subtype.ext
      exact congrArg (fun x : J => x.2.1.1.val.val) hij
    have hu : i.val.1.val.epsilon = j.val.1.val.epsilon :=
      congrArg (fun x : J => x.2.1.2.1) hij
    have hk : i.val.2 = j.val.2 :=
      congrArg (fun x : J => x.2.1.2.2.val) hij
    have ht : i.val.1.val = j.val.1.val := by
      have hh : i.val.1.val.h = j.val.1.val.h :=
        i.val.1.property.trans j.val.1.property.symm
      generalize i.val.1.val = T at *
      generalize j.val.1.val = S at *
      cases T; cases S; simp_all
    exact Subtype.ext (Prod.ext (Subtype.ext ht) hk)
  have hew (j : t) :
      betaIdeal (RMSeparatedExpansion.activeSupport A j.val.1.val) j.val.1.val.a.val /
        A.exteriorNorm j.val.1.val.n = W (e j) := by
    simp only [W, e, g, beta_zero]
    change _ / idealNorm _ = (idealNorm _)⁻¹ * _
    rw [div_eq_mul_inv, mul_comm]
  have hsum : (∑ j ∈ t,
      betaIdeal (RMSeparatedExpansion.activeSupport A j.1.val) j.1.val.a.val /
        A.exteriorNorm j.1.val.n) ≤ ∑' j, W j := by
    rw [← t.sum_coe_sort]
    rw [← tsum_fintype (L := SummationFilter.unconditional t)]
    apply Summable.tsum_le_tsum_of_inj e hei (fun j _ => hw j)
      (fun j => le_of_eq (hew j)) Summable.of_finite hws
  have hfbound := active_sum_le A h Ka b (ha h.val h.property.1 0 (le_refl 0)).1
  have hnbound := (hn (Set.univ : Set (NonzeroIdeal F))).2.2 R hR
  have hhb : 0 ≤ idealHarmonicSum (Set.univ : Set (NonzeroIdeal F)) R :=
    tsum_nonneg (fun _ => by unfold idealNorm; positivity)
  have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hL : (L : ℝ) ≤ Real.log (2 * R) / Real.log 2 := by simpa [L] using dyad_count R hR
  change (∑ j ∈ t, _) ≤ _
  apply hsum.trans
  rw [hwt, hgt]
  calc
    _ ≤ (Ka * Real.rpow (idealNorm h.val) b) *
        (Cu * (Real.log (2 * R) / Real.log 2) * (Kn * Real.log (2 * R))) := by
      apply mul_le_mul hfbound _ (mul_nonneg (by positivity) hhb)
        (mul_nonneg hKa.le (Real.rpow_nonneg (by unfold idealNorm; positivity) _))
      apply mul_le_mul _ hnbound hhb (by positivity)
      apply mul_le_mul (by dsimp [Cu]; linarith) hL (by positivity) hCu.le
    _ = _ := by change _ = Ka * Kn * Cu / Real.log 2 * Real.rpow (idealNorm h.val) b * _; ring

end
end DedekindZetaZeroFree.RMDyadicSieveAggregation

end

section

namespace DedekindZetaZeroFree.RMRetainedAggregation
noncomputable section
open scoped NumberField BigOperators Classical
open ThetaBranch ThetaPhaseSeparation

variable {F : Type} [Field F] [NumberField F]

def branchNorm (A : SArithmeticData F) {h : A.Exterior}
    (i : RMSeparatedExpansion.Index A h) : ℝ :=
  rowNorm i.1.val.a i.2.val i.1.val.n

def cutoff (Z P D θ : ℝ) : ℝ :=
  8 * Real.rpow Z θ * D ^ 2 * P / Z

def retainedIndex (A : SArithmeticData F) (h : A.Exterior) (R₀ : ℝ) :
    Set (RMSeparatedExpansion.Index A h) :=
  {i | branchNorm A i ≤ R₀}

def retainedSummand (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h d : A.Exterior) (Z R₀ : ℝ) (i : RMSeparatedExpansion.Index A h) : ℂ :=
  if i ∈ retainedIndex A h R₀ then
    RMSeparatedExpansion.summand A G U σ ψ L H i.1.val d i.2 Z
  else 0

def retained (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h d : A.Exterior) (Z R₀ : ℝ) : ℂ :=
  ∑ᶠ i : RMSeparatedExpansion.Index A h,
    retainedSummand A G U σ ψ L H h d Z R₀ i

def rowDyad (A : SArithmeticData F) (h : A.Exterior) (D : ℝ) :
    Set (ExteriorSquarefreeIdeal A.cS) :=
  {d | D ≤ A.exteriorNorm d.val ∧ A.exteriorNorm d.val < 2 * D ∧
    d.val.val ⊔ h.val = ⊤}

def rowSquareMass (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h : A.Exterior) (Z D R₀ : ℝ) : ℝ :=
  ∑ᶠ d : rowDyad A h D,
    ‖retained A G U σ ψ L H h d.val.val Z R₀‖ ^ 2

def totalSquareMass (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (Z P D R₀ : ℝ) : ℝ :=
  ∑ᶠ h : exteriorPowerfulDyad A.cS P,
    rowSquareMass A G U σ ψ L H h.val Z D R₀

private theorem frozen_ext (A : SArithmeticData F) (T S : Frozen A)
    (hh : T.h = S.h) (hf : T.f.val = S.f.val) (ha : T.a.val = S.a.val)
    (hn : T.n.val = S.n.val) (he : T.epsilon = S.epsilon) : T = S := by
  have hf' : T.f = S.f := Subtype.ext hf
  have ha' : T.a = S.a := Subtype.ext ha
  have hn' : T.n = S.n := Subtype.ext hn
  cases T
  cases S
  simp_all

theorem retainedIndex_finite (A : SArithmeticData F) (h : A.Exterior) (R₀ : ℝ) :
    (retainedIndex A h R₀).Finite := by
  letI := SArithmeticData.sunitSixthPowerQuotient_finite F A
  letI : Finite A.UnitQuotient := Finite.of_equiv (PowerQuotient A.Rˣ 6)
    (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv A.U A.Rˣ 6 A.unitEquiv).symm.toEquiv
  let encode : RMSeparatedExpansion.Index A h →
      Ideal (𝓞 F) × NonzeroIdeal F × NonzeroIdeal F × NonzeroIdeal F × A.UnitQuotient :=
    fun i => (i.1.val.f.val, ⟨i.1.val.a.val, i.1.val.a.property.1⟩,
      ⟨i.1.val.n.val, i.1.val.n.property.1⟩,
      ⟨i.2.val.val, i.2.val.property.1⟩, i.1.val.epsilon)
  apply Set.Finite.of_injOn (f := encode)
    (t := (↑(activeSquarefreeDivisors h.val) : Set (Ideal (𝓞 F))) ×ˢ
      normBoundedIdeals F R₀ ×ˢ normBoundedIdeals F R₀ ×ˢ
      normBoundedIdeals F R₀ ×ˢ Set.univ)
  · intro i hi
    have ha := idealNorm_ge_one i.1.val.a.val i.1.val.a.property.1
    have hn := idealNorm_ge_one i.1.val.n.val i.1.val.n.property.1
    have hc := idealNorm_ge_one i.2.val.val i.2.val.property.1
    have hn3 : 1 ≤ idealNorm i.1.val.n.val ^ 3 := by
      simpa using (one_le_pow₀ hn : 1 ≤ idealNorm i.1.val.n.val ^ 3)
    have hnn : idealNorm i.1.val.n.val ≤ idealNorm i.1.val.n.val ^ 3 := by
      calc idealNorm i.1.val.n.val = idealNorm i.1.val.n.val * 1 ^ 2 := by ring
           _ ≤ idealNorm i.1.val.n.val * idealNorm i.1.val.n.val ^ 2 := by gcongr
           _ = _ := by ring
    change idealNorm i.1.val.a.val * idealNorm i.2.val.val *
      idealNorm i.1.val.n.val ^ 3 ≤ R₀ at hi
    have hac : 1 ≤ idealNorm i.1.val.a.val * idealNorm i.2.val.val := by nlinarith
    have hab : idealNorm i.1.val.a.val ≤ R₀ := by nlinarith
    have hcb : idealNorm i.2.val.val ≤ R₀ := by nlinarith
    have hnb : idealNorm i.1.val.n.val ≤ R₀ := by nlinarith
    refine ⟨?_, hab, hnb, hcb, Set.mem_univ _⟩
    apply (mem_activeSquarefreeDivisors_iff h.val h.property.1 _).mpr
    exact ⟨i.1.val.f.property.1, i.1.val.f_squarefree,
      i.1.property ▸ i.1.val.f_divides_radical⟩
  · intro i _ j _ hij
    have hf := congrArg (fun x => x.1) hij
    have ha := congrArg (fun x => x.2.1.val) hij
    have hn := congrArg (fun x => x.2.2.1.val) hij
    have hc := congrArg (fun x => x.2.2.2.1.val) hij
    have he := congrArg (fun x => x.2.2.2.2) hij
    have hh : i.1.val.h = j.1.val.h := i.1.property.trans j.1.property.symm
    apply Prod.ext
    · exact Subtype.ext (frozen_ext A _ _ hh hf ha hn he)
    · exact Subtype.ext (Subtype.ext hc)
  · exact (Set.toFinite _).prod ((normBoundedIdeals_finite F R₀).prod
      ((normBoundedIdeals_finite F R₀).prod
        ((normBoundedIdeals_finite F R₀).prod (Set.finite_univ))))

theorem retainedSummand_finite_support (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h d : A.Exterior) (Z R₀ : ℝ) :
    (Function.support (retainedSummand A G U σ ψ L H h d Z R₀)).Finite := by
  apply (retainedIndex_finite A h R₀).subset
  intro i hi
  by_contra hn
  exact hi (by simp [retainedSummand, hn])

theorem retained_eq_tsum (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h d : A.Exterior) (Z R₀ : ℝ) :
    retained A G U σ ψ L H h d Z R₀ =
      ∑' i : RMSeparatedExpansion.Index A h,
        retainedSummand A G U σ ψ L H h d Z R₀ i := by
  exact (tsum_eq_finsum (retainedSummand_finite_support A G U σ ψ L H h d Z R₀)).symm

theorem retained_eq_zero_of_cutoff_lt_one (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h d : A.Exterior) (Z R₀ : ℝ) (hR₀ : R₀ < 1) :
    retained A G U σ ψ L H h d Z R₀ = 0 := by
  have hzero : ∀ i : RMSeparatedExpansion.Index A h,
      retainedSummand A G U σ ψ L H h d Z R₀ i = 0 := by
    intro i
    have ha := idealNorm_ge_one i.1.val.a.val i.1.val.a.property.1
    have hn := idealNorm_ge_one i.1.val.n.val i.1.val.n.property.1
    have hc := idealNorm_ge_one i.2.val.val i.2.val.property.1
    have hi : 1 ≤ branchNorm A i := by
      unfold branchNorm rowNorm
      calc (1 : ℝ) = 1 * 1 * 1 ^ 3 := by norm_num
           _ ≤ _ := by gcongr
    have hi' : i ∉ retainedIndex A h R₀ := not_le.mpr (hR₀.trans_le hi)
    simp [retainedSummand, hi']
  simp [retained, hzero]

theorem rowDyad_finite (A : SArithmeticData F) (h : A.Exterior) (D : ℝ) :
    (rowDyad A h D).Finite := by
  let f : ExteriorSquarefreeIdeal A.cS → NonzeroIdeal F :=
    fun d => ⟨d.val.val, d.val.property.1⟩
  apply Set.Finite.of_injOn (f := f) (t := normBoundedIdeals F (2 * D))
  · intro d hd
    exact hd.2.1.le
  · intro d _ e _ hde
    exact Subtype.ext (Subtype.ext (congrArg (fun i : NonzeroIdeal F => i.val) hde))
  · exact normBoundedIdeals_finite F (2 * D)

theorem finiteMinkowski {I J : Type*} [Fintype I]
    (s : Finset J) (a : J → I → ℂ) :
    Real.sqrt (∑ i, ‖∑ j ∈ s, a j i‖ ^ 2) ≤
      ∑ j ∈ s, Real.sqrt (∑ i, ‖a j i‖ ^ 2) := by
  let v : J → EuclideanSpace ℂ I := fun j => WithLp.toLp 2 (a j)
  have he : (WithLp.toLp 2 (fun i => ∑ j ∈ s, a j i) : EuclideanSpace ℂ I) =
      ∑ j ∈ s, v j := by
    ext i
    simp [v]
  calc
    _ = ‖(WithLp.toLp 2 (fun i => ∑ j ∈ s, a j i) : EuclideanSpace ℂ I)‖ := by
      simpa only [PiLp.toLp_apply] using
        (EuclideanSpace.norm_eq (WithLp.toLp 2 (fun i => ∑ j ∈ s, a j i) :
          EuclideanSpace ℂ I)).symm
    _ = ‖∑ j ∈ s, v j‖ := congrArg norm he
    _ ≤ ∑ j ∈ s, ‖v j‖ := norm_sum_le _ _
    _ = _ := by simp only [v, EuclideanSpace.norm_eq, PiLp.toLp_apply]

theorem retained_eq_finite_sum (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h d : A.Exterior) (Z R : ℝ) :
    retained A G U σ ψ L H h d Z R =
      ∑ i ∈ (retainedIndex_finite A h R).toFinset,
        RMSeparatedExpansion.summand A G U σ ψ L H i.1.val d i.2 Z := by
  rw [retained, finsum_eq_sum_of_support_subset
    (s := (retainedIndex_finite A h R).toFinset)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Set.Finite.mem_toFinset] at hi
    simp [retainedSummand, hi]
  · intro i hi
    change i ∈ (retainedIndex_finite A h R).toFinset
    apply (retainedIndex_finite A h R).mem_toFinset.mpr
    by_contra hn
    exact hi (by simp [retainedSummand, hn])

theorem retained_eq_regrouped {J : Type*} (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h d : A.Exterior) (Z R : ℝ) (g : RMSeparatedExpansion.Index A h → J) :
    retained A G U σ ψ L H h d Z R =
      ∑ j ∈ ((retainedIndex_finite A h R).toFinset.image g),
        ∑ i ∈ ((retainedIndex_finite A h R).toFinset.filter (fun i => g i = j)),
          RMSeparatedExpansion.summand A G U σ ψ L H i.1.val d i.2 Z := by
  rw [retained_eq_finite_sum]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_image_of_mem g hi) _).symm

theorem retained_l2_regrouped_triangle {J : Type*} (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h : A.Exterior) (Z D R : ℝ) (g : RMSeparatedExpansion.Index A h → J) :
    Real.sqrt (rowSquareMass A G U σ ψ L H h Z D R) ≤
      ∑ j ∈ ((retainedIndex_finite A h R).toFinset.image g),
        Real.sqrt (∑ᶠ d : rowDyad A h D,
          ‖∑ i ∈ ((retainedIndex_finite A h R).toFinset.filter (fun i => g i = j)),
            RMSeparatedExpansion.summand A G U σ ψ L H i.1.val d.val.val i.2 Z‖ ^ 2) := by
  letI := (rowDyad_finite A h D).fintype
  simp only [rowSquareMass, finsum_eq_sum_of_fintype,
    retained_eq_regrouped (g := g)]
  exact finiteMinkowski _ _

theorem column_log_dyad (A : SArithmeticData F)
    (c : ExteriorSquarefreeIdeal A.cS) :
    (2 : ℝ) ^ Nat.log 2 (Ideal.absNorm c.val.val) ≤ A.exteriorNorm c.val ∧
      A.exteriorNorm c.val < 2 * (2 : ℝ) ^ Nat.log 2 (Ideal.absNorm c.val.val) := by
  have hc : Ideal.absNorm c.val.val ≠ 0 := by
    intro hc0
    exact c.val.property.1 (Ideal.absNorm_eq_zero_iff.mp hc0)
  change (2 : ℝ) ^ Nat.log 2 (Ideal.absNorm c.val.val) ≤ (Ideal.absNorm c.val.val : ℝ) ∧
    (Ideal.absNorm c.val.val : ℝ) < 2 * (2 : ℝ) ^ Nat.log 2 (Ideal.absNorm c.val.val)
  constructor
  · exact_mod_cast Nat.pow_log_le_self 2 hc
  · have hb := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Ideal.absNorm c.val.val)
    rw [pow_succ, mul_comm] at hb
    exact_mod_cast hb

theorem retained_column_norm_le (A : SArithmeticData F) {h : A.Exterior}
    (i : RMSeparatedExpansion.Index A h) (R : ℝ) (hi : i ∈ retainedIndex A h R) :
    A.exteriorNorm i.2.val ≤ R := by
  have ha := idealNorm_ge_one i.1.val.a.val i.1.val.a.property.1
  have hn := idealNorm_ge_one i.1.val.n.val i.1.val.n.property.1
  have hc := idealNorm_ge_one i.2.val.val i.2.val.property.1
  have hn3 : 1 ≤ idealNorm i.1.val.n.val ^ 3 := one_le_pow₀ hn
  change idealNorm i.1.val.a.val * idealNorm i.2.val.val *
    idealNorm i.1.val.n.val ^ 3 ≤ R at hi
  change idealNorm i.2.val.val ≤ R
  apply le_trans ?_ hi
  calc
    idealNorm i.2.val.val = 1 * idealNorm i.2.val.val * 1 := by ring
    _ ≤ idealNorm i.1.val.a.val * idealNorm i.2.val.val *
      idealNorm i.1.val.n.val ^ 3 := by gcongr

theorem retained_column_dyad_le (A : SArithmeticData F) {h : A.Exterior}
    (i : RMSeparatedExpansion.Index A h) (R : ℝ) (hi : i ∈ retainedIndex A h R) :
    (2 : ℝ) ^ Nat.log 2 (Ideal.absNorm i.2.val.val) ≤ R :=
  (column_log_dyad A i.2).1.trans (retained_column_norm_le A i R hi)

def frozenDyadKey (A : SArithmeticData F) (h : A.Exterior)
    (i : RMSeparatedExpansion.Index A h) : {T : Frozen A // T.h = h} × ℕ :=
  (i.1, Nat.log 2 (Ideal.absNorm i.2.val.val))

def QuadraticFamilyCompatibility (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (𝓕 : QuadraticHeckeFamily F A.cS) : Prop :=
  ∀ d c : ExteriorSquarefreeIdeal A.cS,
    (𝓕.χ c.val.val) d.val.val = quadraticPairing A G σ d.val c.val

theorem frozen_scalar_norm_bound (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x : Fˣ, ‖L x‖ = 1) (T : Frozen A) :
    ‖omega A G U σ ψ L T / (A.exteriorNorm T.n : ℂ)‖ ≤
      betaIdeal (RMSeparatedExpansion.activeSupport A T) T.a.val /
        A.exteriorNorm T.n := by
  have hn := idealNorm_ge_one T.n.val T.n.property.1
  have hb := (RMSeparatedExpansion.factors_norm_le_betaIdeal
    A G U σ ψ hψ L hL T T.n T.n).1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact div_le_div_of_nonneg_right hb (by linarith)

theorem sieve_majorant_mono (D C R b : ℝ) (hD : 0 ≤ D)
    (hC : 0 ≤ C) (hCR : C ≤ R) (hb : 0 ≤ b) :
    (D * C) ^ (b / 2) * Real.sqrt (D + C) ≤
      (D * R) ^ (b / 2) * Real.sqrt (D + R) := by
  have hR := hC.trans hCR
  apply mul_le_mul
  · exact Real.rpow_le_rpow (mul_nonneg hD hC)
      (mul_le_mul_of_nonneg_left hCR hD) (by positivity)
  · exact Real.sqrt_le_sqrt (by linarith)
  · exact Real.sqrt_nonneg _
  · exact Real.rpow_nonneg (mul_nonneg hD hR) _

theorem retained_l2_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ (u : A.UnitQuotient) (x : Fˣ), ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : RMSeparatedExpansion.FiniteProfileFamily A H)
    (𝓕 : QuadraticHeckeFamily F A.cS)
    (h𝓕 : QuadraticFamilyCompatibility A G σ 𝓕)
    (b₁ b₂ : ℝ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : A.UnitQuotient) (Z P D θ : ℝ),
        2 ≤ Z → 1 ≤ P → 1 ≤ D → 0 < θ →
        1 ≤ cutoff Z P D θ →
        ∀ h : A.Exterior, h ∈ exteriorPowerfulDyad A.cS P →
          Real.sqrt (rowSquareMass A G U σ ψ (L u) (H u) h Z D
            (cutoff Z P D θ)) ≤
          K * Real.rpow (A.exteriorNorm h) b₁ *
            Real.log (2 * cutoff Z P D θ) ^ 2 *
            Real.sqrt (D + cutoff Z P D θ) *
            Real.rpow (D * cutoff Z P D θ) (b₂ / 2) := by
  classical
  obtain ⟨K, hK, hblock⟩ := RMDyadicSieveAggregation.frozen_dyadic_block_bound
     A G U σ ψ hψ L hL H hH 𝓕 h𝓕 b₂ hb₂
  obtain ⟨M, hM, hweight⟩ := RMDyadicSieveAggregation.frozen_dyadic_weight_bound
    A b₁ hb₁
  refine ⟨K * M, mul_pos hK hM, ?_⟩
  intro u Z P D θ hZ hP hD hθ hR h hh
  letI : DecidableEq ({T : Frozen A // T.h = h} × ℕ) := Classical.decEq _
  let R := cutoff Z P D θ
  let s := (retainedIndex_finite A h R).toFinset
  let g := frozenDyadKey A h
  have hs (i) (hi : i ∈ s) : i ∈ retainedIndex A h R :=
    (retainedIndex_finite A h R).mem_toFinset.mp hi
  have hw := hweight h R s hR (fun i hi => hs i hi)
  have hw' : (∑ j ∈ s.image g,
      betaIdeal (RMSeparatedExpansion.activeSupport A j.1.val) j.1.val.a.val /
        A.exteriorNorm j.1.val.n) ≤
      M * (A.exteriorNorm h) ^ b₁ * Real.log (2 * R) ^ 2 := by
    apply le_trans (b := _) _ hw
    apply le_of_eq
    apply Finset.sum_congr
    · ext j
      simp only [Finset.mem_image, g, frozenDyadKey]
    · intro j hj
      rfl
  calc
    Real.sqrt (rowSquareMass A G U σ ψ (L u) (H u) h Z D R) ≤
        ∑ j ∈ s.image g,
          Real.sqrt (∑ᶠ d : rowDyad A h D,
            ‖∑ i ∈ s.filter (fun i => g i = j),
              RMSeparatedExpansion.summand A G U σ ψ (L u) (H u)
                i.1.val d.val.val i.2 Z‖ ^ 2) :=
      by simpa only [s] using
        (retained_l2_regrouped_triangle A G U σ ψ (L u) (H u) h Z D R g)
    _ ≤ ∑ j ∈ s.image g,
        K * (betaIdeal (RMSeparatedExpansion.activeSupport A j.1.val) j.1.val.a.val /
          A.exteriorNorm j.1.val.n) * (D * R) ^ (b₂ / 2) * Real.sqrt (D + R) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
      let C : ℝ := 2 ^ j.2
      have hC : 1 ≤ C := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hCR : C ≤ R := by
        have he : Nat.log 2 (Ideal.absNorm i.2.val.val) = j.2 :=
          congrArg Prod.snd hij
        simpa only [C, he] using retained_column_dyad_le A i R (hs i hi)
      have hslice : ∀ i ∈ s.filter (fun i => g i = j),
          i.1 = j.1 ∧ C ≤ A.exteriorNorm i.2.val ∧
            A.exteriorNorm i.2.val < 2 * C := by
        intro i hi
        have he := (Finset.mem_filter.mp hi).2
        have ht : i.1 = j.1 := congrArg Prod.fst he
        have hk : Nat.log 2 (Ideal.absNorm i.2.val.val) = j.2 :=
          congrArg Prod.snd he
        exact ⟨ht, by simpa only [C, hk] using (column_log_dyad A i.2).1,
          by simpa only [C, hk] using (column_log_dyad A i.2).2⟩
      have hb := hblock u h j.1 Z C D (s.filter (fun i => g i = j))
        (by linarith) hC hD hslice
      apply hb.trans
      have hscalar : 0 ≤ betaIdeal (RMSeparatedExpansion.activeSupport A j.1.val)
          j.1.val.a.val / A.exteriorNorm j.1.val.n :=
        (norm_nonneg _).trans (frozen_scalar_norm_bound A G U σ ψ hψ (L u) (hL u) j.1.val)
      calc
        K * (betaIdeal (RMSeparatedExpansion.activeSupport A j.1.val) j.1.val.a.val /
            A.exteriorNorm j.1.val.n) * (D * C) ^ (b₂ / 2) * Real.sqrt (D + C) =
          (K * (betaIdeal (RMSeparatedExpansion.activeSupport A j.1.val) j.1.val.a.val /
            A.exteriorNorm j.1.val.n)) *
              ((D * C) ^ (b₂ / 2) * Real.sqrt (D + C)) := by ring
        _ ≤ (K * (betaIdeal (RMSeparatedExpansion.activeSupport A j.1.val) j.1.val.a.val /
            A.exteriorNorm j.1.val.n)) *
              ((D * R) ^ (b₂ / 2) * Real.sqrt (D + R)) :=
          mul_le_mul_of_nonneg_left
            (sieve_majorant_mono D C R b₂ (by linarith) (by linarith) hCR hb₂.le)
            (mul_nonneg hK.le hscalar)
        _ = _ := by ring
    _ = K * (∑ j ∈ s.image g,
        betaIdeal (RMSeparatedExpansion.activeSupport A j.1.val) j.1.val.a.val /
          A.exteriorNorm j.1.val.n) * (D * R) ^ (b₂ / 2) * Real.sqrt (D + R) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ ≤ K * (M * (A.exteriorNorm h) ^ b₁ * Real.log (2 * R) ^ 2) *
        (D * R) ^ (b₂ / 2) * Real.sqrt (D + R) := by
      gcongr
    _ = (K * M) * (A.exteriorNorm h) ^ b₁ * Real.log (2 * R) ^ 2 *
        Real.sqrt (D + R) * (D * R) ^ (b₂ / 2) := by ring

private theorem bound_square (K P D R b₁ b₂ : ℝ)
    (hP : 0 < P) (hD : 0 < D) (hR : 0 < R) :
    (K * (2 * P) ^ b₁ * Real.log (2 * R) ^ 2 * Real.sqrt (D + R) *
      (D * R) ^ (b₂ / 2)) ^ 2 =
      K ^ 2 * (2 * P) ^ (2 * b₁) * Real.log (2 * R) ^ 4 *
        (D + R) * (D * R) ^ b₂ := by
  simp only [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 2 * P),
    ← Real.rpow_mul_natCast (by positivity : 0 ≤ D * R),
    Real.sq_sqrt (by positivity : 0 ≤ D + R)]
  convert rfl using 1 <;> ring

theorem retained_total_square_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ (u : A.UnitQuotient) (x : Fˣ), ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : RMSeparatedExpansion.FiniteProfileFamily A H)
    (𝓕 : QuadraticHeckeFamily F A.cS)
    (h𝓕 : QuadraticFamilyCompatibility A G σ 𝓕)
    (b₁ b₂ : ℝ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    ∃ K' : ℝ, 0 < K' ∧
      ∀ (u : A.UnitQuotient) (Z P D θ : ℝ),
        2 ≤ Z → 1 ≤ P → 1 ≤ D → 0 < θ →
        1 ≤ cutoff Z P D θ →
        totalSquareMass A G U σ ψ (L u) (H u) Z P D (cutoff Z P D θ) ≤
          K' * Real.rpow P (1 / 2 + 2 * b₁) *
            Real.log (2 * cutoff Z P D θ) ^ 4 *
            (D + cutoff Z P D θ) * Real.rpow (D * cutoff Z P D θ) b₂ := by
  obtain ⟨K, hK, hb⟩ := retained_l2_bound A G U σ ψ hψ L hL H hH 𝓕 h𝓕
    b₁ b₂ hb₁ hb₂
  obtain ⟨C, hC, hc⟩ := exterior_powerful_dyad_count_bound F
  refine ⟨C * K ^ 2 * Real.rpow 2 (2 * b₁),
    mul_pos (mul_pos hC (sq_pos_of_pos hK)) (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro u Z P D θ hZ hP hD hθ hR
  let R := cutoff Z P D θ
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hPp : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let M := K ^ 2 * (2 * P) ^ (2 * b₁) * Real.log (2 * R) ^ 4 *
    (D + R) * (D * R) ^ b₂
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hrow (h : exteriorPowerfulDyad A.cS P) :
      rowSquareMass A G U σ ψ (L u) (H u) h.val Z D R ≤ M := by
    have hbound := hb u Z P D θ hZ hP hD hθ hR h.val h.property
    have hnorm : (A.exteriorNorm h.val) ^ b₁ ≤ (2 * P) ^ b₁ :=
      Real.rpow_le_rpow (by have := idealNorm_ge_one h.val.val h.val.property.1; linarith)
        h.property.2.2.le hb₁.le
    have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
    have hb' : Real.sqrt (rowSquareMass A G U σ ψ (L u) (H u) h.val Z D R) ≤
        K * (2 * P) ^ b₁ * Real.log (2 * R) ^ 2 * Real.sqrt (D + R) *
          (D * R) ^ (b₂ / 2) := by
      change Real.sqrt (rowSquareMass A G U σ ψ (L u) (H u) h.val Z D R) ≤
        K * (A.exteriorNorm h.val) ^ b₁ * Real.log (2 * R) ^ 2 *
          Real.sqrt (D + R) * (D * R) ^ (b₂ / 2) at hbound
      apply hbound.trans
      gcongr
    have hmass : 0 ≤ rowSquareMass A G U σ ψ (L u) (H u) h.val Z D R :=
      finsum_nonneg (fun _ => sq_nonneg _)
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hb'
    rw [Real.sq_sqrt hmass, bound_square K P D R b₁ b₂ hPp hDp hRp] at hsq
    exact hsq
  letI := (exteriorPowerfulDyad_finite A.cS P).fintype
  have hcard : (Fintype.card (exteriorPowerfulDyad A.cS P) : ℝ) ≤ C * Real.sqrt P := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
      hc A.cS A.cS_ne_zero P hP
  calc
    totalSquareMass A G U σ ψ (L u) (H u) Z P D R =
        ∑ h : exteriorPowerfulDyad A.cS P,
          rowSquareMass A G U σ ψ (L u) (H u) h.val Z D R :=
      finsum_eq_sum_of_fintype _
    _ ≤ ∑ _h : exteriorPowerfulDyad A.cS P, M := Finset.sum_le_sum (fun h _ => hrow h)
    _ = (Fintype.card (exteriorPowerfulDyad A.cS P) : ℝ) * M := by
      simp [nsmul_eq_mul]
    _ ≤ (C * Real.sqrt P) * M := mul_le_mul_of_nonneg_right hcard hM
    _ = C * K ^ 2 * Real.rpow 2 (2 * b₁) * Real.rpow P (1 / 2 + 2 * b₁) *
        Real.log (2 * R) ^ 4 * (D + R) * Real.rpow (D * R) b₂ := by
      dsimp [M]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hPp.le,
        Real.sqrt_eq_rpow, Real.rpow_add hPp]
      ring

end
end DedekindZetaZeroFree.RMRetainedAggregation

end
