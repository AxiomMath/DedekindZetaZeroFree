module

public import DedekindZetaZeroFree.Arithmetic.Ideals.RationalPrimePrincipalIdeals
public import DedekindZetaZeroFree.LargeSieve.Bilinear.RationalPrimeDivisorIncidence
public import DedekindZetaZeroFree.LargeSieve.Bilinear.OperatorNormBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.UniformConductorControl
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.FiniteBandAveraging

@[expose] public section

section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.RationalBandInflation

open scoped NumberField Classical

set_option maxHeartbeats 800000 in

theorem arithmetic_band_data (F : Type) [Field F] [NumberField F]
    (q : Ideal (𝓞 F)) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (M N V : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hV : M ≤ V) :
    let d : ℕ := Module.finrank ℚ F
    let H : ℝ := max 2 (max ((NumberField.discr F).natAbs : ℝ)
      (Ideal.absNorm q : ℝ))
    let L : ℕ := Nat.ceil (6 * (d : ℝ) / δ) + 1
    let J : ℕ := L * d
    let Y : ℝ := H ^ d * V * (2 * M * N) ^ δ
    0 ≤ (d : ℝ) / δ ∧ 1 ≤ L ∧ 6 * ((d : ℝ) / δ) ≤ (L : ℝ) ∧
      0 < Y ∧ ∃ p : Fin L → ℕ, Function.Injective p ∧
        (∀ i, (p i).Prime ∧
          max (NumberField.discr F).natAbs (Ideal.absNorm q) < p i) ∧
        (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * M * N →
          (((Finset.univ : Finset (Fin L)).filter (fun i => p i ∣ n)).card : ℝ)
            ≤ (d : ℝ) / δ) ∧
        (∀ i (a : Ideal (𝓞 F)), M < (Ideal.absNorm a : ℝ) →
          (Ideal.absNorm a : ℝ) ≤ 2 * M →
          Y < (Ideal.absNorm (a * rationalPrincipalIdeal F (p i)) : ℝ) ∧
          (Ideal.absNorm (a * rationalPrincipalIdeal F (p i)) : ℝ) ≤
            (2 : ℝ) ^ (J + 1) * Y) := by
  dsimp
  set d : ℕ := Module.finrank ℚ F
  set H : ℝ := max 2 (max ((NumberField.discr F).natAbs : ℝ)
    (Ideal.absNorm q : ℝ))
  set L : ℕ := Nat.ceil (6 * (d : ℝ) / δ) + 1
  set J : ℕ := L * d
  set Z : ℝ := 2 * M * N
  set Y : ℝ := H ^ d * V * Z ^ δ
  have hd : 0 < d := Module.finrank_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hH : 2 ≤ H := le_max_left _ _
  have hHpos : 0 < H := by linarith
  have hZ : 2 ≤ Z := by dsimp [Z]; nlinarith
  have hZpos : 0 < Z := by linarith
  have hMpos : 0 < M := by linarith
  have hVpos : 0 < V := by linarith
  have hVM : 1 ≤ V / M := (one_le_div hMpos).mpr hV
  have hVMpos : 0 < V / M := by linarith
  have hδd : 0 < δ / (d : ℝ) := div_pos hδ hdR
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hceil : 6 * ((d : ℝ) / δ) ≤ (L : ℝ) := by
    calc
      6 * ((d : ℝ) / δ) = 6 * (d : ℝ) / δ := by ring
      _ ≤ (Nat.ceil (6 * (d : ℝ) / δ) : ℝ) := Nat.le_ceil _
      _ ≤ (L : ℝ) := by dsimp [L]; push_cast; linarith
  have hY : 0 < Y := by dsimp [Y]; positivity
  let x : ℝ := H * (V / M) ^ (1 / (d : ℝ)) * Z ^ (δ / (d : ℝ))
  have hpowVM : ((V / M) ^ (1 / (d : ℝ))) ^ d = V / M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hVMpos)]
    have hh : (1 / (d : ℝ)) * (d : ℝ) = 1 := by field_simp
    rw [hh, Real.rpow_one]
  have hpowZ : (Z ^ (δ / (d : ℝ))) ^ d = Z ^ δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZpos.le]
    congr 1
    field_simp
  have hxpow : x ^ d = Y / M := by
    dsimp [x, Y]
    rw [mul_pow, mul_pow, hpowVM, hpowZ]
    field_simp
  have hVM1 : 1 ≤ (V / M) ^ (1 / (d : ℝ)) :=
    Real.one_le_rpow hVM (by positivity)
  have hZ1 : 1 ≤ Z ^ (δ / (d : ℝ)) := Real.one_le_rpow (by linarith) hδd.le
  have hxgeH : H ≤ x := by dsimp [x]; nlinarith [mul_nonneg (sub_nonneg.mpr hVM1) (sub_nonneg.mpr hZ1)]
  have hxZ : Z ^ (δ / (d : ℝ)) ≤ x := by
    dsimp [x]
    have hprod : 1 ≤ H * (V / M) ^ (1 / (d : ℝ)) := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hprod) (le_trans (by norm_num) hZ1)]
  obtain ⟨p, hinj, hp⟩ := exists_rationalBertrand_sequence x (by linarith) L hL
  refine ⟨div_nonneg hdR.le hδ.le, hL, hceil, hY, p, hinj, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hp i).1, ?_⟩
    have hbound : (max (NumberField.discr F).natAbs (Ideal.absNorm q) : ℝ) ≤ H := by
      dsimp [H]
      simpa only [Nat.cast_max] using
        (le_max_right (2 : ℝ) (max ((NumberField.discr F).natAbs : ℝ) (Ideal.absNorm q : ℝ)))
    have hpgt : x < (p i : ℝ) := by
      have hpow : (1 : ℝ) ≤ 2 ^ (i : ℕ) := one_le_pow₀ (by norm_num)
      nlinarith [(hp i).2.1]
    exact_mod_cast (lt_of_le_of_lt (le_trans hbound hxgeH) hpgt)
  · intro n hn hnZ
    apply rationalPrime_divisor_incidence Finset.univ p (fun _ _ _ _ h => hinj h)
      Z (d : ℝ) δ hZ hd1 hδ
    · intro i _
      refine ⟨(hp i).1, ?_⟩
      have hpow : (1 : ℝ) ≤ 2 ^ (i : ℕ) := one_le_pow₀ (by norm_num)
      have : x < (p i : ℝ) := by nlinarith [(hp i).2.1]
      exact lt_of_le_of_lt hxZ this
    · exact hn
    · exact hnZ
  · intro i a ha ha2
    have hpgt : x < (p i : ℝ) := by
      have hh : (1 : ℝ) ≤ 2 ^ (i : ℕ) := one_le_pow₀ (by norm_num)
      nlinarith [(hp i).2.1]
    have hpn : x ^ d < (p i : ℝ) ^ d := pow_lt_pow_left₀ hpgt (by linarith) hd.ne'
    have hpn_le : (p i : ℝ) ^ d ≤ (2 : ℝ) ^ J * x ^ d := by
      have hstep : (p i : ℝ) ^ d ≤ ((2 : ℝ) ^ ((i : ℕ) + 1) * x) ^ d :=
        (pow_le_pow_left₀ (by positivity) (hp i).2.2 d)
      have hindex : ((i : ℕ) + 1) * d ≤ J := by
        dsimp [J]
        exact Nat.mul_le_mul_right d (by omega)
      have htwo : (2 : ℝ) ^ (((i : ℕ) + 1) * d) ≤ 2 ^ J :=
        pow_le_pow_right₀ (by norm_num) hindex
      rw [mul_pow, ← pow_mul] at hstep
      exact le_trans hstep (mul_le_mul_of_nonneg_right htwo (by positivity))
    have hnorm : (Ideal.absNorm (a * rationalPrincipalIdeal F (p i)) : ℝ) =
        (Ideal.absNorm a : ℝ) * (p i : ℝ) ^ d := by
      rw [map_mul, rationalPrincipalIdeal_absNorm F (hp i).1]
      simp only [Nat.cast_mul, Nat.cast_pow, d]
    have hppos : 0 < (p i : ℝ) := by exact_mod_cast (hp i).1.pos
    rw [hnorm]
    constructor
    · rw [hxpow] at hpn
      have : M * (Y / M) = Y := by field_simp
      nlinarith [mul_pos (sub_pos.mpr ha) (by positivity : 0 < (p i : ℝ) ^ d)]
    · have h2J : 0 ≤ (2 : ℝ) ^ J := by positivity
      have hfactor : (2 : ℝ) ^ (J + 1) = 2 * 2 ^ J := by rw [pow_succ]; ring
      rw [hfactor, hxpow] at *
      have heq : M * (Y / M) = Y := by field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (by positivity : 0 ≤ (p i : ℝ) ^ d),
        mul_nonneg (sub_nonneg.mpr hpn_le) (by linarith : 0 ≤ M)]

end DedekindZetaZeroFree.LargeSieve.Sieve.RationalBandInflation

end

section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.RationalBandInflation

open scoped NumberField Classical

noncomputable def bandRows (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Y : ℝ) (J : ℕ) : Finset (Ideal (𝓞 F)) :=
  (Finset.range (J + 1)).biUnion (fun j => paperShell F c ((2 : ℝ) ^ j * Y))

private theorem pairwiseDisjoint_bandShells (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Y : ℝ) (hY : 0 < Y) (J : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (J + 1)) : Set ℕ)
      (fun j => paperShell F c ((2 : ℝ) ^ j * Y)) := by
  intro i _ j _ hij
  change Disjoint (paperShell F c ((2 : ℝ) ^ i * Y)) (paperShell F c ((2 : ℝ) ^ j * Y))
  rw [Finset.disjoint_left]
  intro a hia hja
  obtain ⟨-, -, hi1, hi2⟩ := (mem_paperShell F c ((2 : ℝ) ^ i * Y) a).mp hia
  obtain ⟨-, -, hj1, hj2⟩ := (mem_paperShell F c ((2 : ℝ) ^ j * Y) a).mp hja
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hp : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hmul : (2 : ℝ) ^ (i + 1) * Y ≤ (2 : ℝ) ^ j * Y :=
      mul_le_mul_of_nonneg_right hp (le_of_lt hY)
    have hi2' : (Ideal.absNorm a : ℝ) ≤ (2 : ℝ) ^ (i + 1) * Y := by
      have h : (2 : ℝ) ^ (i + 1) * Y = 2 * ((2 : ℝ) ^ i * Y) := by
        rw [pow_succ]; ring
      rw [h]; exact hi2
    linarith
  · have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hmul : (2 : ℝ) ^ (j + 1) * Y ≤ (2 : ℝ) ^ i * Y :=
      mul_le_mul_of_nonneg_right hp (le_of_lt hY)
    have hj2' : (Ideal.absNorm a : ℝ) ≤ (2 : ℝ) ^ (j + 1) * Y := by
      have h : (2 : ℝ) ^ (j + 1) * Y = 2 * ((2 : ℝ) ^ j * Y) := by
        rw [pow_succ]; ring
      rw [h]; exact hj2
    linarith

theorem dyadic_band_aggregation (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (Y : ℝ) (hY : 0 < Y) (J : ℕ) (N : ℝ) :
    (∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ c = ⊤ →
      Y < (Ideal.absNorm a : ℝ) →
      (Ideal.absNorm a : ℝ) ≤ (2 : ℝ) ^ (J + 1) * Y →
      a ∈ bandRows F c Y J) ∧
    0 ≤ (∑ j ∈ Finset.range (J + 1), B1 F c Q ((2 : ℝ) ^ j * Y) N) ∧
    (∀ lam : Ideal (𝓞 F) → ℂ,
      ∑ a ∈ bandRows F c Y J, ‖rowSum Q N lam a‖ ^ 2 ≤
        (∑ j ∈ Finset.range (J + 1), B1 F c Q ((2 : ℝ) ^ j * Y) N) *
          energy F c N lam) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    intro a hsf hcop hlo hhi
    have hex : ∃ k : ℕ, (Ideal.absNorm a : ℝ) ≤ (2 : ℝ) ^ (k + 1) * Y := ⟨J, hhi⟩
    have hjle : Nat.find hex ≤ J := Nat.find_min' hex hhi
    have hspec : (Ideal.absNorm a : ℝ) ≤ (2 : ℝ) ^ (Nat.find hex + 1) * Y :=
      Nat.find_spec hex
    have hlow : (2 : ℝ) ^ Nat.find hex * Y < (Ideal.absNorm a : ℝ) := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero, one_mul]; exact hlo
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        have hmin : ¬ ((Ideal.absNorm a : ℝ) ≤ (2 : ℝ) ^ (k + 1) * Y) :=
          Nat.find_min hex (by omega)
        rw [hk]
        exact lt_of_not_ge hmin
    have hup : (Ideal.absNorm a : ℝ) ≤ 2 * ((2 : ℝ) ^ Nat.find hex * Y) := by
      have h : (2 : ℝ) ^ (Nat.find hex + 1) * Y = 2 * ((2 : ℝ) ^ Nat.find hex * Y) := by
        rw [pow_succ]; ring
      rw [h] at hspec
      exact hspec
    show a ∈ (Finset.range (J + 1)).biUnion (fun j => paperShell F c ((2 : ℝ) ^ j * Y))
    refine Finset.mem_biUnion.mpr ⟨Nat.find hex, ?_, ?_⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hjle)
    · exact (mem_paperShell F c ((2 : ℝ) ^ Nat.find hex * Y) a).mpr
        ⟨hsf, hcop, hlow, hup⟩
  · exact Finset.sum_nonneg fun j _ => B1_nonneg Q ((2 : ℝ) ^ j * Y) N
  ·
    intro lam
    have hdisj := pairwiseDisjoint_bandShells F c Y hY J
    have hsplit : (∑ a ∈ bandRows F c Y J, ‖rowSum Q N lam a‖ ^ 2) =
        ∑ j ∈ Finset.range (J + 1), Q1 F c Q ((2 : ℝ) ^ j * Y) N lam := by
      rw [bandRows, Finset.sum_biUnion hdisj]
      rfl
    calc ∑ a ∈ bandRows F c Y J, ‖rowSum Q N lam a‖ ^ 2
        = ∑ j ∈ Finset.range (J + 1), Q1 F c Q ((2 : ℝ) ^ j * Y) N lam := hsplit
      _ ≤ ∑ j ∈ Finset.range (J + 1),
            B1 F c Q ((2 : ℝ) ^ j * Y) N * energy F c N lam :=
          Finset.sum_le_sum fun j _ => Q1_le_B1_mul_energy Q ((2 : ℝ) ^ j * Y) N lam
      _ = (∑ j ∈ Finset.range (J + 1), B1 F c Q ((2 : ℝ) ^ j * Y) N) *
            energy F c N lam := (Finset.sum_mul ..).symm

end DedekindZetaZeroFree.LargeSieve.Sieve.RationalBandInflation

end

section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.RationalBandInflation

open scoped NumberField Classical

theorem rational_row_transport (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (hcond : ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
      Q.cond b ∣ b * q)
    (p : ℕ) (hp : p.Prime)
    (hlarge : max (NumberField.discr F).natAbs (Ideal.absNorm q) < p)
    (M N : ℝ) :
    Function.Injective (fun a : Ideal (𝓞 F) => a * rationalPrincipalIdeal F p) ∧
      (∀ a ∈ paperShell F c M, ¬p ∣ Ideal.absNorm a →
        Squarefree (a * rationalPrincipalIdeal F p) ∧
          (a * rationalPrincipalIdeal F p) ⊔ c = ⊤) ∧
      (∀ b ∈ paperShell F c N, ‖(Q.χ b) (rationalPrincipalIdeal F p)‖ ≤ 1) ∧
      (∀ b ∈ paperShell F c N, ¬p ∣ Ideal.absNorm b →
        ‖(Q.χ b) (rationalPrincipalIdeal F p)‖ = 1) ∧
      (∀ a b : Ideal (𝓞 F),
        (Q.χ b) (a * rationalPrincipalIdeal F p) =
          (Q.χ b) (rationalPrincipalIdeal F p) * (Q.χ b) a) := by
  classical
  set P : Ideal (𝓞 F) := rationalPrincipalIdeal F p with hPdef
  have hPne : P ≠ ⊥ := by
    rw [hPdef]; exact rationalPrincipalIdeal_ne_bot F hp
  have hsqP : Squarefree P := by
    rw [hPdef]
    exact (rationalPrincipalIdeal_squarefree_coprime F hp q hq hlarge).1
  have hqpos : 0 < Ideal.absNorm q := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hq
  have hpq : ¬ p ∣ Ideal.absNorm q := by
    intro h
    have h1 : p ≤ Ideal.absNorm q := Nat.le_of_dvd hqpos h
    have h2 := le_max_right (NumberField.discr F).natAbs (Ideal.absNorm q)
    omega
  have hcne : c ≠ ⊥ := by
    intro hc
    obtain ⟨d, hd⟩ := hcq
    exact hq (by rw [hd, hc]; simp)
  have hcpos : 0 < Ideal.absNorm c := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hcne
  have hcq_le : q ≤ c := Ideal.dvd_iff_le.mp hcq
  have habsc_dvd : Ideal.absNorm c ∣ Ideal.absNorm q :=
    Ideal.absNorm_dvd_absNorm_of_le hcq_le
  have hpc : ¬ p ∣ Ideal.absNorm c := by
    intro h
    have h1 : p ≤ Ideal.absNorm c := Nat.le_of_dvd hcpos h
    have h2 : Ideal.absNorm c ≤ Ideal.absNorm q := Nat.le_of_dvd hqpos habsc_dvd
    have h3 := le_max_right (NumberField.discr F).natAbs (Ideal.absNorm q)
    omega
  have hPsupc : P ⊔ c = ⊤ := by
    rw [hPdef]
    exact rationalPrincipalIdeal_sup_eq_top F hp c hcne hpc
  have hPsup_of : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → ¬ p ∣ Ideal.absNorm I → P ⊔ I = ⊤ := by
    intro I hI h
    rw [hPdef]
    exact rationalPrincipalIdeal_sup_eq_top F hp I hI h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a a' haa
    exact mul_right_cancel₀ hPne haa
  · intro a ha hpa
    rw [mem_paperShell] at ha
    obtain ⟨hsqa, hac, -, -⟩ := ha
    have hane : a ≠ ⊥ := hsqa.ne_zero
    have hsupaP : a ⊔ P = ⊤ := by
      rw [sup_comm]; exact hPsup_of a hane hpa
    have hrel : IsRelPrime a P := by
      intro d hda hdP
      have hdt : d ∣ (⊤ : Ideal (𝓞 F)) := by
        rw [← hsupaP]
        exact Ideal.dvd_iff_le.mpr
          (sup_le (Ideal.dvd_iff_le.mp hda) (Ideal.dvd_iff_le.mp hdP))
      have hdtop : d = ⊤ := le_antisymm le_top (Ideal.dvd_iff_le.mp hdt)
      exact Ideal.isUnit_iff.mpr hdtop
    have hsq : Squarefree (a * P) :=
      squarefree_mul_iff.mpr ⟨hrel, hsqa, hsqP⟩
    have hcop : IsCoprime (a * P) c :=
      IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.mpr hac)
        (Ideal.isCoprime_iff_sup_eq.mpr hPsupc)
    exact ⟨hsq, Ideal.isCoprime_iff_sup_eq.mp hcop⟩
  · intro b hb
    rw [mem_paperShell] at hb
    obtain ⟨hsqb, hbc, -, -⟩ := hb
    set z : ℂ := (Q.χ b) P with hzdef
    have hquad : z ^ 3 = z := Q.quadratic b P hsqb hbc
    have hfac : z * (z - 1) * (z + 1) = 0 := by linear_combination hquad
    rcases mul_eq_zero.mp hfac with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rw [h']; simp
      · have : z = 1 := sub_eq_zero.mp h'
        rw [this]; simp
    · have : z = -1 := add_eq_zero_iff_eq_neg.mp h
      rw [this]; simp
  · intro b hb hpb
    rw [mem_paperShell] at hb
    obtain ⟨hsqb, hbc, -, -⟩ := hb
    have hcondne : Q.cond b ≠ ⊥ := (Q.primitive b hsqb hbc).1
    have hdvd : Q.cond b ∣ b * q := hcond b hsqb hbc
    have habs : Ideal.absNorm (Q.cond b) ∣ Ideal.absNorm b * Ideal.absNorm q := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdvd)
      rwa [map_mul Ideal.absNorm b q] at h
    have hpcond : ¬ p ∣ Ideal.absNorm (Q.cond b) := by
      intro h
      rcases hp.dvd_mul.mp (h.trans habs) with h3 | h3
      · exact hpb h3
      · exact hpq h3
    have hsup : P ⊔ Q.cond b = ⊤ := hPsup_of (Q.cond b) hcondne hpcond
    set z : ℂ := (Q.χ b) P with hzdef
    have hz0 : z ≠ 0 := by
      intro hz
      rcases ((Q.χ b).eq_zero_iff' P).mp hz with hbot | hnot
      · exact hPne hbot
      · exact hnot hsup
    have hquad : z ^ 3 = z := Q.quadratic b P hsqb hbc
    have hz2 : z * z = 1 := by
      have h3 : z * (z * z) = z * 1 := by
        calc z * (z * z) = z ^ 3 := by ring
          _ = z := hquad
          _ = z * 1 := by ring
      exact mul_left_cancel₀ hz0 h3
    rcases mul_self_eq_one_iff.mp hz2 with h | h
    · rw [h]; simp
    · rw [h]; simp
  · intro a b
    rw [(Q.χ b).map_mul' a P]
    ring

end DedekindZetaZeroFree.LargeSieve.Sieve.RationalBandInflation

end

section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.RationalBandInflation

open scoped NumberField Classical

theorem B1_isLeast_quadratic_bound (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (M N : ℝ) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ lam : Ideal (𝓞 F) → ℂ,
      Q1 F c Q M N lam ≤ C * energy F c N lam} (B1 F c Q M N) := by
  constructor
  · exact ⟨B1_nonneg Q M N, fun lam => Q1_le_B1_mul_energy Q M N lam⟩
  · rintro C ⟨hC0, hC⟩
    refine csSup_le ⟨0, Or.inl rfl⟩ ?_
    rintro x (hx | ⟨lam, hlam, rfl⟩)
    · have hx0 : x = 0 := by simpa using hx
      rw [hx0]
      exact hC0
    · calc
        Q1 F c Q M N lam ≤ C * energy F c N lam := hC lam
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hlam hC0
        _ = C := mul_one C

end DedekindZetaZeroFree.LargeSieve.Sieve.RationalBandInflation

end

section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem rational_band_inflation (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (hcond : ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
      Q.cond b ∣ b * q)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (M N V : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hV : M ≤ V) :
    let d : ℕ := Module.finrank ℚ F
    let H : ℝ := max 2 (max ((NumberField.discr F).natAbs : ℝ)
      (Ideal.absNorm q : ℝ))
    let A : ℝ := H ^ d
    let L : ℕ := Nat.ceil (6 * (d : ℝ) / δ) + 1
    let J : ℕ := L * d
    let Y : ℝ := A * V * (2 * M * N) ^ δ
    B1 F c Q M N ≤
      4 * ∑ j ∈ Finset.range (J + 1), B1 F c Q ((2 : ℝ) ^ j * Y) N := by
  classical
  let d : ℕ := Module.finrank ℚ F
  let H : ℝ := max 2 (max ((NumberField.discr F).natAbs : ℝ)
    (Ideal.absNorm q : ℝ))
  let L : ℕ := Nat.ceil (6 * (d : ℝ) / δ) + 1
  let J : ℕ := L * d
  let Y : ℝ := H ^ d * V * (2 * M * N) ^ δ
  change B1 F c Q M N ≤
    4 * ∑ j ∈ Finset.range (J + 1), B1 F c Q ((2 : ℝ) ^ j * Y) N
  obtain ⟨ht, hL, habsorb, hY, p, hinjp, hprime, hinc, hnorm⟩ :=
    RationalBandInflation.arithmetic_band_data F q δ hδ hδ1 M N V hM hN hV
  let R := paperShell F c M
  let S := paperShell F c N
  let T := RationalBandInflation.bandRows F c Y J
  let rowGood : Fin L → Ideal (𝓞 F) → Prop := fun i a => ¬p i ∣ Ideal.absNorm a
  let colGood : Fin L → Ideal (𝓞 F) → Prop := fun i b => ¬p i ∣ Ideal.absNorm b
  let P : Fin L → Ideal (𝓞 F) := fun i => rationalPrincipalIdeal F (p i)
  have htransport := fun i : Fin L =>
    RationalBandInflation.rational_row_transport F c Q q hq hcq hcond
      (p i) (hprime i).1 (hprime i).2 M N
  obtain ⟨hcover, hBT, htarget⟩ :=
    RationalBandInflation.dyadic_band_aggregation F c Q Y hY J N
  let f : ∀ i : Fin L, {a : Ideal (𝓞 F) // a ∈ R ∧ rowGood i a} →
      {a : Ideal (𝓞 F) // a ∈ T} := fun i a =>
    ⟨a.val * P i, by
      obtain ⟨hsf, hcop⟩ := (htransport i).2.1 a.val a.property.1 a.property.2
      obtain ⟨-, -, hlo, hhi⟩ := (mem_paperShell F c M a.val).mp a.property.1
      obtain ⟨hlo', hhi'⟩ := hnorm i a.val hlo hhi
      exact hcover (a.val * P i) hsf hcop hlo' hhi'⟩
  have hf : ∀ i, Function.Injective (f i) := by
    intro i a a' haa
    apply Subtype.ext
    apply (htransport i).1
    exact congrArg Subtype.val haa
  have hrowbad : ∀ a ∈ R,
      (((Finset.univ : Finset (Fin L)).filter (fun i => ¬rowGood i a)).card : ℝ)
        ≤ (d : ℝ) / δ := by
    intro a ha
    obtain ⟨-, -, hlo, hhi⟩ := (mem_paperShell F c M a).mp ha
    have hn : (1 : ℝ) ≤ (Ideal.absNorm a : ℝ) := by linarith
    have hnZ : (Ideal.absNorm a : ℝ) ≤ 2 * M * N := by nlinarith
    simpa only [rowGood, not_not] using hinc (Ideal.absNorm a) (by exact_mod_cast hn) hnZ
  have hcolbad : ∀ b ∈ S,
      (((Finset.univ : Finset (Fin L)).filter (fun i => ¬colGood i b)).card : ℝ)
        ≤ (d : ℝ) / δ := by
    intro b hb
    obtain ⟨-, -, hlo, hhi⟩ := (mem_paperShell F c N b).mp hb
    have hn : (1 : ℝ) ≤ (Ideal.absNorm b : ℝ) := by linarith
    have hnZ : (Ideal.absNorm b : ℝ) ≤ 2 * M * N := by nlinarith
    simpa only [colGood, not_not] using hinc (Ideal.absNorm b) (by exact_mod_cast hn) hnZ
  have hleast := RationalBandInflation.B1_isLeast_quadratic_bound F c Q M N
  have hleast' : IsLeast {C : ℝ | 0 ≤ C ∧ ∀ lam : Ideal (𝓞 F) → ℂ,
      ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2 ≤
        C * (∑ b ∈ S, ‖lam b‖ ^ 2)} (B1 F c Q M N) := by
    simpa only [Q1, rowSum, energy] using hleast
  apply (DedekindZetaZeroFree.LargeSieve.Vendor.finite_band_average R S T L hL rowGood colGood f
    (fun i b => (Q.χ b) (P i)) (fun a b => (Q.χ b) a) (fun a b => (Q.χ b) a)
    hf
    (by intro i b hb; exact (htransport i).2.2.1 b hb)
    (by intro i b hb hgood; exact (htransport i).2.2.2.1 b hb hgood)
    (by intro i a b hb hgood; exact (htransport i).2.2.2.2 a.val b)
    ((d : ℝ) / δ) (B1 F c Q M N)
    (∑ j ∈ Finset.range (J + 1), B1 F c Q ((2 : ℝ) ^ j * Y) N)
    ht hleast'.1.1 hBT (by intro a ha; simpa only [rowGood, not_not] using hrowbad a ha)
    (by intro b hb; simpa only [colGood, not_not] using hcolbad b hb) hleast'.1.2
    (by simpa only [rowSum, energy] using htarget)).2 hleast' habsorb

theorem B1_bottom_eq_zero (F : Type) [Field F] [NumberField F]
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F ⊥)
    (M N : ℝ) (hM : 1 ≤ M) : B1 F ⊥ Q M N = 0 := by

  have hMshell : paperShell F ⊥ M = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro I hI
    rw [mem_paperShell] at hI
    obtain ⟨-, htop, hlt, -⟩ := hI
    have hItop : I = ⊤ := by simpa using htop
    rw [hItop, Ideal.absNorm_top] at hlt
    push_cast at hlt
    linarith
  have hQ1 : ∀ lam : Ideal (𝓞 F) → ℂ, Q1 F ⊥ Q M N lam = 0 := by
    intro lam
    simp [Q1, hMshell]
  rw [B1]
  have hset : ({0} ∪ {x : ℝ | ∃ lam : Ideal (𝓞 F) → ℂ,
      energy F ⊥ N lam ≤ 1 ∧ x = Q1 F ⊥ Q M N lam}) = {0} := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨lam, -, rfl⟩)
      · exact h
      · exact hQ1 lam
    · intro hx; exact Or.inl hx
  rw [hset, csSup_singleton]

end DedekindZetaZeroFree.LargeSieve.Sieve

end
