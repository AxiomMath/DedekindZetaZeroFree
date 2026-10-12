module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.UniformConductorControl
public import DedekindZetaZeroFree.Arithmetic.Ideals.ExceptionalSquarefreeDecomposition

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

local instance exceptionalMasksClassGroup (Q : QuadraticHeckeFamily F c) : Group Q.G := Q.instGroup
local instance exceptionalMasksClassGroupFinite (Q : QuadraticHeckeFamily F c) : Finite Q.G := Q.instFinite
noncomputable local instance exceptionalMasksClassGroupFintype (Q : QuadraticHeckeFamily F c) : Fintype Q.G :=
  Fintype.ofFinite Q.G

private lemma sup_eq_top_of_le_of_sup_eq_top {a b d : Ideal (𝓞 F)}
    (h : a ⊔ b = ⊤) (hbd : b ≤ d) : a ⊔ d = ⊤ := by
  rw [eq_top_iff]
  calc ⊤ = a ⊔ b := h.symm
    _ ≤ a ⊔ d := sup_le_sup_left hbd a

private lemma exists_prime_dvd_of_sup_ne_top {u v : Ideal (𝓞 F)} (h : u ⊔ v ≠ ⊤) :
    ∃ p : Ideal (𝓞 F), p.IsPrime ∧ p ∣ u ∧ p ∣ v := by
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (u ⊔ v) h
  exact ⟨p, hp.isPrime, Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle),
    Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle)⟩

private lemma prime_dvd_cond_of_dvd_of_not_dvd_q (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F))
    (H : ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
      Q.cond b ∣ b * q ∧ b ∣ Q.cond b * q)
    {b p : Ideal (𝓞 F)} (hb : Squarefree b) (hbc : b ⊔ c = ⊤)
    (hp : p.IsPrime) (hpb : p ∣ b) (hpq : ¬ p ∣ q) : p ∣ Q.cond b := by
  have hbq : p ∣ Q.cond b * q := dvd_trans hpb (H b hb hbc).2
  rw [Ideal.dvd_iff_le] at hbq ⊢
  rcases (Ideal.IsPrime.mul_le hp).mp hbq with h | h
  · exact h
  · exact absurd (Ideal.dvd_iff_le.mpr h) hpq

private lemma sup_mul_eq_top_of_sup_eq_top_of_sup_eq_top {t u v : Ideal (𝓞 F)}
    (ht : t ⊔ v = ⊤) (hu : u ⊔ v = ⊤) : t * u ⊔ v = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hptu, hpv⟩ := exists_prime_dvd_of_sup_ne_top h
  rw [Ideal.dvd_iff_le] at hptu hpv
  rcases (Ideal.IsPrime.mul_le hp).mp hptu with h | h
  · exact hp.ne_top (top_le_iff.mp (ht ▸ sup_le h hpv))
  · exact hp.ne_top (top_le_iff.mp (hu ▸ sup_le h hpv))

noncomputable def exceptionalColumnMask (Q : QuadraticHeckeFamily F c)
    (r t : Ideal (𝓞 F)) (g : Q.G) (u : Ideal (𝓞 F)) : ℂ :=
  if Q.cls u = g then (Q.χ (t * u)) r else 0

def exceptionalRowMask (Q : QuadraticHeckeFamily F c)
    (t : Ideal (𝓞 F)) (g : Q.G) (v : Ideal (𝓞 F)) : ℂ :=
  (Q.χ v) t * Q.C (Q.cls t * g) (Q.cls v) * Q.C (Q.cls v) g

theorem peeling_mask_transport (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (H : ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
      Q.cond b ∣ b * q ∧ b ∣ Q.cond b * q)
    (r t u v : Ideal (𝓞 F))
    (hr : r ∈ exceptionalDivisors F c q) (ht : t ∈ exceptionalDivisors F c q)
    (hu : Squarefree u) (huq : u ⊔ q = ⊤)
    (hv : Squarefree v) (hvq : v ⊔ q = ⊤) :
    (Q.χ (t * u)) (r * v) =
      (Q.χ (t * u)) r * (Q.χ v) t * (Q.χ u) v *
        Q.C (Q.cls t * Q.cls u) (Q.cls v) * Q.C (Q.cls v) (Q.cls u) := by
  obtain ⟨-, -, ht_dvd, htc, -⟩ := exceptionalDivisors_properties hq ht
  have htu_sq : Squarefree (t * u) :=
    (exceptional_decomposition_converse hq hcq ht hu huq).1
  have htu_c : t * u ⊔ c = ⊤ :=
    (exceptional_decomposition_converse hq hcq ht hu huq).2
  have huc : u ⊔ c = ⊤ := sup_eq_top_of_le_of_sup_eq_top huq (Ideal.dvd_iff_le.mp hcq)
  have hvc : v ⊔ c = ⊤ := sup_eq_top_of_le_of_sup_eq_top hvq (Ideal.dvd_iff_le.mp hcq)
  by_cases huv : u ⊔ v = ⊤
  · have htuv : t ⊔ v = ⊤ := by
      rw [sup_comm]
      exact sup_eq_top_of_le_of_sup_eq_top hvq (Ideal.dvd_iff_le.mp ht_dvd)
    have htuv' : t * u ⊔ v = ⊤ :=
      sup_mul_eq_top_of_sup_eq_top_of_sup_eq_top htuv huv
    have hrec1 := Q.reciprocity (t * u) v htu_sq htu_c hv hvc htuv'
    have huv' : v ⊔ u = ⊤ := by rw [sup_comm]; exact huv
    have hrec2 := Q.reciprocity v u hv hvc hu huc huv'
    have hcls : Q.cls (t * u) = Q.cls t * Q.cls u := Q.cls_mul t u htc huc
    rw [(Q.χ (t * u)).map_mul' r v, hrec1, (Q.χ v).map_mul' t u, hrec2, hcls]
    ring
  · obtain ⟨p, hp, hpu, hpv⟩ := exists_prime_dvd_of_sup_ne_top huv
    have hpq : ¬ p ∣ q := by
      intro hpq
      rw [Ideal.dvd_iff_le] at hpu hpq
      exact hp.ne_top (top_le_iff.mp (huq ▸ sup_le hpu hpq))
    have hpcond_u : p ∣ Q.cond u :=
      prime_dvd_cond_of_dvd_of_not_dvd_q Q q H hu huc hp hpu hpq
    have hptu : p ∣ t * u := dvd_trans hpu (dvd_mul_left u t)
    have hpcond_tu : p ∣ Q.cond (t * u) :=
      prime_dvd_cond_of_dvd_of_not_dvd_q Q q H htu_sq htu_c hp hptu hpq
    have hL : (Q.χ (t * u)) (r * v) = 0 := by
      rw [quadraticFamily_eq_zero_iff Q htu_sq htu_c (r * v)]
      right
      intro hcop
      rw [Ideal.dvd_iff_le] at hpcond_tu
      have hpv' : p ∣ r * v := dvd_trans hpv (dvd_mul_left v r)
      rw [Ideal.dvd_iff_le] at hpv'
      exact hp.ne_top (top_le_iff.mp (hcop ▸ sup_le hpv' hpcond_tu))
    have hχuv : (Q.χ u) v = 0 := by
      rw [quadraticFamily_eq_zero_iff Q hu huc v]
      right
      intro hcop
      rw [Ideal.dvd_iff_le] at hpcond_u hpv
      exact hp.ne_top (top_le_iff.mp (hcop ▸ sup_le hpv hpcond_u))
    rw [hL, hχuv]
    ring

theorem norm_exceptionalColumnMask_le_one (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (r t : Ideal (𝓞 F)) (g : Q.G) (u : Ideal (𝓞 F))
    (hr : r ∈ exceptionalDivisors F c q) (ht : t ∈ exceptionalDivisors F c q)
    (hu : Squarefree u) (huq : u ⊔ q = ⊤) :
    ‖exceptionalColumnMask Q r t g u‖ ≤ 1 := by
  have htu_sq : Squarefree (t * u) :=
    (exceptional_decomposition_converse hq hcq ht hu huq).1
  have htu_c : t * u ⊔ c = ⊤ :=
    (exceptional_decomposition_converse hq hcq ht hu huq).2
  by_cases h : Q.cls u = g
  · rw [exceptionalColumnMask, if_pos h]
    exact quadraticFamily_norm_le_one Q htu_sq htu_c r
  · rw [exceptionalColumnMask, if_neg h]
    simp

theorem norm_exceptionalRowMask_le_one (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (t : Ideal (𝓞 F)) (g : Q.G) (v : Ideal (𝓞 F))
    (ht : t ∈ exceptionalDivisors F c q)
    (hv : Squarefree v) (hvq : v ⊔ q = ⊤) :
    ‖exceptionalRowMask Q t g v‖ ≤ 1 := by
  have hvc : v ⊔ c = ⊤ := sup_eq_top_of_le_of_sup_eq_top hvq (Ideal.dvd_iff_le.mp hcq)
  rw [exceptionalRowMask, norm_mul, norm_mul, ClassTwists.norm_C, ClassTwists.norm_C,
    mul_one, mul_one]
  exact quadraticFamily_norm_le_one Q hv hvc t

theorem peeling_mask_transport_sum (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (H : ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
      Q.cond b ∣ b * q ∧ b ∣ Q.cond b * q)
    (r t v : Ideal (𝓞 F))
    (hr : r ∈ exceptionalDivisors F c q) (ht : t ∈ exceptionalDivisors F c q)
    (hv : Squarefree v) (hvq : v ⊔ q = ⊤)
    (U : Finset (Ideal (𝓞 F)))
    (hU : ∀ u ∈ U, Squarefree u ∧ u ⊔ q = ⊤)
    (lam : Ideal (𝓞 F) → ℂ) :
    (∑ u ∈ U, lam (t * u) * (Q.χ (t * u)) (r * v)) =
      ∑ g : Q.G, exceptionalRowMask Q t g v *
        (∑ u ∈ U, lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v) := by
  have hmain : ∀ u ∈ U, lam (t * u) * (Q.χ (t * u)) (r * v) =
      ∑ g : Q.G, exceptionalRowMask Q t g v *
        (lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v) := by
    intro u huU
    obtain ⟨hu_sq, hu_q⟩ := hU u huU
    rw [peeling_mask_transport Q q hq hcq H r t u v hr ht hu_sq hu_q hv hvq]
    have hsum : (∑ g : Q.G, exceptionalRowMask Q t g v *
        (lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)) =
        exceptionalRowMask Q t (Q.cls u) v *
          (lam (t * u) * exceptionalColumnMask Q r t (Q.cls u) u * (Q.χ u) v) :=
      Finset.sum_eq_single (Q.cls u)
        (fun b _ hb => by rw [exceptionalColumnMask, if_neg (Ne.symm hb)]; ring)
        (fun hmem => absurd (Finset.mem_univ _) hmem)
    rw [hsum, exceptionalRowMask, exceptionalColumnMask, if_pos rfl]
    ring
  calc (∑ u ∈ U, lam (t * u) * (Q.χ (t * u)) (r * v))
      = ∑ u ∈ U, ∑ g : Q.G, exceptionalRowMask Q t g v *
          (lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v) :=
        Finset.sum_congr rfl fun u huU => hmain u huU
    _ = ∑ g : Q.G, ∑ u ∈ U, exceptionalRowMask Q t g v *
          (lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v) :=
        Finset.sum_comm
    _ = ∑ g : Q.G, exceptionalRowMask Q t g v *
          (∑ u ∈ U, lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v) :=
        Finset.sum_congr rfl fun g _ => (Finset.mul_sum _ _ _).symm

end DedekindZetaZeroFree.LargeSieve.Sieve
