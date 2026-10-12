module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Coefficients.RectangleEnvelopesAndEnergies
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.PrimitivePairPhaseSeparation

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def SupportedTransport (C : Context Q) (B : ℝ) (unit : Bool) (J : ℕ) : Prop :=
  ∀ e ∈ C.mobiusDivisors, ∀ t ∈ squarefreeBadPool c,
    ∃ x y : Fin J → Ideal (𝓞 F) → ℂ,
      (∀ i u, ‖x i u‖ ≤ 1) ∧ (∀ i v, ‖y i v‖ ≤ 1) ∧
      ∀ p ∈ C.pairs, ∀ hp : Context.ValidPair C p,
      ∀ r ∈ C.reflectedCoreRows B unit,
        C.primitive p hp e * C.primitive p hp (t * r) =
          ∑ i : Fin J, x i p.1 * star (y i p.2) *
            (Q.χ p.1) r * star ((Q.χ p.2) r)

private lemma sup_mul {a b d : Ideal (𝓞 F)} (hab : a ⊔ b = ⊤)
    (had : a ⊔ d = ⊤) : a ⊔ b * d = ⊤ :=
  ((Ideal.isCoprime_iff_sup_eq.mpr hab).mul_right
    (Ideal.isCoprime_iff_sup_eq.mpr had)).sup_eq

private lemma rel_of_sup {a b : Ideal (𝓞 F)} (h : a ⊔ b = ⊤) : IsRelPrime a b := by
  intro z hz hz'
  apply Ideal.isUnit_iff.mpr
  apply top_unique
  rw [← h]
  exact sup_le (Ideal.dvd_iff_le.mp hz) (Ideal.dvd_iff_le.mp hz')

private lemma sup_of_rel {a b : Ideal (𝓞 F)} (h : IsRelPrime a b) : a ⊔ b = ⊤ :=
  Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr le_sup_left)
    (Ideal.dvd_iff_le.mpr le_sup_right))

private lemma column_spec (C : Context Q) {u : Ideal (𝓞 F)} (hu : u ∈ C.columns) :
    Squarefree u ∧ u ⊔ c = ⊤ ∧ u ⊔ C.d = ⊤ ∧ Q.cls (C.d * u) = C.g := by
  obtain ⟨hu, hdu, hcl⟩ := Finset.mem_filter.mp hu
  have hus := (Sieve.mem_idealAdmissibleFinset F c _ u).mp hu
  have hdus := (Sieve.mem_paperShell F c C.N (C.d * u)).mp hdu
  exact ⟨hus.1, hus.2.1, by simpa only [sup_comm] using
    (sup_of_rel (squarefree_mul_iff.mp hdus.1).1), hcl⟩

private lemma core_spec (C : Context Q) {B : ℝ} {unit : Bool} {r : Ideal (𝓞 F)}
    (hr : r ∈ C.reflectedCoreRows B unit) : r ⊔ c = ⊤ := by
  cases unit with
  | false => exact ((Sieve.mem_paperShell F c B r).mp (Finset.mem_filter.mp hr).1).2.1
  | true => exact (Finset.mem_filter.mp hr).2.2.1

private lemma primitive_core (C : Context Q)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
    (a : Ideal (𝓞 F)) (hac : a ⊔ c = ⊤) :
    C.primitive p hp a = (Q.χ p.1) a * star ((Q.χ p.2) a) := by
  by_cases ha0 : a = ⊥
  · subst a
    simp [RayOperations.map_bot]
  have hupper : ∀ u, Squarefree u → u ⊔ c = ⊤ → a ⊔ u = ⊤ →
      a ⊔ Q.cond u = ⊤ := by
    intro u hu huc hau
    have h : Q.cond u ∣ u * c := by
      simpa only [C.core] using C.D.all_conductor_dvd u hu huc
    exact top_unique ((sup_mul hau hac).symm.trans_le
      (sup_le_sup_left (Ideal.dvd_iff_le.mp h) a))
  have hlower : ∀ u, Squarefree u → u ⊔ c = ⊤ → a ⊔ u ≠ ⊤ →
      a ⊔ Q.cond u ≠ ⊤ := by
    intro u hu huc hau hcond
    have h : u ∣ Q.cond u := C.D.index_dvd_conductor u hu (by simpa [C.core] using huc)
    exact hau (top_unique (hcond.symm.trans_le
      (sup_le_sup_left (Ideal.dvd_iff_le.mp h) a)))
  by_cases hauv : a ⊔ (p.1 * p.2) = ⊤
  · have hau : a ⊔ p.1 = ⊤ := top_unique (hauv.symm.trans_le
        (sup_le_sup_left Ideal.mul_le_left a))
    have hav : a ⊔ p.2 = ⊤ := top_unique (hauv.symm.trans_le
        (sup_le_sup_left Ideal.mul_le_right a))
    exact (C.primitive_spec p hp).2.1 a
      (sup_mul (hupper _ hp.hu hp.huc hau) (hupper _ hp.hv hp.hvc hav))
  · have hzero : C.primitive p hp a = 0 :=
      ((C.primitive p hp).eq_zero_iff' a).mpr (Or.inr hauv)
    have hor : a ⊔ p.1 ≠ ⊤ ∨ a ⊔ p.2 ≠ ⊤ := by
      by_contra h
      push Not at h
      exact hauv (sup_mul h.1 h.2)
    rcases hor with hu | hv
    · have hz := ((Q.χ p.1).eq_zero_iff' a).mpr (Or.inr (hlower _ hp.hu hp.huc hu))
      simp [hzero, hz]
    · have hz := ((Q.χ p.2).eq_zero_iff' a).mpr (Or.inr (hlower _ hp.hv hp.hvc hv))
      simp [hzero, hz]

set_option maxHeartbeats 1000000 in

theorem primitive_supported_transport (D : Sieve.AllIndexNormalizedFamilyData Q) :
    ∃ J : ℕ, 0 < J ∧
      ∀ C : Context Q, C.D = D →
      ∀ B : ℝ, ∀ unit : Bool, (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        SupportedTransport C B unit J := by
  refine ⟨1, by decide, ?_⟩
  intro C hD B unit hunit hM hN hB hBK hKM
  have hc : c ≠ ⊥ := C.D.original_ne_bot
  have hS : ∀ u ∈ C.columns, Squarefree u ∧ u ⊔ c = ⊤ := by
    intro u hu
    exact ⟨(column_spec C hu).1, (column_spec C hu).2.1⟩
  have hclass : ∀ u ∈ C.columns, ∀ v ∈ C.columns, Q.cls u = Q.cls v := by
    intro u hu v hv
    have hh := (column_spec C hu).2.2.2.trans (column_spec C hv).2.2.2.symm
    rw [Q.cls_mul C.d u C.hdc (hS u hu).2, Q.cls_mul C.d v C.hdc (hS v hv).2] at hh
    exact mul_left_cancel hh
  obtain ⟨phase, hn, hphase⟩ :=
    PrimitivePhases.primitive_pair_phase_separation Q hc C.columns hS hclass
  intro e he t ht
  let z := e * t
  have he0 : e ≠ ⊥ := ne_bot_of_mem_idealDivisors he
  have htS := (mem_squarefreeBadPool hc).mp ht
  have hz0 : z ≠ ⊥ := mul_ne_zero he0 htS.1
  have hzcols : ∀ u ∈ C.columns, z ⊔ u = ⊤ := by
    intro u hu
    have hs := column_spec C hu
    have hr0 : (c * C.d).radical ≠ ⊥ := by
      intro h
      exact (mul_ne_zero hc C.hd0) (bot_unique (h ▸ Ideal.le_radical))
    have hediv : e ∣ c * C.d :=
      ((mem_idealDivisors hr0).mp he).trans (Ideal.dvd_iff_le.mpr Ideal.le_radical)
    have hue : u ⊔ e = ⊤ := top_unique ((sup_mul hs.2.1 hs.2.2.1).symm.trans_le
      (sup_le_sup_left (Ideal.dvd_iff_le.mp hediv) u))
    have hut : u ⊔ t = ⊤ := by
      apply sup_of_rel
      apply IsRelPrime.symm
      apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors htS.1).mpr
      intro p hpt hpu hp
      exact hp.not_isUnit ((rel_of_sup hs.2.1) hpu (htS.2.2 p hp hpt))
    exact (by simpa only [sup_comm] using sup_mul hue hut)
  let f : Ideal (𝓞 F) → ℂ := fun u => if u ∈ C.columns then phase u z else 0
  refine ⟨fun _ => f, fun _ => f, ?_, ?_, ?_⟩
  · intro i u
    dsimp [f]
    split_ifs with hu
    · exact hn u hu z
    · simp
  · intro i u
    dsimp [f]
    split_ifs with hu
    · exact hn u hu z
    · simp
  intro p hp hpv r hr
  have hpc := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1)
  have hz := hphase p.1 hpc.1 p.2 hpc.2 hpv.huv (C.primitive p hpv)
    (C.primitive_spec p hpv).2.1 z hz0 hzcols
  have hcore := primitive_core C p hpv r (core_spec C hr)
  have hmul : C.primitive p hpv e * C.primitive p hpv (t * r) =
      C.primitive p hpv z * C.primitive p hpv r := by
    rw [(C.primitive p hpv).map_mul', (C.primitive p hpv).map_mul']
    exact (mul_assoc _ _ _).symm
  rw [hmul, hz, hcore]
  simp only [Fin.sum_univ_one, f, if_pos hpc.1, if_pos hpc.2]
  ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin

end
