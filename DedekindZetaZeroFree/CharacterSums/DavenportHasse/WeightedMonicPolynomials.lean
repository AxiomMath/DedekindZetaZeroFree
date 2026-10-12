module

public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.PolynomialWeights

@[expose] public section

open Polynomial

namespace DavenportHasse.PolyPart

open scoped Classical

set_option linter.unusedSectionVars false

variable {k : Type*} [Field k] [Fintype k]

lemma sum_lt (d : ℕ) (c : Fin d → k) :
    (∑ i : Fin d, C (c i) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).2 fun i _ => ?_
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.2 i.2)

lemma moc_monic (d : ℕ) (c : Fin d → k) : (monicOfCoeffs d c).Monic :=
  monic_X_pow_add (sum_lt d c)

lemma moc_natDegree (d : ℕ) (c : Fin d → k) : (monicOfCoeffs d c).natDegree = d := by
  unfold monicOfCoeffs
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]; exact sum_lt d c

lemma moc_coeff (d : ℕ) (c : Fin d → k) (i : Fin d) :
    (monicOfCoeffs d c).coeff i = c i := by
  unfold monicOfCoeffs
  rw [coeff_add, coeff_X_pow, finsetSum_coeff, Fintype.sum_eq_single i]
  · simp [i.2.ne]
  · intro j hj
    simp only [coeff_C_mul_X_pow, ite_eq_right_iff]
    exact fun h => absurd (Fin.ext h.symm) hj

lemma moc_of_monic {P : k[X]} (hP : P.Monic) :
    monicOfCoeffs P.natDegree (fun i => P.coeff i) = P := by
  conv_rhs => rw [hP.as_sum]
  unfold monicOfCoeffs
  rw [Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i)]

lemma moc_injective (d : ℕ) : Function.Injective (monicOfCoeffs (k := k) d) := by
  intro c c' h
  funext i
  rw [← moc_coeff d c i, ← moc_coeff d c' i, h]

noncomputable def Mon (k : Type*) [Field k] [Fintype k] (d : ℕ) : Finset k[X] :=
  (Finset.univ : Finset (Fin d → k)).image (monicOfCoeffs d)

lemma mem_Mon {d : ℕ} {f : k[X]} : f ∈ Mon k d ↔ f.Monic ∧ f.natDegree = d := by
  unfold Mon
  rw [Finset.mem_image]
  constructor
  · rintro ⟨c, -, rfl⟩
    exact ⟨moc_monic d c, moc_natDegree d c⟩
  · rintro ⟨hm, rfl⟩
    exact ⟨_, Finset.mem_univ _, moc_of_monic hm⟩

lemma sum_Mon {M : Type*} [AddCommMonoid M] (d : ℕ) (F : k[X] → M) :
    ∑ c : Fin d → k, F (monicOfCoeffs d c) = ∑ f ∈ Mon k d, F f := by
  unfold Mon
  rw [Finset.sum_image fun x _ y _ h => moc_injective d h]

variable (χ : MulChar k ℂ) (ψ : AddChar k ℂ)

lemma wt_mul {f g : k[X]} (hf : f.Monic) (hg : g.Monic) :
    wt χ ψ (f * g) = wt χ ψ f * wt χ ψ g := by
  unfold wt
  rw [hf.natDegree_mul hg, mul_coeff_zero, hf.nextCoeff_mul hg, neg_add,
    AddChar.map_add_eq_mul, pow_add,
    show (-1 : k) ^ f.natDegree * (-1) ^ g.natDegree * (f.coeff 0 * g.coeff 0) =
      ((-1) ^ f.natDegree * f.coeff 0) * ((-1) ^ g.natDegree * g.coeff 0) by ring, map_mul]
  ring

lemma wt_one : wt χ ψ (1 : k[X]) = 1 := by
  simp [wt, nextCoeff]

lemma wt_pow {f : k[X]} (hf : f.Monic) (j : ℕ) : wt χ ψ (f ^ j) = wt χ ψ f ^ j := by
  induction j with
  | zero => simp [wt_one]
  | succ j ih => rw [pow_succ, wt_mul χ ψ (hf.pow j) hf, ih, pow_succ]

lemma a_zero : a χ ψ 0 = 1 := by
  simp [a, monicOfCoeffs, wt_one]

lemma a_one : a χ ψ 1 = gaussSum χ ψ := by
  unfold a gaussSum
  refine Fintype.sum_equiv ((Equiv.funUnique (Fin 1) k).trans (Equiv.neg k)) _ _ fun c => ?_
  have h : monicOfCoeffs 1 c = X + C (c 0) := by simp [monicOfCoeffs]
  simp [h, wt, nextCoeff_X_add_C]

lemma a_eq_zero (hψ : ∃ x : k, ψ x ≠ 1) {d : ℕ} (hd : 2 ≤ d) : a χ ψ d = 0 := by
  obtain ⟨t, ht⟩ := hψ
  have hd0 : 0 < d := by omega
  set i : Fin d := ⟨d - 1, by omega⟩
  set i0 : Fin d := ⟨0, hd0⟩
  have hne : i0 ≠ i := by simp [i0, i, Fin.ext_iff]; omega
  have hw : ∀ c : Fin d → k,
      wt χ ψ (monicOfCoeffs d c) = χ ((-1) ^ d * c i0) * ψ (-c i) := by
    intro c
    unfold wt
    rw [moc_natDegree, nextCoeff_of_natDegree_pos (by rw [moc_natDegree]; exact hd0),
      moc_natDegree]
    have h0 := moc_coeff d c i0
    have h1 := moc_coeff d c i
    simp only [i0, i] at h0 h1 ⊢
    rw [h0, h1]
  unfold a
  simp_rw [hw]
  set S := ∑ c : Fin d → k, χ ((-1) ^ d * c i0) * ψ (-c i)
  have hS : S = ψ t * S := by
    have := Fintype.sum_equiv (Equiv.addRight (Pi.single i (-t) : Fin d → k))
      (fun c => χ ((-1) ^ d * (c + (Pi.single i (-t) : Fin d → k)) i0) *
        ψ (-(c + (Pi.single i (-t) : Fin d → k)) i))
      (fun c => χ ((-1) ^ d * c i0) * ψ (-c i)) (fun c => rfl)
    refine this.symm.trans ?_
    simp only [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, add_zero, neg_add,
      neg_neg, AddChar.map_add_eq_mul]
    ring
  have h1 : (1 - ψ t) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd (sub_eq_zero.1 h).symm ht
  · exact h

end DavenportHasse.PolyPart
