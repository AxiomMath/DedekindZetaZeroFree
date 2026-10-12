module

public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.PolynomialWeights

@[expose] public section

open Polynomial IntermediateField

namespace DavenportHasse

open scoped Classical

variable {k : Type*} [Field k] [Fintype k]

omit [Fintype k] in
lemma degree_sum_lt (d : ℕ) (c : Fin d → k) :
    (∑ i : Fin d, C (c i) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).2 fun i _ => ?_
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.2 i.2)

omit [Fintype k] in
lemma monicOfCoeffs_monic (d : ℕ) (c : Fin d → k) : (monicOfCoeffs d c).Monic :=
  monic_X_pow_add (degree_sum_lt d c)

omit [Fintype k] in
lemma monicOfCoeffs_natDegree (d : ℕ) (c : Fin d → k) : (monicOfCoeffs d c).natDegree = d := by
  unfold monicOfCoeffs
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]; exact degree_sum_lt d c

omit [Fintype k] in
lemma monicOfCoeffs_coeff (d : ℕ) (c : Fin d → k) (i : Fin d) :
    (monicOfCoeffs d c).coeff i = c i := by
  unfold monicOfCoeffs
  rw [coeff_add, coeff_X_pow, finsetSum_coeff, Fintype.sum_eq_single i]
  · simp [i.2.ne]
  · intro j hj
    have : (i : ℕ) ≠ j := fun h => hj (Fin.ext h.symm)
    simp [this]

omit [Fintype k] in
lemma monicOfCoeffs_eq_iff {P : k[X]} (hP : P.Monic) (d : ℕ) (c : Fin d → k) :
    monicOfCoeffs d c = P ↔ P.natDegree = d ∧ c = fun i : Fin d => P.coeff i := by
  constructor
  · rintro rfl
    exact ⟨monicOfCoeffs_natDegree d c, funext fun i => (monicOfCoeffs_coeff d c i).symm⟩
  · rintro ⟨rfl, rfl⟩
    conv_rhs => rw [hP.as_sum]
    unfold monicOfCoeffs
    rw [Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i)]

variable (E : Type*) [Field E] [Fintype E] [Algebra k E]

lemma card_minpoly_eq {P : k[X]} (hP : P.Monic) (hirr : Irreducible P)
    (hdvd : P.natDegree ∣ Module.finrank k E) :
    (Finset.univ.filter fun α : E => minpoly k α = P).card = P.natDegree := by
  have : Fact (Irreducible P) := ⟨hirr⟩
  have hK : Module.finrank k (AdjoinRoot P) = P.natDegree :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finrank
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := k) (K := AdjoinRoot P) (L := E)
    (hK ▸ hdvd)
  have hroot : aeval (f (AdjoinRoot.root P)) P = 0 := by
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hmin : P = minpoly k (f (AdjoinRoot.root P)) :=
    minpoly.eq_of_irreducible_of_monic hirr hroot hP
  have hsplit : Splits (P.map (algebraMap k E)) := by
    rw [hmin]; exact Normal.splits inferInstance _
  have hsep : P.Separable := PerfectField.separable_of_irreducible hirr
  rw [← card_rootSet_eq_natDegree hsep hsplit, ← Fintype.card_subtype]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun α => ?_)
  rw [mem_rootSet_of_ne hirr.ne_zero]
  constructor
  · rintro rfl; exact minpoly.aeval k α
  · intro h; exact (minpoly.eq_of_irreducible_of_monic hirr h hP).symm

omit [Fintype k] in
lemma norm_trace_eq (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (α : E) :
    χ (Algebra.norm k α) * ψ (Algebra.trace k E α) =
      wt χ ψ (minpoly k α) ^ (Module.finrank k E / (minpoly k α).natDegree) := by
  have hx : IsIntegral k α := .of_finite k α
  have hd : Module.finrank k k⟮α⟯ = (minpoly k α).natDegree := adjoin.finrank hx
  have hm : Module.finrank k E / (minpoly k α).natDegree = Module.finrank k⟮α⟯ E := by
    rw [← Module.finrank_mul_finrank k k⟮α⟯ E, hd,
      Nat.mul_div_cancel_left _ (minpoly.natDegree_pos hx)]
  rw [hm, Algebra.norm_eq_norm_adjoin, trace_eq_finrank_mul_minpoly_nextCoeff,
    ← adjoin.powerBasis_gen hx, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    adjoin.powerBasis_gen hx, minpoly_gen, adjoin.powerBasis_dim, wt, map_pow, ← nsmul_eq_mul,
    AddChar.map_nsmul_eq_pow, mul_pow]

lemma term_eq (χ : MulChar k ℂ) (ψ : AddChar k ℂ) {d : ℕ} (hd : d ∣ Module.finrank k E)
    (c : Fin d → k) :
    (if Irreducible (monicOfCoeffs d c) then
        (d : ℂ) * wt χ ψ (monicOfCoeffs d c) ^ (Module.finrank k E / d) else 0) =
      ∑ α : E, if minpoly k α = monicOfCoeffs d c then
        wt χ ψ (minpoly k α) ^ (Module.finrank k E / (minpoly k α).natDegree) else 0 := by
  split_ifs with hirr
  · rw [← Finset.sum_filter]
    have hdeg := monicOfCoeffs_natDegree d c
    rw [Finset.sum_congr rfl (g := fun _ => wt χ ψ (monicOfCoeffs d c) ^ (Module.finrank k E / d))
      (fun α hα => by rw [(Finset.mem_filter.1 hα).2, hdeg]), Finset.sum_const, nsmul_eq_mul,
      card_minpoly_eq E (monicOfCoeffs_monic d c) hirr (by rw [hdeg]; exact hd), hdeg]
  · refine (Finset.sum_eq_zero fun α _ => ?_).symm
    refine ite_eq_right_iff.2 fun h => ?_
    exact absurd (h ▸ minpoly.irreducible (.of_finite k α)) hirr

theorem sum_lifted_eq_b (E : Type*) [Field E] [Fintype E] [Algebra k E]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) :
    ∑ α : E, χ (Algebra.norm k α) * ψ (Algebra.trace k E α) = b χ ψ (Module.finrank k E) := by
  unfold b
  rw [Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun c _ =>
    term_eq E χ ψ (Nat.dvd_of_mem_divisors hd) c]
  rw [Finset.sum_congr rfl fun d _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [norm_trace_eq]
  have hx : IsIntegral k α := .of_finite k α
  have hmon := minpoly.monic hx
  set P := minpoly k α
  simp_rw [eq_comm (a := P), monicOfCoeffs_eq_iff hmon]
  rw [Finset.sum_eq_single P.natDegree]
  · rw [Finset.sum_eq_single (fun i : Fin P.natDegree => P.coeff i)]
    · simp
    · intro c _ hc; simp [hc]
    · simp
  · intro d _ hd
    exact Finset.sum_eq_zero fun c _ => ite_eq_right_iff.2 fun h => absurd h.1.symm hd
  · intro h
    exfalso; apply h
    rw [Nat.mem_divisors]
    refine ⟨?_, Module.finrank_pos.ne'⟩
    rw [← adjoin.finrank hx, ← Module.finrank_mul_finrank k k⟮α⟯ E]
    exact dvd_mul_right _ _

end DavenportHasse
