module

public import DedekindZetaZeroFree.Theta.RayClasses.ZeroModeCancellation
public import DedekindZetaZeroFree.Theta.RayClasses.AveragedContinuity
public import DedekindZetaZeroFree.Theta.RayClasses.ZeroModeTail

@[expose] public section

noncomputable section

open scoped NumberField
open MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]
variable {m : Ideal (𝓞 F)} {hm : m ≠ ⊥}

theorem normalizedRayTheta_continuousOn
    (D : RayThetaRepresentatives F m hm)
    {η : DedekindZetaZeroFree.RayClassCharacter F m}
    (χ : RayCharacterData F m hm η) :
    ContinuousOn (normalizedRayTheta D χ.ψ) (Set.Ioi (0 : ℝ)) := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  unfold normalizedRayTheta
  apply continuousOn_const.mul
  apply continuousOn_finset_sum
  intro c hc
  apply continuousOn_const.mul
  exact (DedekindZetaZeroFree.rayTheta_continuousOn_fδ (D.coset c) ∅).comp
    (continuous_id.div_const _).continuousOn
    (fun t ht => div_pos ht (conductorScale_pos hm))

theorem normalizedRayConjugateTheta_continuousOn
    (D : RayThetaRepresentatives F m hm)
    {η : DedekindZetaZeroFree.RayClassCharacter F m}
    (χ : RayCharacterData F m hm η) :
    ContinuousOn (normalizedRayConjugateTheta D χ.ψ) (Set.Ioi (0 : ℝ)) := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  unfold normalizedRayConjugateTheta
  apply continuousOn_const.mul
  apply continuousOn_finset_sum
  intro c hc
  apply continuousOn_const.mul
  exact (DedekindZetaZeroFree.rayTheta_continuousOn_fδ (D.coset c) ∅).comp
    (continuous_id.div_const _).continuousOn
    (fun t ht => div_pos ht (conductorScale_pos hm))

theorem normalizedRayTheta_locallyIntegrableOn
    (D : RayThetaRepresentatives F m hm)
    {η : DedekindZetaZeroFree.RayClassCharacter F m}
    (χ : RayCharacterData F m hm η) :
    LocallyIntegrableOn (normalizedRayTheta D χ.ψ) (Set.Ioi (0 : ℝ)) := by
  exact (normalizedRayTheta_continuousOn D χ).locallyIntegrableOn measurableSet_Ioi

theorem normalizedRayConjugateTheta_locallyIntegrableOn
    (D : RayThetaRepresentatives F m hm)
    {η : DedekindZetaZeroFree.RayClassCharacter F m}
    (χ : RayCharacterData F m hm η) :
    LocallyIntegrableOn (normalizedRayConjugateTheta D χ.ψ) (Set.Ioi (0 : ℝ)) := by
  exact (normalizedRayConjugateTheta_continuousOn D χ).locallyIntegrableOn measurableSet_Ioi

private theorem tail_rate_mono (a b p t : ℝ) (hab : a ≤ b) (ht : 0 ≤ t) :
    Real.exp (-b * t ^ p) ≤ Real.exp (-a * t ^ p) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hab) (Real.rpow_nonneg ht p)

private theorem tail_rescale (f : ℝ → ℂ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hf : ContinuousOn f (Set.Ioi 0))
    (h : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t, 1 ≤ t →
      ‖f t‖ ≤ A * Real.exp (-B * t ^ p)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t, 1 ≤ t →
      ‖f (q * t)‖ ≤ A * Real.exp (-B * t ^ p) := by
  obtain ⟨A, B, hA, hB, hb⟩ := h
  let b := B * q ^ p
  have hbpos : 0 < b := mul_pos hB (Real.rpow_pos_of_pos hq p)
  let T := max 1 (1 / q)
  have hfc : ContinuousOn (fun t => f (q * t)) (Set.Ioi 0) :=
    hf.comp (continuous_const.mul continuous_id).continuousOn
      (fun t ht => mul_pos hq ht)
  have hec : Continuous (fun t : ℝ => Real.exp (b * t ^ p)) :=
    Real.continuous_exp.comp (continuous_const.mul (Real.continuous_rpow_const hp.le))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hfc.norm.mul hec.continuousOn).mono
      (show Set.Icc 1 T ⊆ Set.Ioi 0 from fun t ht => lt_of_lt_of_le zero_lt_one ht.1))
  refine ⟨A + |M| + 1, b, by positivity, hbpos, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  by_cases hT : T ≤ t
  · have hqt : 1 ≤ q * t := by
      have h := (le_max_right 1 (1 / q)).trans hT
      have h' := (div_le_iff₀ hq).mp h
      simpa [mul_comm] using h'
    have H := hb (q * t) hqt
    rw [Real.mul_rpow hq.le ht0] at H
    have heq : -B * (q ^ p * t ^ p) = -b * t ^ p := by dsimp [b]; ring
    rw [heq] at H
    exact H.trans (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M])
      (Real.exp_pos _).le)
  · have H := hM t ⟨ht, le_of_not_ge hT⟩
    have H' : ‖f (q * t)‖ * Real.exp (b * t ^ p) ≤ A + |M| + 1 := by
      simp only [Real.norm_eq_abs] at H
      have H0 : ‖f (q * t)‖ * Real.exp (b * t ^ p) ≤ M :=
        (le_abs_self _).trans H
      linarith [le_abs_self M]
    have H'' := (le_div_iff₀ (Real.exp_pos (b * t ^ p))).mpr H'
    simpa [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using H''

private theorem tail_mul (f : ℝ → ℂ) (p : ℝ) (c : ℂ)
    (h : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t, 1 ≤ t →
      ‖f t‖ ≤ A * Real.exp (-B * t ^ p)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t, 1 ≤ t →
      ‖c * f t‖ ≤ A * Real.exp (-B * t ^ p) := by
  obtain ⟨A, B, hA, hB, hb⟩ := h
  refine ⟨(‖c‖ + 1) * A, B, mul_pos (by positivity) hA, hB, ?_⟩
  intro t ht
  rw [norm_mul]
  calc
    _ ≤ ‖c‖ * (A * Real.exp (-B * t ^ p)) :=
      mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _)
    _ ≤ (‖c‖ + 1) * (A * Real.exp (-B * t ^ p)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

private theorem tail_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (p : ℝ)
    (h : ∀ i ∈ s, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t, 1 ≤ t →
      ‖f i t‖ ≤ A * Real.exp (-B * t ^ p)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t, 1 ≤ t →
      ‖∑ i ∈ s, f i t‖ ≤ A * Real.exp (-B * t ^ p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, 1, one_pos, one_pos, ?_⟩
      intro t ht
      simpa using (Real.exp_pos (-1 * t ^ p)).le
  | @insert i s hi ih =>
      obtain ⟨A, B, hA, hB, hb⟩ := h i (Finset.mem_insert_self i s)
      obtain ⟨C, D, hC, hD, hd⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      refine ⟨A + C, min B D, add_pos hA hC, lt_min hB hD, ?_⟩
      intro t ht
      rw [Finset.sum_insert hi]
      have ht0 : 0 ≤ t := le_trans zero_le_one ht
      calc
        _ ≤ ‖f i t‖ + ‖∑ j ∈ s, f j t‖ := norm_add_le _ _
        _ ≤ A * Real.exp (-B * t ^ p) + C * Real.exp (-D * t ^ p) :=
          add_le_add (hb t ht) (hd t ht)
        _ ≤ A * Real.exp (-(min B D) * t ^ p) + C * Real.exp (-(min B D) * t ^ p) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (tail_rate_mono _ _ _ _ (min_le_left _ _) ht0) hA.le)
            (mul_le_mul_of_nonneg_left (tail_rate_mono _ _ _ _ (min_le_right _ _) ht0) hC.le)
        _ = _ := (add_mul _ _ _).symm

theorem normalizedRayTheta_tail_bound
    (D : RayThetaRepresentatives F m hm)
    {η : DedekindZetaZeroFree.RayClassCharacter F m}
    (χ : RayCharacterData F m hm η) (hη : ¬ η.IsPrincipal) :
    0 < 2 / (Module.finrank ℚ F : ℝ) ∧
    ∃ C b : ℝ, 0 < C ∧ 0 < b ∧ ∀ t : ℝ, 1 ≤ t →
      ‖normalizedRayTheta D χ.ψ t‖ ≤
        C * Real.exp (-b * t ^ (2 / (Module.finrank ℚ F : ℝ))) ∧
      ‖normalizedRayDualTheta D χ.ψ t‖ ≤
        C * Real.exp (-b * t ^ (2 / (Module.finrank ℚ F : ℝ))) ∧
      ‖normalizedRayConjugateTheta D χ.ψ t‖ ≤
        C * Real.exp (-b * t ^ (2 / (Module.finrank ℚ F : ℝ))) := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  let p : ℝ := 2 / (Module.finrank ℚ F : ℝ)
  have hp : 0 < p := div_pos (by norm_num)
    (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := F)))
  refine ⟨hp, ?_⟩
  have hf : ∀ c : RayIdealClass F m hm, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ t, 1 ≤ t →
        ‖RayTheta.fδ (D.coset c) ∅ (t / conductorScale F m) -
          RayTheta.f0δ (D.coset c) ∅‖ ≤ A * Real.exp (-B * t ^ p) := by
    intro c
    have H := DedekindZetaZeroFree.rayTheta_zeroModeTail F (D.coset c) ∅
    obtain ⟨A, B, hA, hB, hb⟩ := H
    have H' := tail_rescale
      (fun t => RayTheta.fδ (D.coset c) ∅ t - RayTheta.f0δ (D.coset c) ∅)
      p (conductorScale F m)⁻¹ hp (inv_pos.mpr (conductorScale_pos hm))
      ((DedekindZetaZeroFree.rayTheta_continuousOn_fδ (D.coset c) ∅).sub continuousOn_const)
      ⟨A, B, hA, hB, fun t ht => (hb t ht).1⟩
    simpa [div_eq_mul_inv, mul_comm] using H'
  have hg : ∀ c : RayIdealClass F m hm, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ t, 1 ≤ t →
        ‖RayTheta.gδDual (D.coset c) ∅ (conductorScale F m * t) -
          RayTheta.g0δ (D.coset c) ∅‖ ≤ A * Real.exp (-B * t ^ p) := by
    intro c
    obtain ⟨A, B, hA, hB, hb⟩ :=
      DedekindZetaZeroFree.rayTheta_zeroModeTail F (D.coset c) ∅
    exact tail_rescale
      (fun t => RayTheta.gδDual (D.coset c) ∅ t - RayTheta.g0δ (D.coset c) ∅)
      p (conductorScale F m) hp (conductorScale_pos hm)
      ((DedekindZetaZeroFree.rayTheta_continuousOn_gδDual (D.coset c) ∅).sub continuousOn_const)
      ⟨A, B, hA, hB, fun t ht => (hb t ht).2⟩
  have hprimal : ∀ k : RayIdealClass F m hm → ℂ,
      ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t, 1 ≤ t →
        ‖(4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
          ∑ c, k c * (RayTheta.fδ (D.coset c) ∅ (t / conductorScale F m) -
            RayTheta.f0δ (D.coset c) ∅)‖ ≤ A * Real.exp (-B * t ^ p) := by
    intro k
    exact tail_mul _ p _ (tail_sum Finset.univ _ p (fun c _ => tail_mul _ p (k c) (hf c)))
  obtain ⟨A1, B1, hA1, hB1, hb1⟩ := hprimal χ.ψ
  obtain ⟨A3, B3, hA3, hB3, hb3⟩ := hprimal (fun c => (starRingEnd ℂ) (χ.ψ c))
  obtain ⟨A2, B2, hA2, hB2, hb2⟩ :=
    tail_mul _ p ((4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
      (conductorScale F m : ℂ))
      (tail_sum Finset.univ _ p (fun c _ => tail_mul _ p (χ.ψ c) (hg c)))
  let C := A1 + A2 + A3
  let b := min B1 (min B2 B3)
  have hb : 0 < b := lt_min hB1 (lt_min hB2 hB3)
  refine ⟨C, b, by dsimp [C]; positivity, hb, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have H : ∀ A B : ℝ, 0 < A → A ≤ C → b ≤ B →
      A * Real.exp (-B * t ^ p) ≤ C * Real.exp (-b * t ^ p) := by
    intro A B hA hAC hbB
    exact (mul_le_mul_of_nonneg_left (tail_rate_mono b B p t hbB htpos.le) hA.le).trans
      (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)
  rw [normalizedRayTheta_eq_sub_zero_modes D χ hη t htpos,
    normalizedRayDualTheta_eq_sub_zero_modes D χ hη t htpos,
    normalizedRayConjugateTheta_eq_sub_zero_modes D χ hη t htpos]
  refine ⟨(hb1 t ht).trans (H A1 B1 hA1 ?_ (min_le_left _ _)),
    (hb2 t ht).trans (H A2 B2 hA2 ?_ ((min_le_right _ _).trans (min_le_left _ _))),
    (hb3 t ht).trans (H A3 B3 hA3 ?_ ((min_le_right _ _).trans (min_le_right _ _)))⟩
  all_goals dsimp [C]; linarith

end DedekindZetaZeroFree.Hecke.Theta

end
