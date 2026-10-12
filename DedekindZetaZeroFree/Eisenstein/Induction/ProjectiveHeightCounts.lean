module

public import DedekindZetaZeroFree.Arithmetic.Units.BalancedProjectivePairs
public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalIdealPairBoxCount

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPChamberProjectiveCount

variable (F : Type) [Field F] [NumberField F]

theorem relativeHeight_count :
    ∃ C_F : ℝ, 0 < C_F ∧ ∀ B : ℝ, 1 ≤ B →
      {ℓ : KPChamberHeight.Line F | Projectivization.mulHeight ℓ ≤ B}.Finite ∧
        ({ℓ : KPChamberHeight.Line F | Projectivization.mulHeight ℓ ≤ B}.ncard : ℝ) ≤
          C_F * B ^ 2 := by
  classical
  let J : ClassGroup (NumberField.RingOfIntegers F) →
      ↥(nonZeroDivisors (Ideal (NumberField.RingOfIntegers F))) :=
    fun j => Classical.choose (ClassGroup.mk0_surjective j)
  have hJ : ∀ j, ClassGroup.mk0 (J j) = j :=
    fun j => Classical.choose_spec (ClassGroup.mk0_surjective j)
  obtain ⟨C, hC, hbalanced⟩ :=
    KPChamberUnitBalancedPairs.exists_unit_balanced_pair F J hJ
  let I := fun j => ((J j : Ideal (NumberField.RingOfIntegers F)) :
    FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
  have hI : ∀ j, I j ≠ 0 := by
    intro j
    apply FractionalIdeal.coeIdeal_ne_zero.mpr
    exact nonZeroDivisors.coe_ne_zero (J j)
  choose D hD hbox using fun j => kp_chamber_lattice_box_count F (I j) (hI j)
  let d := Module.finrank ℚ F
  have hd : d ≠ 0 := ne_of_gt (Module.finrank_pos)
  let A : ℝ := C + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let K : ℝ := (∑ j, D j) * A ^ (2 * d)
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (Finset.sum_pos (fun j _ => hD j) Finset.univ_nonempty)
      (pow_pos hApos _)
  refine ⟨K, hK, ?_⟩
  intro B hB
  let R : ℝ := A * B ^ (1 / (d : ℝ))
  have hroot : 1 ≤ B ^ (1 / (d : ℝ)) :=
    Real.one_le_rpow hB (by positivity)
  have hR : 1 ≤ R := by
    dsimp [R]
    nlinarith
  have hpow : R ^ (2 * d) = A ^ (2 * d) * B ^ 2 := by
    dsimp [R]
    rw [mul_pow, Nat.mul_comm 2 d, one_div]
    rw [pow_mul (B ^ (d : ℝ)⁻¹),
      Real.rpow_inv_natCast_pow (by linarith : 0 ≤ B) hd]
  let row : F × F → Fin 2 → F := fun p => ![p.1, p.2]
  let toLine : F × F → KPChamberHeight.Line F := fun p =>
    if h : row p ≠ 0 then Projectivization.mk F (row p) h
    else Projectivization.mk F (fun _ : Fin 2 => (1 : F))
      (by intro he; have he0 := congrFun he 0; simpa using he0)
  let boxes := fun j => KPChamberLattice.idealPairBox F (I j) R
  let lines := fun j => toLine '' boxes j
  have hbfin : ∀ j, (boxes j).Finite := fun j => (hbox j R hR).1
  have hlfin : (⋃ j, lines j).Finite := Set.finite_iUnion fun j => (hbfin j).image toLine
  have hsub : {ℓ : KPChamberHeight.Line F | Projectivization.mulHeight ℓ ≤ B} ⊆
      ⋃ j, lines j := by
    intro ℓ hℓ
    obtain ⟨j, r, hr, heq, hspan, harch⟩ := hbalanced B hB ℓ hℓ
    let p : F × F := ((r 0 : F), (r 1 : F))
    have hrow : row p = fun i => (r i : F) := by
      funext i
      fin_cases i <;> rfl
    have hp : p ∈ boxes j := by
      refine ⟨?_, ?_, ?_⟩
      · apply FractionalIdeal.mem_coeIdeal_of_mem
        rw [← hspan]
        exact Ideal.mem_span_range_self
      · apply FractionalIdeal.mem_coeIdeal_of_mem
        rw [← hspan]
        exact Ideal.mem_span_range_self
      · intro σ
        have hm : C * B ^ (1 / (Module.finrank ℚ F : ℝ)) ≤ R := by
          dsimp [R, A, d]
          nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ B)
            (1 / (Module.finrank ℚ F : ℝ))]
        exact ⟨(le_max_left _ _).trans ((harch σ).trans hm),
          (le_max_right _ _).trans ((harch σ).trans hm)⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, p, hp, ?_⟩
    have hpnonzero : row p ≠ 0 := by rw [hrow]; exact hr
    simpa only [toLine, dif_pos hpnonzero, hrow] using heq
  refine ⟨hlfin.subset hsub, ?_⟩
  calc
    ({ℓ : KPChamberHeight.Line F | Projectivization.mulHeight ℓ ≤ B}.ncard : ℝ) ≤
        ((⋃ j, lines j).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hlfin
    _ ≤ ∑ j, ((lines j).ncard : ℝ) := by
      exact_mod_cast Set.ncard_iUnion_le_of_fintype lines
    _ ≤ ∑ j, D j * R ^ (2 * d) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        ((lines j).ncard : ℝ) ≤ ((boxes j).ncard : ℝ) := by
          exact_mod_cast Set.ncard_image_le (hbfin j)
        _ ≤ D j * R ^ (2 * d) := (hbox j R hR).2
    _ = K * B ^ 2 := by rw [← Finset.sum_mul, hpow]; dsimp [K]; ring

end DedekindZetaZeroFree.KPChamberProjectiveCount

end
