module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorConvolution

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Detector
open scoped Classical

def cutoffMoebius (F : Type) [Field F] [NumberField F] (V : ℝ) (n : Ideal (𝓞 F)) : ℝ :=
  ∑ᶠ d : Ideal (𝓞 F),
    if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ V then (idealMoebius F d : ℝ) else 0

def cutoffInverse (F : Type) [Field F] [NumberField F] {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (V : ℝ) (s : ℂ) : ℂ :=
  ∑ᶠ d : Ideal (𝓞 F),
    if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ V then
      (idealMoebius F d : ℂ) * ω d * (Ideal.absNorm d : ℂ) ^ (-s) else 0

theorem a_eq_cutoffMoebius (F : Type) [Field F] [NumberField F] (U : ℝ) (n : Ideal (𝓞 F)) :
    DetectorDef.a F U n = cutoffMoebius F (U ^ DetectorDef.qExp) n := rfl

theorem D_eq_cutoffInverse (F : Type) [Field F] [NumberField F] (U : ℝ) {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (s : ℂ) :
    DetectorDef.D F U ω s = cutoffInverse F ω (U ^ DetectorDef.qExp) s := rfl

theorem cutoffMoebius_support_finite (F : Type) [Field F] [NumberField F] (V : ℝ)
    (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) :
    (Function.support (fun d : Ideal (𝓞 F) =>
      if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ V then (idealMoebius F d : ℝ) else 0)).Finite :=
  (ideal_divisors_finite F n hn).subset (fun d hd => by
    by_contra h
    exact hd (if_neg (fun hh => h ⟨hh.1, hh.2.1⟩)))

theorem idealLSeries_mul_cutoffInverse (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ω : RayClassCharacter F m)
    (hω : ω.IsPrimitive) (V : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : Ideal (𝓞 F) =>
      if n ≠ ⊥ then (cutoffMoebius F V n : ℂ) *
        ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0) ∧
    HasSum (fun n : Ideal (𝓞 F) =>
      if n ≠ ⊥ then (cutoffMoebius F V n : ℂ) *
        ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0)
      (idealLSeries F ω s * cutoffInverse F ω V s) := by
  classical
  let K := (ideals_bounded_norm_finite F (V)).toFinset
  have hK (d : Ideal (𝓞 F)) : d ∈ K ↔ d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ V :=
    Set.Finite.mem_toFinset _
  let W : Ideal (𝓞 F) → ℂ := fun n => ω n * (Ideal.absNorm n : ℂ) ^ (-s)
  have hzero : W ⊥ = 0 := by
    have hz : ω ⊥ = 0 := (ω.eq_zero_iff' ⊥).mpr (Or.inl rfl)
    simp [W, hz]
  have hmul (a b : Ideal (𝓞 F)) : W (a * b) = W a * W b := by
    dsimp [W]
    rw [ω.map_mul', map_mul Ideal.absNorm, Nat.cast_mul]
    have hp : ((Ideal.absNorm a : ℂ) * (Ideal.absNorm b : ℂ)) ^ (-s) =
        (Ideal.absNorm a : ℂ) ^ (-s) * (Ideal.absNorm b : ℂ) ^ (-s) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm a) : (0 : ℝ) ≤ Ideal.absNorm a)
        (Nat.cast_nonneg (Ideal.absNorm b) : (0 : ℝ) ≤ Ideal.absNorm b) (-s)
    rw [hp]
    ring
  have hW : HasSum W (idealLSeries F ω s) := by
    have heq : (fun n : Ideal (𝓞 F) => if n ≠ ⊥ then W n else 0) = W := by
      funext n
      by_cases hn : n = ⊥ <;> simp [hn, hzero]
    change HasSum W (∑' n, if n ≠ ⊥ then W n else 0)
    rw [heq]
    exact ((idealLSeries_summable F m hm ω hω s hs).congr
      (fun n => congrFun heq n)).hasSum
  let T : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun d n =>
    if n ≠ ⊥ ∧ d ∣ n then (idealMoebius F d : ℂ) * W n else 0
  have hT (d : Ideal (𝓞 F)) (hd : d ∈ K) :
      HasSum (T d) (idealLSeries F ω s * ((idealMoebius F d : ℂ) * W d)) := by
    have hd0 := ((hK d).mp hd).1
    have hinj : Function.Injective (fun n : Ideal (𝓞 F) => n * d) :=
      mul_left_injective₀ hd0
    apply (hinj.hasSum_iff ?_).mp
    · have heq : T d ∘ (fun n : Ideal (𝓞 F) => n * d) =
          fun n => W n * ((idealMoebius F d : ℂ) * W d) := by
        funext n
        dsimp [T, Function.comp_def]
        by_cases hn : n = ⊥
        · simp [hn, hzero]
        · rw [if_pos ⟨mul_ne_zero hn hd0, dvd_mul_left d n⟩, hmul]
          ring
      rw [heq]
      exact hW.mul_right _
    · intro n hn
      have hnd : ¬d ∣ n := by
        rintro ⟨a, ha⟩
        apply hn
        exact ⟨a, by simpa [mul_comm] using ha.symm⟩
      simp [T, hnd]
  have hsum := hasSum_sum hT
  have hcoef (n : Ideal (𝓞 F)) : (∑ d ∈ K, T d n) =
      if n ≠ ⊥ then (cutoffMoebius F V n : ℂ) * W n else 0 := by
    by_cases hn : n ≠ ⊥
    · rw [if_pos hn]
      have ha : cutoffMoebius F V n = ∑ d ∈ K,
          if d ∣ n then (idealMoebius F d : ℝ) else 0 := by
        unfold cutoffMoebius
        rw [finsum_eq_sum_of_support_subset _ (s := K)]
        · apply Finset.sum_congr rfl
          intro d hd
          simp [((hK d).mp hd).1, ((hK d).mp hd).2]
        · intro d hd
          apply (hK d).mpr
          by_contra h
          exact hd (if_neg (fun hh => h ⟨hh.1, hh.2.2⟩))
      rw [ha, Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdn : d ∣ n <;> simp [T, hn, hdn]
    · simp [T, hn]
  have hvalue : (∑ d ∈ K, idealLSeries F ω s * ((idealMoebius F d : ℂ) * W d)) =
      idealLSeries F ω s * cutoffInverse F ω V s := by
    have hi : cutoffInverse F ω V s =
        ∑ d ∈ K, (idealMoebius F d : ℂ) * W d := by
      unfold cutoffInverse
      rw [finsum_eq_sum_of_support_subset _ (s := K)]
      · apply Finset.sum_congr rfl
        intro d hd
        rw [if_pos ((hK d).mp hd)]
        dsimp [W]
        ring
      · intro d hd
        apply (hK d).mpr
        by_contra h
        exact hd (if_neg h)
    rw [hi, Finset.mul_sum]
  rw [hvalue] at hsum
  have heq : (fun n => ∑ d ∈ K, T d n) =
      (fun n => if n ≠ ⊥ then (cutoffMoebius F V n : ℂ) * W n else 0) :=
    funext hcoef
  rw [heq] at hsum
  simpa only [W, mul_assoc] using And.intro hsum.summable hsum

theorem idealLSeries_mul_D (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ω : RayClassCharacter F m)
    (hω : ω.IsPrimitive) (U : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : Ideal (𝓞 F) =>
      if n ≠ ⊥ then (DetectorDef.a F U n : ℂ) *
        ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0) ∧
    HasSum (fun n : Ideal (𝓞 F) =>
      if n ≠ ⊥ then (DetectorDef.a F U n : ℂ) *
        ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0)
      (idealLSeries F ω s * DetectorDef.D F U ω s) :=
  idealLSeries_mul_cutoffInverse F m hm ω hω (U ^ DetectorDef.qExp) s hs

end

end DedekindZetaZeroFree.Quantitative.DetectorConvolution
