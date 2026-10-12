module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.LargeDualRectangles
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.MiddleDirectKernelBounds
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.MiddleDualBounds
public import DedekindZetaZeroFree.LargeSieve.Exponents.ThreeThresholdOptimization

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

namespace LocalExponentHelpers

open scoped BigOperators

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def shellRestriction (C : Context Q) : Context Q :=
  { C with lam := fun b => if b ∈ Sieve.paperShell F c C.N then C.lam b else 0 }

theorem shellRestriction_support (C : Context Q) :
    Function.support (shellRestriction C).lam ⊆
      (Sieve.paperShell F c C.N : Set (Ideal (𝓞 F))) := by
  intro b hb
  change b ∈ Sieve.paperShell F c C.N
  by_contra h
  exact hb (by simp [shellRestriction, h])

theorem shellRestriction_energy (C : Context Q) :
    Sieve.energy F c C.N (shellRestriction C).lam =
      Sieve.energy F c C.N C.lam := by
  apply Finset.sum_congr rfl
  intro b hb
  simp [shellRestriction, hb]

theorem shellRestriction_validPair (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) :
    (shellRestriction C).ValidPair p ↔ C.ValidPair p := by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption

theorem shellRestriction_pairs (C : Context Q) :
    (shellRestriction C).pairs = C.pairs := by
  ext p
  simp only [Context.pairs, Finset.mem_filter, Finset.mem_product,
    shellRestriction_validPair]
  rfl

theorem shellRestriction_E3 (C : Context Q) (B : ℝ) (unit : Bool) :
    E3 (shellRestriction C) B unit = E3 C B unit := by
  unfold E3 Context.pairSum
  rw [shellRestriction_pairs]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ∈ C.pairs := hp
  have hpc := (Finset.mem_filter.mp hp').1
  have hc1 := (Finset.mem_product.mp hpc).1
  have hc2 := (Finset.mem_product.mp hpc).2
  have hs1 := (Finset.mem_filter.mp hc1).2.1
  have hs2 := (Finset.mem_filter.mp hc2).2.1
  have hv : C.ValidPair p := (Finset.mem_filter.mp hp).2
  have hv' := (shellRestriction_validPair C p).mpr hv
  rw [dif_pos hv', dif_pos hv]
  simp only [shellRestriction, Context.coefficient, hs1, hs2, if_pos]
  rfl

theorem finiteSup_mul_le (S : Finset (ℝ × ℝ)) (f : ℝ × ℝ → ℝ)
    (k R : ℝ) (hk : 0 < k) (hR : 0 ≤ R)
    (h : ∀ P ∈ S, k * f P ≤ R) :
    k * ErrorRectangles.finiteSup S f ≤ R := by
  rw [mul_comm, ← le_div_iff₀ hk]
  apply csSup_le
  · exact ⟨0, Or.inl rfl⟩
  rintro z (hz | ⟨P, hP, rfl⟩)
  · have hz0 : z = 0 := hz
    simpa only [hz0] using div_nonneg hR hk.le
  · exact (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using h P hP)

theorem prefix_U_nonneg (B X : ℝ) : 0 ≤ ErrorRectangles.U Q B X := by
  unfold ErrorRectangles.U
  dsimp only
  by_cases h : BddAbove ({0} ∪ {z : ℝ | ∃ lam : Ideal (𝓞 F) → ℂ,
    (∑ b ∈ Sieve.idealAdmissibleFinset F c (2 * X), ‖lam b‖ ^ 2) ≤ 1 ∧
    z = ∑ a ∈ Sieve.idealAdmissibleFinset F c (2 * B),
      ‖∑ b ∈ Sieve.idealAdmissibleFinset F c (2 * X), lam b * (Q.χ b) a‖ ^ 2})
  · exact le_csSup h (Or.inl rfl)
  · rw [Real.sSup_of_not_bddAbove h]

private theorem max_prefix_bound (B M N n P η A : ℝ)
    (hB : 1 ≤ B) (hBM : B ≤ M) (hN : 1 ≤ N) (hn : 1 ≤ n)
    (hP : 1 ≤ P) (hη : 0 ≤ η) (hA : 0 ≤ A) :
    A * (B * max 1 (N / (n * P))) ^ η ≤ A * (2 * (M*N)) ^ η := by
  have hnP : 1 ≤ n*P := by nlinarith
  have hN0 : 0 ≤ N := by linarith
  have hx : max 1 (N/(n*P)) ≤ 2*N := max_le (by linarith)
    ((div_le_self hN0 hnP).trans (by linarith))
  have hbase : B * max 1 (N/(n*P)) ≤ 2*(M*N) := by
    calc _ ≤ B*(2*N) := mul_le_mul_of_nonneg_left hx (by linarith)
         _ ≤ M*(2*N) := mul_le_mul_of_nonneg_right hBM (by positivity)
         _ = _ := by ring
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase hη) hA

private theorem rectangle_thresholds (C : Context Q) (B α η A : ℝ)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d)
    (hnN : norm C.d ≤ 2*C.N) (hB : 1 ≤ B) (hBM : B ≤ C.M)
    (hα : α ∈ Set.Icc (1:ℝ) 2) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hb : ∀ X, 0 < X → ErrorRectangles.U Q B X ≤
      A * (B * max 1 X)^η * (max 1 X + B^α))
    (P : ℝ × ℝ) (hP : P ∈ ErrorRectangles.rectangles C) :
    let L := A * (2*(C.M*C.N))^η
    (∀ a : ℝ, 0 < a → a*C.N/(norm C.d*Real.sqrt (B*C.M)) ≤ P.1*P.2 →
      Real.sqrt (C.M/B) * ErrorRectangles.largeScore C B P ≤
        L*(2*C.M/a + Real.sqrt C.M*B^(α-1/2))) ∧
    (∀ a t : ℝ, 0 < a → 1 ≤ t →
      a*Real.sqrt (C.M/B)/(norm C.d*t) ≤ P.1*P.2 →
      Real.sqrt (C.M/B) * ErrorRectangles.largeScore C B P ≤
        L*(2*C.N*t/a + Real.sqrt C.M*B^(α-1/2))) ∧
    (∀ t : ℝ, 1 ≤ t → P.1*P.2 ≤ t*C.N/Real.sqrt (B*C.M) →
      C.estimatePrefactor * ErrorRectangles.originScore C B P ≤
        L*(2*C.M + norm C.d*t*(Real.sqrt C.M*B^(α-1/2)))) := by
  obtain ⟨h1, h2, hp1, hp2⟩ := ErrorRectangles.rectangle_endpoints C P hP
  have hn0 : 0 < norm C.d := by linarith
  have bound : ∀ T : ℝ, 1 ≤ T →
      ErrorRectangles.U Q B (C.N/(norm C.d*T)) ≤
        (A*(2*(C.M*C.N))^η)*(max 1 ((C.N/norm C.d)/T)+B^α) := by
    intro T hT
    have ht0 : 0 < T := by linarith
    calc _ ≤ A*(B*max 1 (C.N/(norm C.d*T)))^η *
        (max 1 (C.N/(norm C.d*T))+B^α) := hb _ (by positivity)
      _ ≤ A*(2*(C.M*C.N))^η *
        (max 1 (C.N/(norm C.d*T))+B^α) :=
          mul_le_mul_of_nonneg_right
            (max_prefix_bound B C.M C.N (norm C.d) T η A hB hBM hN hn hT hη hA)
            (by positivity)
      _ = _ := by rw [div_div]
  have hh := Sieve.bilinear_rectangle_three_thresholds C.M C.N (norm C.d) B α
    P.1 P.2 (ErrorRectangles.U Q B (C.N/(norm C.d*P.1)))
    (ErrorRectangles.U Q B (C.N/(norm C.d*P.2))) (A*(2*(C.M*C.N))^η)
    hM hN hn hB hnN hα ⟨h1, by simpa [mul_div_assoc] using hp1⟩
    ⟨h2, by simpa [mul_div_assoc] using hp2⟩
    (prefix_U_nonneg _ _) (prefix_U_nonneg _ _) (by positivity)
    (bound _ h1) (bound _ h2)
  have hs : ErrorRectangles.largeScore C B P =
      Real.sqrt (ErrorRectangles.U Q B (C.N/(norm C.d*P.1)) *
      ErrorRectangles.U Q B (C.N/(norm C.d*P.2))/(P.1*P.2)) := by
    rw [ErrorRectangles.largeScore, Real.sqrt_div (mul_nonneg
      (prefix_U_nonneg _ _) (prefix_U_nonneg _ _))]
  have ho : ErrorRectangles.originScore C B P =
      Real.sqrt ((P.1*P.2)*ErrorRectangles.U Q B (C.N/(norm C.d*P.1))*
        ErrorRectangles.U Q B (C.N/(norm C.d*P.2))) := by
    rw [ErrorRectangles.originScore, ← Real.sqrt_mul (by nlinarith : 0 ≤ P.1*P.2)]
    congr 1; ring
  simpa only [hs, ho, Context.estimatePrefactor] using ⟨hh.1, hh.2.1, hh.2.2.1⟩

section
open MiddleFinite
private lemma middle_rectangle_bound (A η α B M N n θ Cq : ℝ)
    (hA : 0 < A) (hη : 0 ≤ η) (hB : 1 ≤ B) (hBM : B ≤ M)
    (hN : 1 ≤ N) (hn : 1 ≤ n)
    (hU0 : ∀ X, 0 < X → 0 ≤ U Q B X)
    (hU : ∀ X, 0 < X → U Q B X ≤ A * (B * max 1 X) ^ η * (max 1 X + B ^ α))
    (ij : ℕ × ℕ) (hij : ij ∈ rectangles F B M N n θ Cq) :
    rectangleValue Q B N n ij ≤
      2 * A * (2 * (M*N)) ^ η *
        (N / n + B ^ α * (Cq*N*θ / Real.sqrt (B*M))) := by
  have hB0 : 0 < B := by linarith
  have hM : 1 ≤ M := hB.trans hBM
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hn0 : 0 < n := by linarith
  obtain ⟨_, h1, h2, hp, _⟩ := (Finset.mem_filter.mp hij)
  let P := divisorScale ij.1
  let S := divisorScale ij.2
  have hP : 1 ≤ P := by dsimp [P, S, divisorScale]; exact one_le_pow₀ (by norm_num)
  have hS : 1 ≤ S := by dsimp [P, S, divisorScale]; exact one_le_pow₀ (by norm_num)
  have hP0 : 0 < P := by linarith
  have hS0 : 0 < S := by linarith
  have bound : ∀ T : ℝ, 1 ≤ T → T ≤ 2*N/n →
      U Q B (N/(n*T)) ≤ A * (2*(M*N))^η * (2*N/(n*T) + B^α) := by
    intro T hT hTn
    have hT0 : 0 < T := by linarith
    have hX : 0 < N/(n*T) := by positivity
    have ht : 1 ≤ 2*N/(n*T) := by
      rw [le_div_iff₀ (by positivity)]
      have := (le_div_iff₀ hn0).mp hTn
      nlinarith
    have hx : max 1 (N/(n*T)) ≤ 2*N/(n*T) := max_le ht (by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith)
    have hnT : 1 ≤ n*T := by nlinarith
    have hbx : B * max 1 (N/(n*T)) ≤ 2*(M*N) := by
      have hxx : 2*N/(n*T) ≤ 2*N := div_le_self (by positivity) hnT
      calc B * max 1 (N/(n*T)) ≤ B * (2*N) := mul_le_mul_of_nonneg_left (hx.trans hxx) hB0.le
           _ ≤ M * (2*N) := mul_le_mul_of_nonneg_right hBM (by positivity)
           _ = _ := by ring
    calc U Q B (N/(n*T)) ≤ A*(B*max 1 (N/(n*T)))^η*(max 1 (N/(n*T))+B^α) := hU _ hX
      _ ≤ A*(2*(M*N))^η*(2*N/(n*T)+B^α) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbx hη) hA.le
        · linarith
        · positivity
        · positivity
  have hu := bound P hP h1
  have hv := bound S hS h2
  have hu0 := hU0 _ (by positivity : 0 < N/(n*P))
  have hv0 := hU0 _ (by positivity : 0 < N/(n*S))
  have hps : 0 ≤ P*S := by positivity
  have hsum : P+S ≤ 2*(P*S) := by nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hS)]
  have hps1 : 1 ≤ P*S := by nlinarith
  have ht : 0 ≤ Cq*N*θ / Real.sqrt (B*M) := le_trans (by positivity : 0 ≤ P*S) hp
  have hprod : P*S*U Q B (N/(n*P))*U Q B (N/(n*S)) ≤
      (2*A*(2*(M*N))^η*(N/n+B^α*(P*S)))^2 := by
    calc P*S*U Q B (N/(n*P))*U Q B (N/(n*S))
        ≤ P*S*(A*(2*(M*N))^η*(2*N/(n*P)+B^α)) * (A*(2*(M*N))^η*(2*N/(n*S)+B^α)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hu hps) hv hv0 (by positivity)
      _ ≤ _ := by
        have hq : 0 ≤ N/n := by positivity
        have hb : 0 ≤ B^α := Real.rpow_nonneg hB0.le _
        have halg : P*S*(2*N/(n*P)+B^α)*(2*N/(n*S)+B^α) =
            4*(N/n)^2 + 2*(N/n)*B^α*(P+S) + (B^α)^2*(P*S) := by
          field_simp; ring
        have hs := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2*(N/n)*B^α)
        have hpp : P*S ≤ (P*S)^2 := by nlinarith
        have hh := mul_le_mul_of_nonneg_left hpp (sq_nonneg (B^α))
        have hvv : P*S*(2*N/(n*P)+B^α)*(2*N/(n*S)+B^α) ≤ (2*(N/n+B^α*(P*S)))^2 := by rw [halg]; nlinarith [sq_nonneg (B^α*(P*S)), mul_nonneg hq (mul_nonneg hb hps)]
        have hc := mul_le_mul_of_nonneg_left hvv (sq_nonneg (A*(2*(M*N))^η))
        nlinarith only [hc]
  unfold rectangleValue
  change Real.sqrt (P*S*U Q B (N/(n*P))*U Q B (N/(n*S))) ≤ _
  calc _ ≤ 2*A*(2*(M*N))^η*(N/n+B^α*(P*S)) := (Real.sqrt_le_left (by positivity)).mpr hprod
       _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hB0.le α)) _) (by positivity)
private lemma middle_R_bound (A η α B M N n θ Cq : ℝ)
    (hA : 0 < A) (hη : 0 ≤ η) (hB : 1 ≤ B) (hBM : B ≤ M)
    (hN : 1 ≤ N) (hn : 1 ≤ n) (hθ : 1 ≤ θ) (hCq : 1 ≤ Cq)
    (hU0 : ∀ X, 0 < X → 0 ≤ U Q B X)
    (hU : ∀ X, 0 < X → U Q B X ≤ A * (B * max 1 X) ^ η * (max 1 X + B ^ α)) :
    (n*M/N) * MiddleFinite.R Q B M N n θ Cq ≤
      (2*A*2^η*Cq) * (M*N)^η * n * θ *
        (M + Real.sqrt M * B^(α-1/2)) := by
  have hM : 1 ≤ M := hB.trans hBM
  have hB0 : 0 < B := by linarith
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hn0 : 0 < n := by linarith
  have hR : MiddleFinite.R Q B M N n θ Cq ≤
      2*A*(2*(M*N))^η*(N/n+B^α*(Cq*N*θ/Real.sqrt (B*M))) := by
    apply csSup_le
    · exact ⟨0, Or.inl (Set.mem_singleton 0)⟩
    · intro z hz
      rcases hz with hz | ⟨ij, hij, rfl⟩
      · simp only [Set.mem_singleton_iff] at hz
        subst z; positivity
      · exact middle_rectangle_bound A η α B M N n θ Cq hA hη hB hBM hN hn hU0 hU ij hij
  have hid : (n*M/N)*(N/n+B^α*(Cq*N*θ/Real.sqrt (B*M))) =
      M + Cq*n*θ*Real.sqrt M*B^(α-1/2) := by
    rw [Real.sqrt_mul hB0.le, Real.rpow_sub hB0, ← Real.sqrt_eq_rpow]
    have hsM : (Real.sqrt M)^2 = M := Real.sq_sqrt hM0.le
    have hsM0 : Real.sqrt M ≠ 0 := (Real.sqrt_pos.mpr hM0).ne'
    have hsB0 : Real.sqrt B ≠ 0 := (Real.sqrt_pos.mpr hB0).ne'
    field_simp
    linear_combination -(n * B ^ α * Cq * θ) * hsM
  have hnt : 1 ≤ n*θ := by nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hθ)]
  have hh : 1 ≤ Cq*n*θ := by nlinarith [mul_nonneg (sub_nonneg.mpr hCq) (sub_nonneg.mpr hnt)]
  calc (n*M/N)*MiddleFinite.R Q B M N n θ Cq ≤
      (n*M/N)*(2*A*(2*(M*N))^η*(N/n+B^α*(Cq*N*θ/Real.sqrt (B*M)))) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
    _ = 2*A*2^η*(M*N)^η*(M+Cq*n*θ*Real.sqrt M*B^(α-1/2)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)]
      calc _ = 2*A*2^η*(M*N)^η*((n*M/N)*(N/n+B^α*(Cq*N*θ/Real.sqrt (B*M)))) := by ring
           _ = _ := by rw [hid]
    _ ≤ _ := by
      have hm : M ≤ Cq*n*θ*M := by nlinarith
      have ht := mul_le_mul_of_nonneg_left (add_le_add_right hm (Cq*n*θ*Real.sqrt M*B^(α-1/2))) (by positivity : 0 ≤ 2*A*2^η*(M*N)^η)
      convert ht using 1 <;> ring

end
private theorem loss_bound (X n ζ δ Cj C0 : ℝ) (hX : 1 ≤ X)
    (hn : 0 ≤ n) (hnX : n ≤ 2*X) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hj : Cj ≤ C0) (h0 : 0 ≤ C0) :
    (X*n)^(ζ/4) * X^(Cj*δ) * (2*X)^(ζ/4) * X^δ ≤
      2^(ζ/2) * X^(8*ζ+(C0+2)*δ) := by
  have hx0 : 0 < X := by linarith
  have hp : (X*n)^(ζ/4) ≤ (2*(X*X))^(ζ/4) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
  have he : (2*(X*X))^(ζ/4) * X^(Cj*δ) * (2*X)^(ζ/4) * X^δ =
      2^(ζ/2) * X^(3*ζ/4+(Cj+1)*δ) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
      Real.mul_rpow hx0.le hx0.le, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx0.le]
    calc
      _ = (2^(ζ/4)*2^(ζ/4)) * (((X^(ζ/4)*X^(ζ/4))*X^(Cj*δ))*X^(ζ/4)*X^δ) := by ring
      _ = _ := by
        simp only [← Real.rpow_add hx0, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1 <;> (congr 1 <;> ring)
  calc _ ≤ (2*(X*X))^(ζ/4) * X^(Cj*δ) * (2*X)^(ζ/4) * X^δ := by gcongr
       _ = _ := he
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_left _ (by positivity)
         apply Real.rpow_le_rpow_of_exponent_le hX
         nlinarith

private theorem shape_bound (M N n θ H a u : ℝ)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hn : 1 ≤ n) (ht : 1 ≤ θ)
    (hu : 0 ≤ u) (ha : 0 < a) (hH : 2/a+2 ≤ H) :
    2*M/a+u ≤ H*n*θ*(M+N+u) ∧
    2*N*θ/a+u ≤ H*n*θ*(M+N+u) := by
  have hnt : 1 ≤ n*θ := by nlinarith
  have h0 : 0 ≤ 2/a := by positivity
  have hh0 : 0 ≤ H := by linarith
  have hh1 : 1 ≤ H := by linarith
  have hHnt : H ≤ H*n*θ := by nlinarith
  have hHn : H ≤ H*n := by nlinarith
  have hMu : 2*M/a ≤ H*M := by rw [mul_div_right_comm]; nlinarith
  have hNu : 2*N*θ/a ≤ H*n*θ*N := by
    have : 2/a ≤ H*n := by linarith
    calc _ = (2/a)*(θ*N) := by ring
         _ ≤ (H*n)*(θ*N) := mul_le_mul_of_nonneg_right this (by positivity)
         _ = _ := by ring
  have hSu : u ≤ H*n*θ*u := by nlinarith
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hHnt) hM, mul_nonneg (by positivity : 0 ≤ H*n*θ) hN]
  · nlinarith [mul_nonneg (by positivity : 0 ≤ H*n*θ) hM]

private theorem upper_shape (M N n θ H t u : ℝ)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hn : 1 ≤ n) (ht : 1 ≤ θ)
    (hu : 0 ≤ u) (hH : 2 ≤ H) (htt : t ≤ H) :
    2*M+n*t*θ*u ≤ H*n*θ*(M+N+u) := by
  have hnt : 1 ≤ n*θ := by nlinarith
  have hHM : 2*M ≤ H*n*θ*M := by
    have : 2 ≤ H*n*θ := by nlinarith
    nlinarith
  have hHu : n*t*θ*u ≤ H*n*θ*u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htt) (by positivity : 0 ≤ n*θ*u)]
  nlinarith [mul_nonneg (by positivity : 0 ≤ H*n*θ) hN]

private theorem envelope_bounds (C : Context Q) (B α η A H : ℝ)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d)
    (hnN : norm C.d ≤ 2*C.N) (hB : 1 ≤ B) (hBM : B ≤ C.M)
    (hδ : 0 < C.δ) (hα : α ∈ Set.Icc (1:ℝ) 2) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hH4 : 4/ErrorRectangles.lowerConstant c + 2 ≤ H)
    (hHu : ErrorRectangles.upperConstant c ≤ H) (hH2 : 2 ≤ H)
    (hb : ∀ X, 0 < X → ErrorRectangles.U Q B X ≤
      A * (B * max 1 X)^η * (max 1 X + B^α)) :
    let R := A*(2*(C.M*C.N))^η*H*norm C.d*(C.M*C.N)^C.δ*
      (C.M+C.N+Real.sqrt C.M*B^(α-1/2))
    Real.sqrt (C.M/B)*ErrorRectangles.dualEnvelope C B ≤ R ∧
    C.estimatePrefactor*ErrorRectangles.originEnvelope C B ≤ R ∧
    Real.sqrt (C.M/B)*ErrorRectangles.directEnvelope C B ≤ R ∧
    Real.sqrt (C.M/B)*ErrorRectangles.middleEnvelope C B ≤ R := by
  let θ := (C.M*C.N)^C.δ
  let L := A*(2*(C.M*C.N))^η
  let S := C.M+C.N+Real.sqrt C.M*B^(α-1/2)
  have hM0 : 0 < C.M := by linarith
  have hN0 : 0 < C.N := by linarith
  have hn0 : 0 < norm C.d := by linarith
  have hB0 : 0 < B := by linarith
  have hMN : 1 ≤ C.M*C.N := by nlinarith
  have ht : 1 ≤ θ := Real.one_le_rpow hMN hδ.le
  have ht0 : 0 < θ := by linarith
  have ha : 0 < ErrorRectangles.lowerConstant c := by
    unfold ErrorRectangles.lowerConstant; positivity
  have hH : 2/ErrorRectangles.lowerConstant c + 2 ≤ H := by
    have hh : 0 ≤ 2 / ErrorRectangles.lowerConstant c := by positivity
    have hid : 4 / ErrorRectangles.lowerConstant c =
        2 * (2 / ErrorRectangles.lowerConstant c) := by ring
    rw [hid] at hH4
    linarith
  have ha5 : 0 < ErrorRectangles.lowerConstant c / 2 := by positivity
  have hH5 : 2 / (ErrorRectangles.lowerConstant c / 2) + 2 ≤ H := by
    convert hH4 using 1 <;> field_simp <;> ring
  have hsh5 := shape_bound C.M C.N (norm C.d) θ H (ErrorRectangles.lowerConstant c / 2)
    (Real.sqrt C.M*B^(α-1/2)) hM0.le hN0.le hn ht (by positivity) ha5 hH5
  have hR0 : 0 ≤ L*H*norm C.d*θ*S := by dsimp [L,S]; positivity
  have hsh := shape_bound C.M C.N (norm C.d) θ H (ErrorRectangles.lowerConstant c)
    (Real.sqrt C.M*B^(α-1/2)) hM0.le hN0.le hn ht (by positivity) ha hH
  have hS := fun P hP => rectangle_thresholds C B α η A hM hN hn hnN hB hBM hα hη hA hb P hP
  have scale : ∀ r, r ≤ H*norm C.d*θ*S → L*r ≤ L*H*norm C.d*θ*S := by
    intro r hr
    convert mul_le_mul_of_nonneg_left hr (show 0 ≤ L by dsimp [L]; positivity) using 1 <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply finiteSup_mul_le _ _ _ _ (by positivity) hR0
    intro P hP
    obtain ⟨hp, hthr⟩ := Finset.mem_filter.mp hP
    apply le_trans ((hS P hp).1 _ ha ?_) (scale _ hsh.1)
    exact le_trans (le_mul_of_one_le_right (by positivity) ht) hthr
  · apply finiteSup_mul_le _ _ _ _ (by dsimp [Context.estimatePrefactor]; positivity) hR0
    intro P hP
    obtain ⟨hp, hthr⟩ := Finset.mem_filter.mp hP
    have hu1 : 1 ≤ ErrorRectangles.upperConstant c := by
      unfold ErrorRectangles.upperConstant; have := le_max_left (1:ℝ) (norm c); linarith
    have hut : 1 ≤ ErrorRectangles.upperConstant c*θ := by nlinarith
    apply le_trans ((hS P hp).2.2 (ErrorRectangles.upperConstant c*θ) hut ?_) ?_
    · convert hthr using 1 <;> dsimp [θ] <;> ring
    · apply scale
      simpa only [S, mul_assoc, mul_left_comm, mul_comm] using
        upper_shape C.M C.N (norm C.d) θ H (ErrorRectangles.upperConstant c)
          (Real.sqrt C.M*B^(α-1/2)) hM0.le hN0.le hn ht (by positivity) hH2 hHu
  · apply finiteSup_mul_le _ _ _ _ (by positivity) hR0
    intro P hP
    obtain ⟨hp, hthr⟩ := Finset.mem_filter.mp hP
    apply le_trans ((hS P hp).2.1 _ 1 ha le_rfl ?_) (scale _ ?_)
    · simp only [mul_one]
      have hh := le_mul_of_one_le_right (show 0 ≤ ErrorRectangles.lowerConstant c * Real.sqrt (C.M/B)/norm C.d by positivity) ht
      exact le_trans hh (by convert hthr using 1; dsimp [θ]; ring)
    · simpa only [mul_one] using (shape_bound C.M C.N (norm C.d) θ H
        (ErrorRectangles.lowerConstant c) (Real.sqrt C.M*B^(α-1/2))
        hM0.le hN0.le hn ht (by positivity) ha hH).2.trans' (by
          have := ht
          have hh : 2*C.N/ErrorRectangles.lowerConstant c ≤
              2*C.N*θ/ErrorRectangles.lowerConstant c := by
                calc
                  _ ≤ (2*C.N/ErrorRectangles.lowerConstant c)*θ :=
                    le_mul_of_one_le_right (by positivity) ht
                  _ = _ := by ring
          linarith)
  · apply finiteSup_mul_le _ _ _ _ (by positivity) hR0
    intro P hP
    obtain ⟨hp, hthr⟩ := Finset.mem_filter.mp hP
    apply le_trans ((hS P hp).2.1 _ θ ha5 ht ?_) (scale _ hsh5.2)
    change (ErrorRectangles.lowerConstant c / 2)*Real.sqrt (C.M/B)*(C.M*C.N)^(-C.δ)/norm C.d ≤ P.1*P.2 at hthr
    rw [Real.rpow_neg (by positivity : 0 ≤ C.M*C.N)] at hthr
    convert hthr using 1 <;> dsimp [θ] <;> ring

private theorem combine_bound (X n ζ δ Cj C0 Ai A0 H S E e : ℝ)
    (hX : 1 ≤ X) (hn : 1 ≤ n) (hnX : n ≤ 2*X) (hζ : 0 < ζ)
    (hδ : 0 < δ) (hj : Cj ≤ C0) (hC0 : 0 ≤ C0)
    (hAi : 0 ≤ Ai) (hA0 : 0 ≤ A0) (hH : 0 ≤ H)
    (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hb : e ≤ Ai*(X*n)^(ζ/4)*X^(Cj*δ)*
      (A0*(2*X)^(ζ/4)*H*n*X^δ*S)*E) :
    e ≤ Ai*A0*H*2^(ζ/2)*n*X^(8*ζ+(C0+2)*δ)*S*E := by
  have hp := loss_bound X n ζ δ Cj C0 hX (by linarith) hnX hζ hδ hj hC0
  have hs : 0 ≤ Ai*A0*H*n*S*E := by positivity
  calc
    e ≤ _ := hb
    _ = (Ai*A0*H*n*S*E) *
        ((X*n)^(ζ/4)*X^(Cj*δ)*(2*X)^(ζ/4)*X^δ) := by ring
    _ ≤ (Ai*A0*H*n*S*E) *
        (2^(ζ/2)*X^(8*ζ+(C0+2)*δ)) := mul_le_mul_of_nonneg_left hp hs
    _ = _ := by ring

end LocalExponentHelpers

theorem bilinear_error_local_exponent_bound
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c)
    (hF : NumberField.IsTotallyComplex F)
    (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ (α : ℝ), α ∈ Set.Icc (1 : ℝ) 2 →
      Sieve.HasSieveExponent F c Q α →
      ∀ (ζ δ : ℝ), 0 < ζ → 0 < δ →
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (M N K : ℝ), 1 ≤ M → 1 ≤ N → 1 ≤ K → K ≤ M →
        ∀ (d : Ideal (𝓞 F)) (hd0 : d ≠ ⊥) (hd : Squarefree d)
          (hdc : d ⊔ c = ⊤),
        1 ≤ (Ideal.absNorm d : ℝ) → (Ideal.absNorm d : ℝ) ≤ 2 * N →
        ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ) (B : ℝ) (unit : Bool),
        1 ≤ B → B ≤ K → (unit = true → B = 1) →
        let C : Context Q := {
          D := D, core := core, hF := hF,
          M := M, N := N, K := K, δ := δ, W := W, hW := hW,
          d := d, hd0 := hd0, hd := hd, hdc := hdc, g := g, lam := lam }
        ‖E1 C B unit‖ + ‖E2 C B unit‖ + ‖E3 C B unit‖ +
            ‖E4 C B unit‖ + ‖E5 C B unit‖ ≤
          A * (Ideal.absNorm d : ℝ) * Real.rpow (M * N) (8 * ζ + (C0 + 2) * δ) *
            (M + N + Real.sqrt M * Real.rpow B (α - 1 / 2)) *
            Sieve.energy F c N lam := by
  obtain ⟨C5, hC5, h5⟩ := bilinear_error_middle_direct D core hF W hW
  obtain ⟨Cq, hCq, C3, hC3, h3⟩ :=
    bilinear_error_middle_dual F c Q D core hF W hW
  let C0 := max C3 C5
  refine ⟨C0, le_trans hC3 (le_max_left _ _), ?_⟩
  intro α hα hE ζ δ hζ hδ
  have hη : 0 < ζ/4 := by linarith
  obtain ⟨A1, hA1, he1⟩ := bilinear_error_large_dual D W δ hδ (ζ/4) hη
  obtain ⟨A2, hA2, he2⟩ := bilinear_error_origin D W δ hδ (ζ/4) hη
  obtain ⟨A4, hA4, he4⟩ := bilinear_error_large_direct D W δ hδ (ζ/4) hη
  obtain ⟨A5, hA5, he5⟩ := h5 (ζ/4) hη
  obtain ⟨A3, hA3, he3⟩ := h3 (ζ/4) hη
  have hrec := (DedekindZetaZeroFree.LargeSieve.algebra_normalized_reciprocity F c Q D.bad
    D.bad_ne_bot D.original_dvd_bad (fun a ha hac =>
      ⟨D.index_dvd_conductor a ha hac, D.conductor_dvd_index_bad a ha hac⟩)).2.1
  rw [core] at hrec
  obtain ⟨Ap, hAp, hp⟩ := ErrorRectangles.U_le_of_exponent Q D.original_ne_bot
    hrec α hα hE (ζ/4) hη
  obtain ⟨As, hAs, hs⟩ := ErrorRectangles.U_le_of_exponent Q D.original_ne_bot
    hrec α hα hE (ζ/4) hη
  let A0 := max Ap As
  let H := 4/ErrorRectangles.lowerConstant c + 2 + ErrorRectangles.upperConstant c + 2*Cq
  have ha : 0 < ErrorRectangles.lowerConstant c := by
    unfold ErrorRectangles.lowerConstant; positivity
  have hu : 0 ≤ ErrorRectangles.upperConstant c := by
    unfold ErrorRectangles.upperConstant; positivity
  have hH : 4/ErrorRectangles.lowerConstant c + 2 ≤ H := by
    dsimp [H]
    have hh : 0 ≤ 4 / ErrorRectangles.lowerConstant c := by positivity
    linarith
  have hHu : ErrorRectangles.upperConstant c ≤ H := by
    dsimp [H]
    have hh : 0 ≤ 4 / ErrorRectangles.lowerConstant c := by positivity
    linarith
  have hHC : 2*Cq ≤ H := by
    dsimp [H]
    have hh : 0 ≤ 4 / ErrorRectangles.lowerConstant c := by positivity
    linarith
  have hH2 : 2 ≤ H := by
    dsimp [H]
    have hh : 0 ≤ 4 / ErrorRectangles.lowerConstant c := by positivity
    linarith
  have hH0 : 0 ≤ H := by linarith
  have hA0 : 0 ≤ A0 := le_trans (by linarith : 0 ≤ Ap) (le_max_left _ _)
  let T := A0*H*2^(ζ/2)
  refine ⟨(A1+A2+A3+A4+A5)*T, by dsimp [T]; positivity, ?_⟩
  intro M N K hM hN hK hKM d hd0 hd hdc hn hnN g lam B unit hB hBK huB
  let C : Context Q := {
    D := D, core := core, hF := hF,
    M := M, N := N, K := K, δ := δ, W := W, hW := hW,
    d := d, hd0 := hd0, hd := hd, hdc := hdc, g := g, lam := lam }
  let X := M*N
  let n := norm d
  let S := M+N+Real.sqrt M*B^(α-1/2)
  let E := Sieve.energy F c N lam
  have hx : 1 ≤ X := by dsimp [X]; nlinarith
  have hx0 : 0 < X := by linarith
  have hn' : 1 ≤ n := hn
  have hnX : n ≤ 2*X := by dsimp [X,n]; change (Ideal.absNorm d : ℝ) ≤ _; nlinarith
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hEn : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hBM : B ≤ M := hBK.trans hKM
  have hub : ∀ Z, 0 < Z → ErrorRectangles.U Q B Z ≤
      A0*(B*max 1 Z)^(ζ/4)*(max 1 Z+B^α) := by
    intro Z hZ
    calc _ ≤ Ap*(B*max 1 Z)^(ζ/4)*
          min (B+(max 1 Z)^α) (max 1 Z+B^α) := hp B Z hB hZ
         _ ≤ _ := by gcongr; exact le_max_left _ _; exact min_le_right _ _
  obtain ⟨eb1, eb2, eb4, eb5⟩ := LocalExponentHelpers.envelope_bounds C B α (ζ/4)
    A0 H hM hN hn hnN hB hBM hδ hα hη.le hA0 hH hHu hH2 hub
  change ‖E1 C B unit‖+‖E2 C B unit‖+‖E3 C B unit‖+
    ‖E4 C B unit‖+‖E5 C B unit‖ ≤ _
  have comb := LocalExponentHelpers.combine_bound X n ζ δ
  have hC0 : 0 ≤ C0 := le_trans hC3 (le_max_left _ _)
  have zC : 0 ≤ C0 := hC0
  have b1 : ‖E1 C B unit‖ ≤ A1*T*n*X^(8*ζ+(C0+2)*δ)*S*E := by
    simp only [T, ← mul_assoc]
    apply comb 0 C0 A1 A0 H S E _ hx hn' hnX hζ hδ zC hC0
      hA1.le hA0 hH0 hS hEn
    have hh := he1 C rfl rfl rfl B unit huB hM hN hB hBK hKM hn hnN
    calc _ ≤ A1*(X*n)^(ζ/4)* (Real.sqrt (M/B)*ErrorRectangles.dualEnvelope C B)*E := by
           simpa only [Real.rpow_eq_pow,C,X,n,E,mul_assoc] using hh
         _ ≤ _ := by simpa only [zero_mul,Real.rpow_eq_pow,Real.rpow_zero,mul_one,C,X,n,S,E] using
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left eb1
             (show 0 ≤ A1*(X*n)^(ζ/4) by positivity)) hEn
  have b2 : ‖E2 C B unit‖ ≤ A2*T*n*X^(8*ζ+(C0+2)*δ)*S*E := by
    simp only [T, ← mul_assoc]
    apply comb 0 C0 A2 A0 H S E _ hx hn' hnX hζ hδ zC hC0
      hA2.le hA0 hH0 hS hEn
    have hh := he2 C rfl rfl rfl B unit huB hM hN hB hBK hKM hn hnN
    calc _ ≤ A2*(X*n)^(ζ/4)* (C.estimatePrefactor*ErrorRectangles.originEnvelope C B)*E := by
           simpa only [Real.rpow_eq_pow,C,X,n,E,mul_assoc] using hh
         _ ≤ _ := by simpa only [zero_mul,Real.rpow_eq_pow,Real.rpow_zero,mul_one,C,X,n,S,E] using
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left eb2
             (show 0 ≤ A2*(X*n)^(ζ/4) by positivity)) hEn
  have b4 : ‖E4 C B unit‖ ≤ A4*T*n*X^(8*ζ+(C0+2)*δ)*S*E := by
    simp only [T, ← mul_assoc]
    apply comb 0 C0 A4 A0 H S E _ hx hn' hnX hζ hδ zC hC0
      hA4.le hA0 hH0 hS hEn
    have hh := he4 C rfl rfl rfl B unit huB hM hN hB hBK hKM hn hnN
    calc _ ≤ A4*(X*n)^(ζ/4)* (Real.sqrt (M/B)*ErrorRectangles.directEnvelope C B)*E := by
           simpa only [Real.rpow_eq_pow,C,X,n,E,mul_assoc] using hh
         _ ≤ _ := by simpa only [zero_mul,Real.rpow_eq_pow,Real.rpow_zero,mul_one,C,X,n,S,E] using
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left eb4
             (show 0 ≤ A4*(X*n)^(ζ/4) by positivity)) hEn
  have b5 : ‖E5 C B unit‖ ≤ A5*T*n*X^(8*ζ+(C0+2)*δ)*S*E := by
    simp only [T, ← mul_assoc]
    apply comb C5 C0 A5 A0 H S E _ hx hn' hnX hζ hδ (le_max_right _ _) hC0
      hA5.le hA0 hH0 hS hEn
    have hh := he5 δ hδ C rfl rfl rfl B unit huB hM hN hB hBK hKM hn hnN
    calc _ ≤ A5*(X*n)^(ζ/4)*X^(C5*δ)*
          (Real.sqrt (M/B)*ErrorRectangles.middleEnvelope C B)*E := by
           simpa only [Real.rpow_eq_pow,C,X,n,E,mul_assoc] using hh
         _ ≤ _ := by simpa only [C,X,n,S,E] using
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left eb5
             (show 0 ≤ A5*(X*n)^(ζ/4)*X^(C5*δ) by positivity)) hEn
  have b3 : ‖E3 C B unit‖ ≤ A3*T*n*X^(8*ζ+(C0+2)*δ)*S*E := by
    simp only [T, ← mul_assoc]
    apply comb C3 C0 A3 A0 H S E _ hx hn' hnX hζ hδ (le_max_left _ _) hC0
      hA3.le hA0 hH0 hS hEn
    have hUs : ∀ Z, 0 < Z → MiddleFinite.U Q B Z ≤
        As*(B*max 1 Z)^(ζ/4)*(max 1 Z+B^α) := by
      intro Z hZ
      apply le_trans (hs B Z hB hZ)
      apply mul_le_mul_of_nonneg_left (min_le_right _ _)
      exact mul_nonneg (le_trans zero_le_one hAs)
        (Real.rpow_nonneg (mul_nonneg (by linarith)
          (le_trans zero_le_one (le_max_left _ _))) _)
    have hr := LocalExponentHelpers.middle_R_bound As (ζ/4) α B M N n
      (X^δ) Cq (by linarith) hη.le hB hBM hN hn'
      (Real.one_le_rpow hx hδ.le) hCq
      (fun Z _ => Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩) hUs
    have hr' : (n*M/N)*MiddleFinite.R Q B M N n (X^δ) Cq ≤
        A0*(2*X)^(ζ/4)*H*n*X^δ*S := by
      calc _ ≤ (2*As*2^(ζ/4)*Cq)*X^(ζ/4)*n*X^δ*
          (M+Real.sqrt M*B^(α-1/2)) := hr
           _ = As*(2*X)^(ζ/4)*(2*Cq)*n*X^δ*
             (M+Real.sqrt M*B^(α-1/2)) := by
               rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx0.le]; ring
           _ ≤ _ := by
             have hsS : M+Real.sqrt M*B^(α-1/2) ≤ S := by dsimp [S]; linarith
             gcongr
             · exact le_max_right _ _
    let lam' := (LocalExponentHelpers.shellRestriction C).lam
    have hh := (he3 M N K δ hM hN hδ hK hKM d hd0 hd hdc hn hnN g lam'
      (LocalExponentHelpers.shellRestriction_support C) B unit hB hBK huB).1
    have hEeq := LocalExponentHelpers.shellRestriction_E3 C B unit
    have heeq := LocalExponentHelpers.shellRestriction_energy C
    have hh' : ‖E3 C B unit‖ ≤ A3*(X*n)^(ζ/4)*X^(C3*δ)*
        ((n*M/N)*MiddleFinite.R Q B M N n (X^δ) Cq)*E := by
      rw [← hEeq]
      change ‖E3 (LocalExponentHelpers.shellRestriction C) B unit‖ ≤
        A3*(X*n)^(ζ/4)*X^(C3*δ)*
        ((n*M/N)*MiddleFinite.R Q B M N n (X^δ) Cq)*Sieve.energy F c N C.lam
      rw [← heeq]
      simpa only [Real.rpow_eq_pow,C,X,n,E,lam',LocalExponentHelpers.shellRestriction,mul_assoc] using hh
    exact le_trans hh' (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr' (by positivity)) hEn)
  have hh := add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5
  convert hh using 1 <;> dsimp [T,X,n,S,E,norm] <;> ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end
