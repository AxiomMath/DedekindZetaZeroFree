module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.Codifferent.ReducedPairs
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.SingleModulusGaussBound
public import DedekindZetaZeroFree.ZeroDetection.Conductors.PrimitiveResidueFibers

@[expose] public section

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain

theorem residue_orthogonal_of_primitive {R : Type*} [CommRing R] [Fintype R]
    (psi : AddChar R ℂ) (hp : psi.IsPrimitive) : IsOrthogonalResidueAddChar psi := by
  intro n hn
  simpa only [mul_comm, if_neg hn, Nat.cast_zero] using AddChar.sum_mulShift n hp

theorem additive_residue_row_sieve_of_scaled_trace_adapter
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (K_bal : Set A.G) (hK : IsCompact K_bal)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hAdapter : ∀ (B : Subgroup A.V) (s : A.BalancedIdealSection B K_bal)
      (V : ℝ), 1 ≤ V → ∀ (Q : Type) [Fintype Q] (q : Q → Ideal A.R)
        [∀ j, Fintype (A.R ⧸ q j)],
        Function.Injective q → (∀ j, q j ≠ ⊥) →
        (∀ j, (Nat.card (A.R ⧸ q j) : ℝ) ≤ V) →
        ∃ (p : ProbeSeparation.Presentation F A.Sf)
          (rho : (Σ j, (A.R ⧸ q j)ˣ) → ProbeSeparation.ReducedPair F A.Sf),
          Function.Injective rho ∧
          (∀ jd, ProbeSeparation.denominatorNorm F (rho jd) ≤ C0 * V) ∧
          ∃ psi : ∀ j, AddChar (A.R ⧸ q j) ℂ,
            (∀ j, (psi j).IsPrimitive) ∧
            ∀ j (d : (A.R ⧸ q j)ˣ) (m : A.R),
              psi j (Ideal.Quotient.mk (q j) m * (d : A.R ⧸ q j)) =
                ProbeAdditive.phase F A.Sf e (sLocalDiagonal F A.Sf
                  (-((m : F) * ProbeSeparation.value F p (rho ⟨j, d⟩))))) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (B : Subgroup A.V) (s : A.BalancedIdealSection B K_bal)
        (X V : ℝ), 1 ≤ X → 1 ≤ V →
        ∀ (Q : Type) [Fintype Q] (q : Q → Ideal A.R)
          [∀ j, Fintype (A.R ⧸ q j)],
          Function.Injective q → (∀ j, q j ≠ ⊥) →
          (∀ j, (Nat.card (A.R ⧸ q j) : ℝ) ≤ V) →
          ∃ psi : ∀ j, AddChar (A.R ⧸ q j) ℂ,
            (∀ j, IsOrthogonalResidueAddChar (psi j)) ∧
            let rows := (probe_additive_box_rows_finite F A.Sf X
              (A.balancedDyadicBox K_bal)
              (A.detector_balanced_ideal_section B K_bal hK s).1).toFinset
            ∀ z : ↥rows → ℂ,
              (∑ j, ∑ d : (A.R ⧸ q j)ˣ, ‖∑ m : ↥rows,
                z m * psi j (Ideal.Quotient.mk (q j) m.val *
                  (d : A.R ⧸ q j))‖ ^ 2) ≤
                D * (X + V ^ 2) * ∑ m : ↥rows, ‖z m‖ ^ 2 := by
  by_cases hs : ∃ (B : Subgroup A.V), Nonempty (A.BalancedIdealSection B K_bal)
  · obtain ⟨B0, ⟨s0⟩⟩ := hs
    have hbox := (A.detector_balanced_ideal_section B0 K_bal hK s0).1
    obtain ⟨D, hD, hb⟩ := probe_additive_row_box_sieve F A.zeta12 A.primitive_zeta12
      A.Sf e he htrace (A.balancedDyadicBox K_bal) hbox
    refine ⟨D * C0 ^ 2, mul_nonneg hD (sq_nonneg _), ?_⟩
    intro B s X V hX hV Q inst q instq hinj hq hnorm
    obtain ⟨p, rho, hrho, hrnorm, psi, hp, hphase⟩ :=
      hAdapter B s V hV Q q hinj hq hnorm
    refine ⟨psi, fun j => residue_orthogonal_of_primitive (psi j) (hp j), ?_⟩
    dsimp only
    intro z
    let P := Finset.univ.image rho
    have hP : ∀ beta ∈ P, ProbeSeparation.denominatorNorm F beta ≤ C0 * V := by
      intro beta hbeta
      obtain ⟨jd, _, rfl⟩ := Finset.mem_image.mp hbeta
      exact hrnorm jd
    have hCV : 1 ≤ C0 * V := by nlinarith [mul_le_mul_of_nonneg_right hC0 (by linarith : 0 ≤ V)]
    have hd := (hb X (C0 * V) hX hCV p P hP).2 z
    let f : ProbeSeparation.ReducedPair F A.Sf → ℝ := fun beta =>
      ‖∑ m, z m * ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf (-((m.val : F) * ProbeSeparation.value F p beta)))‖ ^ 2
    have hreindex : (∑ jd, f (rho jd)) = ∑ beta : ↥P, f beta.val := by
      rw [Finset.sum_coe_sort]
      symm
      exact Finset.sum_image (fun i _ j _ hij => hrho hij)
    have hh : (∑ jd, f (rho jd)) ≤ D * (X + (C0 * V) ^ 2) * ∑ m, ‖z m‖ ^ 2 :=
      hreindex.le.trans hd
    have hh' : (∑ j, ∑ d : (A.R ⧸ q j)ˣ, ‖∑ m,
        z m * psi j (Ideal.Quotient.mk (q j) m.val * (d : A.R ⧸ q j))‖ ^ 2) ≤
        D * (X + (C0 * V) ^ 2) * ∑ m, ‖z m‖ ^ 2 := by
      simpa only [Fintype.sum_sigma, f, ← hphase] using hh
    apply hh'.trans
    have hX0 : 0 ≤ X := le_trans (by norm_num) hX
    have hC2 : 1 ≤ C0 ^ 2 := by nlinarith
    have hscale : X + (C0 * V) ^ 2 ≤ C0 ^ 2 * (X + V ^ 2) := by
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_right hC2 hX0]
    have hE : 0 ≤ ∑ m, ‖z m‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale hD) hE
    simpa only [mul_assoc] using h
  · refine ⟨0, le_rfl, ?_⟩
    intro B s
    exact (hs ⟨B, ⟨s⟩⟩).elim

theorem additive_residue_row_sieve
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (K_bal : Set A.G) (hK : IsCompact K_bal) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (B : Subgroup A.V) (s : A.BalancedIdealSection B K_bal)
        (X V : ℝ), 1 ≤ X → 1 ≤ V →
        ∀ (Q : Type) [Fintype Q] (q : Q → Ideal A.R)
          [∀ j, Fintype (A.R ⧸ q j)],
          Function.Injective q →
          (∀ j, q j ≠ ⊥) →
          (∀ j, (Nat.card (A.R ⧸ q j) : ℝ) ≤ V) →
          ∃ psi : ∀ j, AddChar (A.R ⧸ q j) ℂ,
            (∀ j, IsOrthogonalResidueAddChar (psi j)) ∧
            let rows := (probe_additive_box_rows_finite F A.Sf X
              (A.balancedDyadicBox K_bal)
              (A.detector_balanced_ideal_section B K_bal hK s).1).toFinset
            ∀ z : ↥rows → ℂ,
              (∑ j, ∑ d : (A.R ⧸ q j)ˣ, ‖∑ m : ↥rows,
                z m * psi j (Ideal.Quotient.mk (q j) m.val *
                  (d : A.R ⧸ q j))‖ ^ 2) ≤
                D * (X + V ^ 2) * ∑ m : ↥rows, ‖z m‖ ^ 2 := by
  let T := CodifferentResidueSieve.canonical_trace_dual_data A
  exact additive_residue_row_sieve_of_scaled_trace_adapter F A K_bal hK
    (CodifferentResidueSieve.finiteTrace A) T.continuous T.compatible
    (CodifferentResidueSieve.denominatorScale A) (le_max_left _ _)
    (fun B s V hV Q _ q _ hinj hq hnorm =>
      CodifferentResidueSieve.scaled_reduced_pair_adapter A T K_bal B s
        V hV Q q hinj hq hnorm)

end
end DedekindZetaZeroFree.Detector.ExteriorDyadic

end

section

namespace DedekindZetaZeroFree.Detector

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain

def HasFixedFullSLocalTuple (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (omega : PrimitiveFrequencyCharacter F)
    (sigma : FixedSResidue.FullLocalCharacters A) : Prop :=
  (∀ w : InfinitePlace F, sigma.1 w = 1) ∧
    ∀ v : {v // v ∈ A.Sf},
      ∃ delta : (v.val.adicCompletion F)ˣ →ₜ* ℂˣ,
        delta.toMonoidHom = sigma.2 v ∧
          IsFrequencyLocalComponent F omega v.val delta

namespace ExteriorDyadicTransport

theorem local_twist_energy {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (s : A.BalancedIdealSection B K_bal)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hSigma : FixedSResidue.HasFiniteOrder A sigma)
    (T : Finset A.Exterior) (c : A.Exterior → ℂ) :
    (∑ a ∈ T, ‖c a * FixedSResidue.localInverseProduct A sigma
      ⟨s.generator a, (s.generates a).1⟩‖ ^ 2) =
      ∑ a ∈ T, ‖c a‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [norm_mul, FixedSResidue.localInverseProduct_norm A sigma hSigma, mul_one]

theorem row_energy {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (hK : IsCompact K_bal) (s : A.BalancedIdealSection B K_bal)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hSigma : FixedSResidue.HasFiniteOrder A sigma)
    (X : ℝ) (hX : 1 ≤ X) (T : Finset A.Exterior)
    (hT : ∀ a ∈ T, a ∈ A.balancedDyadicIdeals X) (c : A.Exterior → ℂ) :
    let rows := (probe_additive_box_rows_finite F A.Sf X
      (A.balancedDyadicBox K_bal) (A.detector_balanced_ideal_section B K_bal hK s).1).toFinset
    (∑ m ∈ rows, ‖A.balancedTransportCoeff B K_bal s T
      (fun a => c a * FixedSResidue.localInverseProduct A sigma
        ⟨s.generator a, (s.generates a).1⟩) m‖ ^ 2) =
      ∑ a ∈ T, ‖c a‖ ^ 2 := by
  exact (A.balanced_ideal_section_energy B K_bal hK s X hX T hT _).2.trans
    (local_twist_energy A B K_bal s sigma hSigma T c)

theorem row_sum {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (hK : IsCompact K_bal) (s : A.BalancedIdealSection B K_bal)
    (X : ℝ) (hX : 1 ≤ X) (T : Finset A.Exterior)
    (hT : ∀ a ∈ T, a ∈ A.balancedDyadicIdeals X)
    (c : A.Exterior → ℂ) (f : A.R → ℂ) :
    let rows := (probe_additive_box_rows_finite F A.Sf X
      (A.balancedDyadicBox K_bal) (A.detector_balanced_ideal_section B K_bal hK s).1).toFinset
    (∑ m ∈ rows, A.balancedTransportCoeff B K_bal s T c m * f m) =
      ∑ a ∈ T, c a * f (s.generator a) := by
  dsimp only
  let rows := (probe_additive_box_rows_finite F A.Sf X
    (A.balancedDyadicBox K_bal) (A.detector_balanced_ideal_section B K_bal hK s).1).toFinset
  have hsub : T.image s.generator ⊆ rows :=
    (A.balanced_ideal_section_energy B K_bal hK s X hX T hT c).1
  calc
    _ = ∑ m ∈ T.image s.generator, A.balancedTransportCoeff B K_bal s T c m * f m := by
      symm
      apply Finset.sum_subset hsub
      intro m hm hnot
      rw [A.balancedTransportCoeff_zero B K_bal s T c m hnot, zero_mul]
    _ = ∑ a ∈ T, A.balancedTransportCoeff B K_bal s T c (s.generator a) *
        f (s.generator a) := by
      apply Finset.sum_image
      intro a ha b hb hab
      exact A.balanced_ideal_section_injective B K_bal s hab
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [A.balancedTransportCoeff_generator B K_bal s T c a ha]

theorem conductor_fiber_gauss_sieve
    {I Q T : Type*} [Fintype I] [Fintype Q] [Fintype T]
    (g : I → Q) (R : Q → Type*) [∀ q, CommRing (R q)] [∀ q, Fintype (R q)]
    (chi : ∀ q, {i : I // g i = q} → MulChar (R q) ℂ)
    (hchi : ∀ q, Function.Injective (chi q))
    (psi : ∀ q, AddChar (R q) ℂ)
    (hp : ∀ q i, IsPrimitiveResidueCharacter (chi q i))
    (ho : ∀ q, IsOrthogonalResidueAddChar (psi q))
    (row : ∀ q, T → R q) (c : T → ℂ)
    (value : I → ℂ)
    (hv : ∀ q (i : {i : I // g i = q}),
      value i = ∑ t, c t * chi q i (row q t)) :
    (∑ i, ‖value i‖ ^ 2) ≤
      ∑ q, ∑ d : (R q)ˣ, ‖∑ t, c t * psi q (row q t * (d : R q))‖ ^ 2 := by
  classical
  rw [← Fintype.sum_fiberwise g (fun i => ‖value i‖ ^ 2)]
  apply Finset.sum_le_sum
  intro q hq
  simp_rw [hv q]
  exact le_trans
    (detector_single_modulus_gauss_sieve (R q) {i : I // g i = q}
      (chi q) (hchi q) (psi q) (hp q) (ho q) T (row q) c).1
    (detector_single_modulus_gauss_sieve (R q) {i : I // g i = q}
      (chi q) (hchi q) (psi q) (hp q) (ho q) T (row q) c).2

theorem conductor_scale_bound (C0 U : ℝ) (hU : 2 ≤ U) :
    (max 1 (C0 * U)) ^ 2 ≤ max (C0 ^ 2) (1 / 4) * U ^ 2 := by
  have hUp : 0 ≤ U := le_trans (by norm_num) hU
  by_cases h : 1 ≤ C0 * U
  · rw [max_eq_right h, mul_pow]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg U)
  · rw [max_eq_left (le_of_not_ge h)]
    have hm : (1 / 4 : ℝ) ≤ max (C0 ^ 2) (1 / 4) := le_max_right _ _
    have hsq : 4 ≤ U ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg U)]

theorem conductor_scale_energy_bound (D C0 X U E : ℝ)
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hU : 2 ≤ U) (hE : 0 ≤ E) :
    D * (X + (max 1 (C0 * U)) ^ 2) * E ≤
      (D * max 1 (max (C0 ^ 2) (1 / 4))) * (X + U ^ 2) * E := by
  let M := max 1 (max (C0 ^ 2) (1 / 4))
  have hMX : X ≤ M * X := le_mul_of_one_le_left hX (le_max_left _ _)
  have hMU : (max 1 (C0 * U)) ^ 2 ≤ M * U ^ 2 :=
    (conductor_scale_bound C0 U hU).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg U))
  have hscale : X + (max 1 (C0 * U)) ^ 2 ≤ M * (X + U ^ 2) := by
    nlinarith
  have hd := mul_le_mul_of_nonneg_left hscale hD
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd hE

theorem row_gauss_to_ideal_bound
    {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (hK : IsCompact K_bal) (s : A.BalancedIdealSection B K_bal)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hSigma : FixedSResidue.HasFiniteOrder A sigma)
    (D C0 X U : ℝ) (hD : 0 ≤ D) (hX : 1 ≤ X) (hU : 2 ≤ U)
    (I Q : Type) [Fintype I] [Fintype Q]
    (omega : I → PrimitiveFrequencyCharacter F) (g : I → Q)
    (q : Q → Ideal A.R) [∀ j, Fintype (A.R ⧸ q j)]
    (chi : ∀ j, {i : I // g i = j} → MulChar (A.R ⧸ q j) ℂ)
    (hinj : ∀ j, Function.Injective (chi j))
    (psi : ∀ j, AddChar (A.R ⧸ q j) ℂ)
    (hp : ∀ j i, IsPrimitiveResidueCharacter (chi j i))
    (ho : ∀ j, IsOrthogonalResidueAddChar (psi j))
    (hbridge : ∀ j (i : {i : I // g i = j}) (a : A.Exterior)
      (m : FixedSResidue.NonzeroSInteger A),
      Ideal.span {m.val} = A.extendIdeal a →
        (omega i).character a.val = FixedSResidue.localInverseProduct A sigma m *
          chi j i (Ideal.Quotient.mk (q j) m.val))
    (T : Finset A.Exterior) (hT : ∀ a ∈ T, a ∈ A.balancedDyadicIdeals X)
    (c : A.Exterior → ℂ) :
    let rows := (probe_additive_box_rows_finite F A.Sf X
      (A.balancedDyadicBox K_bal) (A.detector_balanced_ideal_section B K_bal hK s).1).toFinset
    (∀ z : ↥rows → ℂ,
      (∑ j, ∑ d : (A.R ⧸ q j)ˣ, ‖∑ m : ↥rows,
        z m * psi j (Ideal.Quotient.mk (q j) m.val * (d : A.R ⧸ q j))‖ ^ 2) ≤
        D * (X + (max 1 (C0 * U)) ^ 2) * ∑ m : ↥rows, ‖z m‖ ^ 2) →
    (∑ i, ‖∑ a ∈ T, c a * (omega i).character a.val‖ ^ 2) ≤
      (D * max 1 (max (C0 ^ 2) (1 / 4))) * (X + U ^ 2) *
        ∑ a ∈ T, ‖c a‖ ^ 2 := by
  let rows := (probe_additive_box_rows_finite F A.Sf X
    (A.balancedDyadicBox K_bal) (A.detector_balanced_ideal_section B K_bal hK s).1).toFinset
  let ct : A.Exterior → ℂ := fun a => c a * FixedSResidue.localInverseProduct A sigma
    ⟨s.generator a, (s.generates a).1⟩
  let z : ↥rows → ℂ := fun m => A.balancedTransportCoeff B K_bal s T ct m.val
  have hv : ∀ j (i : {i : I // g i = j}),
      (∑ a ∈ T, c a * (omega i).character a.val) =
        ∑ m : ↥rows, z m * chi j i (Ideal.Quotient.mk (q j) m.val) := by
    intro j i
    rw [Finset.sum_coe_sort rows (fun m =>
      A.balancedTransportCoeff B K_bal s T ct m * chi j i (Ideal.Quotient.mk (q j) m))]
    rw [row_sum A B K_bal hK s X hX T hT ct]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hbridge j i a ⟨s.generator a, (s.generates a).1⟩ (s.generates a).2]
    exact (mul_assoc _ _ _).symm
  have henergy : (∑ m : ↥rows, ‖z m‖ ^ 2) = ∑ a ∈ T, ‖c a‖ ^ 2 := by
    rw [Finset.sum_coe_sort rows (fun m =>
      ‖A.balancedTransportCoeff B K_bal s T ct m‖ ^ 2)]
    exact row_energy A B K_bal hK s sigma hSigma X hX T hT c
  dsimp only
  intro hadd
  have hg := conductor_fiber_gauss_sieve g (fun j => A.R ⧸ q j) chi hinj psi hp ho
    (fun j m => Ideal.Quotient.mk (q j) m.val) z
    (fun i => ∑ a ∈ T, c a * (omega i).character a.val) hv
  calc
    _ ≤ _ := hg
    _ ≤ D * (X + (max 1 (C0 * U)) ^ 2) * ∑ m : ↥rows, ‖z m‖ ^ 2 := hadd z
    _ = D * (X + (max 1 (C0 * U)) ^ 2) * ∑ a ∈ T, ‖c a‖ ^ 2 := by rw [henergy]
    _ ≤ _ := conductor_scale_energy_bound D C0 X U _ hD (by linarith) hU
      (Finset.sum_nonneg (fun a _ => sq_nonneg ‖c a‖))

end ExteriorDyadicTransport

theorem detector_exterior_dyadic_conductor_sieve
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V)
    (K_bal : Set A.G) (hK : IsCompact K_bal)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hSigma : FixedSResidue.HasFiniteOrder A sigma)
    (C0 : ℝ) (hC0 : 0 < C0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (s : A.BalancedIdealSection B K_bal)
        (X U : ℝ), 1 ≤ X → 2 ≤ U →
        ∀ (n : ℕ) (omega : Fin n → PrimitiveFrequencyCharacter F),
          (Pairwise (fun i j =>
            ¬ samePrimitiveFrequencyCharacter F (omega i) (omega j))) →
          (∀ i : Fin n, HasFixedFullSLocalTuple F A (omega i) sigma) →
          (∀ i : Fin n, (Ideal.absNorm (omega i).conductor : ℝ) ≤ C0 * U) →
          ∀ c : A.Exterior →₀ ℂ,
            (∀ a ∈ c.support, a ∈ A.balancedDyadicIdeals X) →
            (∑ i : Fin n, ‖∑ a ∈ c.support, c a * (omega i).character a.val‖ ^ 2) ≤
              K * (X + U ^ 2) * ∑ a ∈ c.support, ‖c a‖ ^ 2 := by
  obtain ⟨D, hD, hadditive⟩ :=
    ExteriorDyadic.additive_residue_row_sieve F A K_bal hK
  refine ⟨D * max 1 (max (C0 ^ 2) (1 / 4)),
    mul_nonneg hD (le_trans (by norm_num) (le_max_left _ _)), ?_⟩
  intro s X U hX hU n omega hdist hlocal hconductor c hc
  have hprincipal : FixedSInjectivity.ExteriorPrincipalization A := by
    intro a
    exact ⟨⟨s.generator a, (s.generates a).1⟩, (s.generates a).2⟩
  obtain ⟨r, g, q, hfinite, chi, hqinj, hqzero, hqnorm, hchi, hp, hbridge⟩ :=
    ExteriorDyadic.primitive_residue_fibers F A hprincipal sigma hSigma
      (Fin n) omega hdist hlocal (C0 * U) hconductor
  letI : ∀ j, Fintype (A.R ⧸ q j) := hfinite
  obtain ⟨psi, ho, hadd⟩ := hadditive B s X (max 1 (C0 * U)) hX
    (le_max_left _ _) (Fin r) q hqinj hqzero
    (fun j => (hqnorm j).trans (le_max_right _ _))
  exact ExteriorDyadicTransport.row_gauss_to_ideal_bound A B K_bal hK s sigma hSigma
    D C0 X U hD hX hU (Fin n) (Fin r) omega g q chi hchi psi hp ho hbridge
    c.support hc c hadd

end
end DedekindZetaZeroFree.Detector

end
