module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.Definitions

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.CompatiblePrimeRawLocal.CongruenceBridgeRace
open LocalFiniteSums CRTRawLocalModel
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem completion_divisibility_iff (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (k : ℕ) (x : A.R) :
    (∃ r : LocalIntegers p,
      algebraMap F (LocalField p) (x : F) = uniformizer C p ^ k * (r : LocalField p)) ↔
    ∃ z : A.R, x = generator C p ^ k * z := by
  let i := A.exteriorIntegerMap (primeIdeal p) p.val rfl
  let e := A.exteriorLocalResidueEquiv (primeIdeal p) p.val rfl
  let res := IsLocalRing.residue (LocalIntegers p)
  have hres (y : A.R) : res (i y) = 0 ↔ y ∈ Ideal.span {generator C p} := by
    rw [(generator_generates C p).2]
    have he := A.exteriorLocalResidueEquiv_apply (primeIdeal p) p.val rfl y
    change e (Ideal.Quotient.mk _ y) = res (i y) at he
    rw [← he, ← map_zero e, e.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hπ : res (i (generator C p)) = 0 :=
    (hres _).2 (Ideal.subset_span (Set.mem_singleton _))
  have core (n : ℕ) (y : A.R) :
      (∃ r : LocalIntegers p, i y = i (generator C p) ^ n * r) ↔
      ∃ z : A.R, y = generator C p ^ n * z := by
    induction n generalizing y with
    | zero =>
      simp only [pow_zero, one_mul]
      exact ⟨fun _ => ⟨y, rfl⟩, fun _ => ⟨i y, rfl⟩⟩
    | succ n ih =>
      constructor
      · rintro ⟨r, hr⟩
        have hy : res (i y) = 0 := by
          rw [hr, map_mul, map_pow, hπ, zero_pow (Nat.succ_ne_zero n), zero_mul]
        obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp ((hres y).1 hy)
        have hz' : i z = i (generator C p) ^ n * r := by
          have hiπ : i (generator C p) ≠ 0 := by
            intro hh
            have hh' := congrArg (fun u : LocalIntegers p => (u : LocalField p)) hh
            have hg : (generator C p : F) = 0 := by
              apply (algebraMap F (LocalField p)).injective
              simpa [i, SArithmeticData.exteriorIntegerMap] using hh'
            exact (generator_generates C p).1 (Subtype.ext hg)
          apply mul_left_cancel₀ hiπ
          calc
            i (generator C p) * i z = i y := by rw [← map_mul, mul_comm, hz]
            _ = i (generator C p) * (i (generator C p) ^ n * r) := by
              rw [hr, pow_succ']; ring
        obtain ⟨w, hw⟩ := (ih z).1 ⟨r, hz'⟩
        refine ⟨w, ?_⟩
        rw [← hz, hw, pow_succ']
        ring
      · rintro ⟨z, rfl⟩
        exact ⟨i z, by rw [map_mul, map_pow]⟩
  convert core k x using 1
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, Subtype.ext hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, congrArg (fun u : LocalIntegers p => (u : LocalField p)) hr⟩

theorem congruent_iff_residue (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (k : ℕ) (x y : A.R) :
    Congruent C p k (algebraMap F (LocalField p) (x : F))
      (algebraMap F (LocalField p) (y : F)) ↔
    residueMap C p k x = residueMap C p k y := by
  have hh := completion_divisibility_iff C p k (x - y)
  rw [show (algebraMap F (LocalField p)) ((x - y : A.R) : F) =
      algebraMap F (LocalField p) (x : F) - algebraMap F (LocalField p) (y : F) by
        simp] at hh
  rw [CRTRawLocalModel.Congruent, hh]
  change _ ↔ Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ y
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz, mul_comm]⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [← hz, mul_comm]⟩

end DedekindZetaZeroFree.CompatiblePrimeRawLocal.CongruenceBridgeRace

end
