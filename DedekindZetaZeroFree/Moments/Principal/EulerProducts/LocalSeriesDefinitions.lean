module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.CharacterSums.Gauss.ResidueRowFourierTransform
public import DedekindZetaZeroFree.LFunctions.Hecke.ExteriorIdealEulerProducts

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

abbrev ExteriorPrime (A : SArithmeticData F) :=
  {p : HeightOneSpectrum (𝓞 F) // p.asIdeal ⊔ A.cS = ⊤}

def primeIdeal (p : ExteriorPrime A) : A.Exterior :=
  ⟨p.val.asIdeal, p.val.ne_bot, p.property⟩

abbrev LocalField (p : ExteriorPrime A) := p.val.adicCompletion F
abbrev LocalIntegers (p : ExteriorPrime A) := p.val.adicCompletionIntegers F

def generator (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) : A.R :=
  Classical.choose (C.allowed_integral (primeIdeal p))

private theorem generator_spec (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    ∃ a : Fˣ, A.Generates (primeIdeal p) (generator C p) ∧
      (a : F) = (generator C p : F) ∧ A.IsAllowed C.correction.B a :=
  Classical.choose_spec (C.allowed_integral (primeIdeal p))

theorem generator_generates (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : A.Generates (primeIdeal p) (generator C p) :=
  (generator_spec C p).choose_spec.1

theorem generator_allowed (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    A.IsAllowed C.correction.B (Units.mk0 (generator C p : F)
      (by exact_mod_cast (generator_generates C p).1)) := by
  obtain ⟨a, _, ha, hallowed⟩ := generator_spec C p
  convert hallowed using 1
  apply Units.ext
  exact ha.symm

def uniformizer (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : LocalField p :=
  algebraMap F (LocalField p) (generator C p : F)

def Q (p : ExteriorPrime A) : ℝ := A.exteriorNorm (primeIdeal p)

def powerIdeal (p : ExteriorPrime A) (n : ℕ) : A.Exterior :=
  ExteriorIdealEuler.pow (primeIdeal p) n

 theorem generator_power_generates (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    A.Generates (powerIdeal p n) (generator C p ^ n) := by
  refine ⟨pow_ne_zero _ (generator_generates C p).1, ?_⟩
  rw [← Ideal.span_singleton_pow, (generator_generates C p).2]
  exact (Ideal.map_pow _ _ _).symm

abbrev Residue (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :=
  FiniteTransform.Residue A.R.toSubring (generator C p ^ n)

instance residueFinite (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : Finite (Residue C p n) := by
  change Finite (A.R ⧸ Ideal.span {generator C p ^ n})
  rw [(generator_power_generates C p n).2]
  exact A.exteriorResidue_finite (powerIdeal p n)

instance residueFintype (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : Fintype (Residue C p n) := Fintype.ofFinite _

def residueMap (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : A.R →+* Residue C p n :=
  FiniteTransform.residueMap A.R.toSubring (generator C p ^ n)

def lifts (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : FiniteTransform.ResidueLifts
      A.R.toSubring (generator C p ^ n) :=
  FiniteTransform.canonicalLifts A.R.toSubring (generator C p ^ n)

def chi (p : ExteriorPrime A) : MulChar (A.R ⧸ A.extendIdeal (primeIdeal p)) ℂ :=
  A.sexticResiduePowerChar σ (primeIdeal p) 1

def reduction (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) :
    Residue C p n →+* (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
  Ideal.Quotient.factor (by
    rw [← (generator_generates C p).2]
    apply Ideal.span_le.mpr
    rintro x (rfl : x = generator C p ^ n)
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact Ideal.mem_span_singleton'.mpr ⟨generator C p ^ r, by rw [pow_succ]⟩)

def maskedPower (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (a : ℤ) (x : Residue C p n) : ℂ :=
  if hn : n = 0 then 1 else
    if IsUnit x then
      A.sexticResiduePowerChar σ (primeIdeal p) a (reduction C p n hn x)
    else 0

def negativeTrace (p : ExteriorPrime A) : AddChar (LocalField p) Circle :=
  -(ResidueTrace.localTraceCharacter p.val)

def quotientTrace (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : AddChar (Residue C p n) Circle := by
  let ψ := A.residueTraceCharacter hS (powerIdeal p n) (generator C p ^ n)
    (generator_power_generates C p n)
  rw [← (generator_power_generates C p n).2] at ψ
  exact ψ

def psi (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : Residue C p n) : ℂ :=
  (quotientTrace C p n x : ℂ)

def Ctk (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) : ℂ :=
  ∑ d : Residue C p k,
    if residueMap C p k (generator C p ^ J) =
        residueMap C p k (generator C p ^ t) * d then
      maskedPower C p k k d *
        ∑ v : Residue C p t, maskedPower C p t t v *
          psi C p (k + t) (residueMap C p (k + t)
            ((generator C p ^ J - generator C p ^ t * (lifts C p k).val d) *
              (lifts C p t).val v))
    else 0

def T (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) (y : Residue C p 1) : ℂ :=
  ∑ x : Residue C p 1, maskedPower C p 1 a x * psi C p 1 (y * x)

def tau (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) : ℂ := T C p a 1

def gammaTwo (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : ℂ :=
  A.idealGauss σ hS (primeIdeal p) (generator C p) (generator_generates C p) 2

def vartheta (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : ℂ :=
  (A.correctionLS C.correction.Λ C.correction.G C.correction.η_id
    (A.diagonal (Units.mk0 (generator C p : F)
      (by exact_mod_cast (generator_generates C p).1))) : ℂ)

def qPower (p : ExteriorPrime A) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log (Q p) : ℂ))

def seriesTerm (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1})
    (e : Fin 2) (l k m : ℕ) (ξ w z : ℂ) : ℂ :=
  gammaTwo C p ^ e.val * vartheta C p ^ (e.val + 3 * l) *
    θ.val ^ ((k : ℤ) - (e.val : ℤ) - 3 * (l : ℤ)) *
    Ctk C p (e.val + 3 * l) k (j.val + 6 * m) *
    qPower p (-(e.val : ℂ) * (1 / 2 + ξ) - (l : ℂ) * (1 + 3 * ξ) -
      (k : ℂ) * w - 6 * (m : ℂ) * z)

def f (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1})
    (ξ w z : ℂ) : ℂ :=
  ∑' i : Fin 2 × ℕ × ℕ × ℕ,
    seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 ξ w z

end DedekindZetaZeroFree.LocalFiniteSums

end
