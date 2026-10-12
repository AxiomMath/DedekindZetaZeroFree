module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.ProbeRowCharacters

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.PrincipalProbeConstruction.Inputs
variable {F : Type} [Field F] [NumberField F]

 theorem exterior_coprime (A : SArithmeticData F) (I : A.Exterior) :
    I.val ⊔ A.modulus = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (I.val ⊔ A.modulus) h
  have hp0 : p ≠ ⊥ := by
    intro he
    apply I.property.1
    apply bot_unique
    have hh : I.val ≤ p := le_trans le_sup_left hle
    simpa only [he] using hh
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp.isPrime, hp0⟩
  have hv : v ∈ A.Sf := A.modulus_support v (le_trans le_sup_right hle)
  have hi := (A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v hv
  have : I.val ⊔ v.asIdeal ≤ p := sup_le (le_trans le_sup_left hle) le_rfl
  rw [hi] at this
  exact hp.ne_top (top_unique this)

def principalCorrection (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (D : A.GaussCorrectionOutput σ η hS) (hη : η.IsPrincipal) :
    A.GaussCorrectionOutput σ η hS := by
  have hc : Continuous (1 : A.ArithmeticIdeleClasses →* Circle) := continuous_const
  have hu : A.IdeleCharacterUnramifiedOutside (1 : A.ArithmeticIdeleClasses →* Circle) :=
    fun _ _ _ _ => rfl
  have hi : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
      A.ideleInfiniteComponent (1 : A.ArithmeticIdeleClasses →* Circle) w z = 1 :=
    fun _ _ => rfl
  have ht := SArithmeticData.CorrectionAssembly.correctionTheta_continuous A
    D.Λ D.G 1 D.Λ_continuous D.G_continuous hc
  have hut := SArithmeticData.CorrectionAssembly.correctionTheta_unramified A
    D.Λ D.G 1 D.Λ_unramified D.G_unramified hu
  obtain ⟨hideal, hunit, hfinite⟩ := SArithmeticData.GaussCorrection.localArithmeticLaws
    A (A.correctionTheta D.Λ D.G 1) ht hut
  exact { D with
    η_id := 1
    eta_continuous := hc
    eta_finiteOrder := ⟨1, by norm_num, fun _ => by simp⟩
    eta_unramified := hu
    eta_ideal := fun I x hx => (hη I.val I.property.1 (exterior_coprime A I)).symm
    eta_infinity := hi
    theta_ideal_local := hideal
    theta_unit := hunit
    theta_continuous := ht
    theta_unramified := hut
    finite_locallyConstant := hfinite
    infinity_angular := SArithmeticData.CorrectionAssembly.correctionTheta_infinity_angular
      A σ D.Λ D.G 1 D.Λ_infinity D.G_infinity hi
    infinity_no_radial := SArithmeticData.CorrectionAssembly.correctionTheta_infinity_no_radial
      A σ D.Λ D.G 1 D.Λ_infinity D.G_infinity hi }

@[simp] theorem principalCorrection_target (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (D : A.GaussCorrectionOutput σ η hS) (hη : η.IsPrincipal) :
    (principalCorrection A σ η hS D hη).η_id = 1 := rfl

def principalContext (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (hη : η.IsPrincipal) :
    A.GeneralArithmeticContext σ η hS := by
  let D := principalCorrection A σ η hS C.correction hη
  exact { C with
    correction := D
    prime_target := fun I v hIv p hp a ha hap x hx =>
      D.prime_theta I v hIv p hp a ha hap x hx }

@[simp] theorem principalContext_target (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (hη : η.IsPrincipal) :
    (principalContext A σ η hS C hη).correction.η_id = 1 := rfl

end DedekindZetaZeroFree.PrincipalProbeConstruction.Inputs

end
