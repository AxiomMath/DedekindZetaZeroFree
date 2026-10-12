module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.UniformNormalizationData
public import DedekindZetaZeroFree.LargeSieve.Bilinear.GcdPairRowCharacterIdentity
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.PrimitiveProductValues
public import DedekindZetaZeroFree.LargeSieve.Bilinear.ReflectedSigmaFourBlocks
public import DedekindZetaZeroFree.LargeSieve.Bilinear.MobiusTransformTails
public import DedekindZetaZeroFree.Analysis.DyadicLength

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical ContDiff BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

structure Context (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) where
  D : Sieve.AllIndexNormalizedFamilyData Q
  core : D.bad = c
  hF : NumberField.IsTotallyComplex F
  M : ℝ
  N : ℝ
  K : ℝ
  δ : ℝ
  W : ℝ → ℝ
  hW : Sieve.SieveWeight W
  d : Ideal (𝓞 F)
  hd0 : d ≠ ⊥
  hd : Squarefree d
  hdc : d ⊔ c = ⊤
  g : Q.G
  lam : Ideal (𝓞 F) → ℂ

variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def norm (a : Ideal (𝓞 F)) : ℝ := Ideal.absNorm a

namespace Context

def source (C : Context Q) (x : ℝ) : ℂ := C.W x

def kappa (C : Context Q) : ℂ :=
  SquareSecondPass.kappa (principalHeckeData F C.hF)

def mass (C : Context Q) : ℂ := ∫ t in Set.Ioi (0 : ℝ), C.source (t ^ 2)

def origin (C : Context Q) : ℂ :=
  -(2 : ℂ) ^ (principalComplexPlaces F - 1) * C.kappa * mellin C.source 1

def estimatePrefactor (C : Context Q) : ℝ := norm C.d * C.M / C.N

def Y1 (C : Context Q) (B : ℝ) (e : Ideal (𝓞 F)) : ℝ :=
  C.N * Real.sqrt (norm e) / (norm C.d * Real.sqrt (2 * B * C.M)) *
    Real.rpow (C.M * C.N) (-C.δ)

def Z1 (C : Context Q) (B : ℝ) (e : Ideal (𝓞 F)) : ℝ :=
  C.N * Real.sqrt (norm e) / (norm C.d * Real.sqrt (B * C.M)) *
    Real.rpow (C.M * C.N) C.δ

def Y2 (C : Context Q) (B : ℝ) : ℝ :=
  Real.sqrt (C.M / (2 * B)) * Real.rpow (C.M * C.N) (-C.δ)

def Z2 (C : Context Q) (B : ℝ) : ℝ :=
  Real.sqrt (C.M / B) * Real.rpow (C.M * C.N) C.δ

def L1 (C : Context Q) : ℝ := 8 * Real.rpow (C.M * C.N) (2 * C.δ)

def L2 (C : Context Q) : ℝ := C.L1

def columns (C : Context Q) : Finset (Ideal (𝓞 F)) :=
  (Sieve.idealAdmissibleFinset F c (2 * C.N / norm C.d)).filter
    (fun u => C.d * u ∈ Sieve.paperShell F c C.N ∧ Q.cls (C.d * u) = C.g)

structure ValidPair (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) : Prop where
  hu0 : p.1 ≠ ⊥
  hv0 : p.2 ≠ ⊥
  hu : Squarefree p.1
  hv : Squarefree p.2
  huc : p.1 ⊔ c = ⊤
  hvc : p.2 ⊔ c = ⊤
  hdu : Squarefree (C.d * p.1)
  hdv : Squarefree (C.d * p.2)
  hduc : (C.d * p.1) ⊔ c = ⊤
  hdvc : (C.d * p.2) ⊔ c = ⊤
  huv : p.1 ⊔ p.2 = ⊤
  hduv : C.d ⊔ (p.1 * p.2) = ⊤
  hclass : Q.cls (C.d * p.1) = Q.cls (C.d * p.2)
  hquotientClass : Q.cls p.1 = Q.cls p.2
  offDiagonal : p.1 * p.2 ≠ ⊤

def pairs (C : Context Q) : Finset (Ideal (𝓞 F) × Ideal (𝓞 F)) :=
  (C.columns ×ˢ C.columns).filter (ValidPair C)

 theorem transport_exists (C : Context Q)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : ValidPair C p) :
    ∃ ψ : DedekindZetaZeroFree.RayClassCharacter F (p.1 * p.2),
      ψ.IsPrimitive ∧
      (∀ I, I ⊔ (Q.cond p.1 * Q.cond p.2) = ⊤ →
        ψ I = (Q.χ p.1) I * starRingEnd ℂ ((Q.χ p.2) I)) ∧
      (∀ I, I ⊔ (c * C.d) = ⊤ →
        (Q.χ (C.d * p.1)) I * starRingEnd ℂ ((Q.χ (C.d * p.2)) I) = ψ I ∧
          ψ I = (Q.χ p.1) I * starRingEnd ℂ ((Q.χ p.2) I)) := by
  apply pairRowTransport C.D.original_ne_bot Q
    (q := c) (by simpa only [C.core] using C.D.bad_ne_bot) (dvd_refl c)
    (fun b hb hbc => ?_) C.hd0 hp.hu0 hp.hv0 C.hd hp.hu hp.hv
    hp.hdu hp.hdv hp.hduc hp.hdvc hp.huv hp.hduv hp.hclass
  have h := And.intro (C.D.all_conductor_dvd b hb hbc) (C.D.all_index_dvd b hb hbc)
  simpa only [C.core] using h

def primitive (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : ValidPair C p) : DedekindZetaZeroFree.RayClassCharacter F (p.1 * p.2) :=
  (transport_exists C p hp).choose

theorem primitive_spec (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : ValidPair C p) :
    (C.primitive p hp).IsPrimitive ∧
      (∀ I, I ⊔ (Q.cond p.1 * Q.cond p.2) = ⊤ →
        C.primitive p hp I = (Q.χ p.1) I * starRingEnd ℂ ((Q.χ p.2) I)) ∧
      (∀ I, I ⊔ (c * C.d) = ⊤ →
        (Q.χ (C.d * p.1)) I * starRingEnd ℂ ((Q.χ (C.d * p.2)) I) =
          C.primitive p hp I ∧
          C.primitive p hp I = (Q.χ p.1) I * starRingEnd ℂ ((Q.χ p.2) I)) :=
  (transport_exists C p hp).choose_spec

theorem primitive_quadratic (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : ValidPair C p) (I : Ideal (𝓞 F)) :
    (C.primitive p hp I) ^ 3 = C.primitive p hp I :=
  ((primitiveProductQuadratic Q hp.hu0 hp.hv0 hp.hu hp.hv hp.huc hp.hvc hp.huv
    hp.hquotientClass (C.primitive p hp) (C.primitive_spec p hp).2.1).1 I).2.2.1

def pairSum (C : Context Q)
    (f : (p : Ideal (𝓞 F) × Ideal (𝓞 F)) → ValidPair C p → ℂ) : ℂ :=
  ∑ p ∈ C.pairs, if hp : ValidPair C p then f p hp else 0

def coefficient (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) : ℂ :=
  C.lam (C.d * p.1) * star (C.lam (C.d * p.2))

def mobiusDivisors (C : Context Q) : Finset (Ideal (𝓞 F)) :=
  idealDivisors (c * C.d).radical

def dualScale (C : Context Q) (e : Ideal (𝓞 F))
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) : ℝ := norm e * norm (p.1 * p.2) / C.M

def prefactor (C : Context Q) (e : Ideal (𝓞 F))
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : ValidPair C p) : ℂ :=
  (UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e *
    ((C.M : ℂ) / ((norm e : ℂ) * (Real.sqrt (norm (p.1 * p.2)) : ℂ)))

def largeDensity (j : Ideal (𝓞 F)) (Z : ℝ) : ℂ :=
  ∑ f ∈ (idealDivisors j).filter (fun f => Z < norm f),
    (UniqueFactorizationMonoid.moebius f : ℂ) / (norm f : ℂ)

def originDivisors (j : Ideal (𝓞 F)) (Z : ℝ) : ℂ :=
  ∑ f ∈ (idealDivisors j).filter (fun f => norm f ≤ Z),
    (UniqueFactorizationMonoid.moebius f : ℂ)

def middle (k : ℝ → ℂ) (j : Ideal (𝓞 F)) (T Y Z L : ℝ) : ℂ :=
  ∑ f ∈ (idealDivisors j).filter (fun f => Y < norm f ∧ norm f ≤ Z),
    (UniqueFactorizationMonoid.moebius f : ℂ) * (T / norm f : ℂ) *
      ∑ b ∈ (boundedNormIdeals F L).filter (fun b => b ≠ ⊥),
        k (norm b * T / norm f)

def originalKernel (C : Context Q) : ℝ → ℂ :=
  fieldTransform (principalDiscriminant F) (principalComplexPlaces F)
    (fun x => C.source (x ^ 2))

def reflectedKernel (C : Context Q) : ℝ → ℂ :=
  SquareSecondPass.reflectedTransform (principalDiscriminant F)
    (principalComplexPlaces F) C.source

def originalRows (C : Context Q) (B : ℝ) (unit : Bool := false) : Finset (Ideal (𝓞 F)) :=
  if unit then ReflectedSigma4.unitRows c (c * C.d) C.K
  else sigma4DyadicRows F (c * C.d) C.K B

def reflectedCoreRows (C : Context Q) (B : ℝ) (unit : Bool := false) :
    Finset (Ideal (𝓞 F)) :=
  if unit then ReflectedSigma4.unitRows c c C.K
  else sigma4DyadicRows F c C.K B

def reflectedRowIndices (C : Context Q) (B : ℝ) (unit : Bool := false) :
    Finset (Ideal (𝓞 F) × Ideal (𝓞 F)) :=
  ((squarefreeBadPool c) ×ˢ C.reflectedCoreRows B unit).filter
    (fun tr => tr.1 ⊔ tr.2 = ⊤ ∧ Squarefree (tr.1 * tr.2) ∧ tr.1 * tr.2 ≠ ⊥)

def reflectedRows (C : Context Q) (B : ℝ) (unit : Bool := false) :
    Finset (Ideal (𝓞 F)) :=
  (C.reflectedRowIndices B unit).image (fun tr => tr.1 * tr.2)

def reflectedTopRows (C : Context Q) : Finset (Ideal (𝓞 F)) :=
  (C.reflectedRows 1 true).filter (fun a => a = ⊤)

def reflectedSupportedUnitRows (C : Context Q) : Finset (Ideal (𝓞 F)) :=
  (C.reflectedRows 1 true).filter (fun a => a ≠ ⊤)

end Context

def T (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        C.primitive p hp a * C.kappa *
          (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
          (sigma4Rho (p.1 * p.2) : ℂ)

def Tprime (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ a ∈ C.originalRows B unit,
      C.primitive p hp a * C.kappa * (Real.sqrt (C.M / norm a) : ℂ) * C.mass *
        (sigma4Rho ((c * C.d) * (p.1 * p.2)) : ℂ)

def E1 (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        C.primitive p hp a * C.kappa *
          (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
          Context.largeDensity (p.1 * p.2) (C.Z1 B e)

def E2 (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  -C.pairSum fun p hp => C.coefficient p *
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        C.primitive p hp a * C.origin * Context.originDivisors (p.1 * p.2) (C.Z1 B e)

def E3 (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        C.primitive p hp a * Context.middle C.reflectedKernel (p.1 * p.2)
          (Real.sqrt (C.dualScale e p / norm a)) (C.Y1 B e) (C.Z1 B e) C.L1

def E4 (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ a ∈ C.originalRows B unit,
      C.primitive p hp a * C.kappa * (Real.sqrt (C.M / norm a) : ℂ) * C.mass *
        Context.largeDensity ((c * C.d) * (p.1 * p.2)) (C.Z2 B)

def E5 (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ a ∈ C.originalRows B unit,
      C.primitive p hp a * Context.middle C.originalKernel ((c * C.d) * (p.1 * p.2))
        (Real.sqrt (C.M / norm a)) (C.Y2 B) (C.Z2 B) C.L2

namespace Context

theorem source_smooth (C : Context Q) : ContDiff ℝ ∞ C.source :=
  Complex.ofRealCLM.contDiff.comp C.hW.smooth

theorem source_support (C : Context Q) :
    Function.support C.source ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2) := by
  intro x hx
  by_contra h
  exact hx (by simp [source, C.hW.zero_outside x h])

theorem source_compact (C : Context Q) : HasCompactSupport C.source :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc C.source_support

theorem source_zero (C : Context Q) : C.source 0 = 0 := by
  simp [source, C.hW.zero_outside 0 (by norm_num)]

def originalRemainder (C : Context Q) (j : Ideal (𝓞 F)) (T Y Z L : ℝ) : ℂ :=
  ReflectedTails.primalTail F (fun x => C.source (x ^ 2)) T
    ((idealDivisors j).filter (fun f => Z < norm f))
    (fun f => (UniqueFactorizationMonoid.moebius f : ℂ)) +
  ReflectedTails.smallDualTail F C.originalKernel T
    ((idealDivisors j).filter (fun f => norm f ≤ Y))
    (fun f => (UniqueFactorizationMonoid.moebius f : ℂ)) +
  ReflectedTails.dualCutoffTail F C.originalKernel T L
    ((idealDivisors j).filter (fun f => Y < norm f ∧ norm f ≤ Z))
    (fun f => (UniqueFactorizationMonoid.moebius f : ℂ))

def reflectedRemainder (C : Context Q) (j : Ideal (𝓞 F)) (T Y Z L : ℝ) : ℂ :=
  ReflectedCoprimeTruncation.remainder F C.source j T Y Z L

end Context

def R (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  (C.pairSum fun p hp => C.coefficient p *
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        C.primitive p hp a * C.reflectedRemainder (p.1 * p.2)
          (Real.sqrt (C.dualScale e p / norm a)) (C.Y1 B e) (C.Z1 B e) C.L1) -
  (C.pairSum fun p hp => C.coefficient p *
    ∑ a ∈ C.originalRows B unit,
      C.primitive p hp a * C.originalRemainder ((c * C.d) * (p.1 * p.2))
        (Real.sqrt (C.M / norm a)) (C.Y2 B) (C.Z2 B) C.L2)

def sevenTermBlock (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  T C B unit - Tprime C B unit - E1 C B unit - E2 C B unit +
    E3 C B unit + E4 C B unit - E5 C B unit

def dyadicScales (C : Context Q) : Finset ℝ :=
  (Finset.range (Vendor.dyadicLength C.K)).image (fun i => (2 : ℝ) ^ i)

def unitBlock (C : Context Q) : ℂ := sevenTermBlock C 1 true

def cutoffRemainder (C : Context Q) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    primitiveMobiusTransformTail c C.d C.W C.M C.K p.1 p.2 (C.primitive p hp)

def totalRemainder (C : Context Q) : ℂ :=
  cutoffRemainder C + R C 1 true + ∑ B ∈ dyadicScales C, R C B

def sevenTermSum (C : Context Q) : ℂ :=
  unitBlock C + ∑ B ∈ dyadicScales C, sevenTermBlock C B

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end
