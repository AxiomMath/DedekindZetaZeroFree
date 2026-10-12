module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.AdelicRestrictedProductTopology
public import DedekindZetaZeroFree.Metaplectic.Torus.LocalCubicHeisenbergPairing

@[expose] public section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Ideles := KPAdelicCoverRestrictedProduct.Ideles F

abbrev D := Ideles F ⧸ CubicCharacters.cubes (Ideles F)

abbrev LocalD (v : KPHilbert.Place F) :=
  KPLocalTorus.CubeClasses (KPHilbert.Completion F v)ˣ

def localClass (v : KPHilbert.Place F) : (KPHilbert.Completion F v)ˣ →* LocalD F v :=
  QuotientGroup.mk' (CubicCharacters.cubes (KPHilbert.Completion F v)ˣ)

def U (v : KPHilbert.Place F) : Subgroup (LocalD F v) :=
  match v with
  | Sum.inl _ => ⊤
  | Sum.inr q => (KPHilbert.integerUnitInclusion F q).range.map (localClass F (Sum.inr q))

abbrev RestrictedClasses := RestrictedProduct (LocalD F)
  (fun v => (U F v : Set _)) Filter.cofinite

def ideleEval (v : KPHilbert.Place F) : Ideles F →* (KPHilbert.Completion F v)ˣ :=
  Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v)

theorem ideleClass_restricted (x : Ideles F) :
    ∀ᶠ v in Filter.cofinite, localClass F v (ideleEval F v x) ∈ U F v := by
  have hi : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∃ u : KPHilbert.LocalIntegerUnits F q,
        KPHilbert.integerUnitInclusion F q u = ideleEval F (Sum.inr q) x := by
    filter_upwards [(x.val.2).property, (x.inv.2).property] with q hq hqi
    letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
    letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    have mem (a : q.adicCompletion F) (ha : a ∈ q.adicCompletionIntegers F) :
        a ∈ (ValuativeRel.valuation (q.adicCompletion F)).integer := by
      rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff]
      exact (Valuation.vle_one_iff
        (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr ha
    let z := ideleEval F (Sum.inr q) x
    let u : KPHilbert.LocalIntegerUnits F q :=
      ⟨⟨(z : q.adicCompletion F), mem _ hq⟩,
       ⟨(z⁻¹ : (q.adicCompletion F)ˣ), mem _ hqi⟩,
       by apply Subtype.ext; exact z.val_inv,
       by apply Subtype.ext; exact z.inv_val⟩
    exact ⟨u, rfl⟩
  have hf : {q : HeightOneSpectrum (𝓞 F) | ¬ ∃ u : KPHilbert.LocalIntegerUnits F q,
      KPHilbert.integerUnitInclusion F q u = ideleEval F (Sum.inr q) x}.Finite :=
    Filter.mem_cofinite.mp hi
  filter_upwards [(hf.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)).compl_mem_cofinite] with v hv
  cases v with
  | inl w => exact Subgroup.mem_top _
  | inr q =>
    have hq : ∃ u : KPHilbert.LocalIntegerUnits F q,
        KPHilbert.integerUnitInclusion F q u = ideleEval F (Sum.inr q) x := by
      by_contra h
      exact hv ⟨q, h, rfl⟩
    obtain ⟨u, hu⟩ := hq
    exact ⟨_, ⟨u, rfl⟩, congrArg (localClass F (Sum.inr q)) hu⟩

def restrictedClassMap : Ideles F →* RestrictedClasses F where
  toFun x := ⟨fun v => localClass F v (ideleEval F v x), ideleClass_restricted F x⟩
  map_one' := by ext v; simp
  map_mul' x y := by
    ext v
    change localClass F v (ideleEval F v (x * y)) =
      localClass F v (ideleEval F v x) * localClass F v (ideleEval F v y)
    simp

theorem restrictedClassMap_kills_cubes :
    CubicCharacters.cubes (Ideles F) ≤ (restrictedClassMap F).ker := by
  rintro x ⟨y, rfl⟩
  change restrictedClassMap F (y ^ 3) = 1
  ext v
  change localClass F v (ideleEval F v (y ^ 3)) = 1
  rw [map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨ideleEval F v y, rfl⟩

def classComparison : D F →* RestrictedClasses F :=
  QuotientGroup.lift _ (restrictedClassMap F) (restrictedClassMap_kills_cubes F)

theorem localSymbol_congr (v : KPHilbert.Place F)
    (a b a' b' : (KPHilbert.Completion F v)ˣ)
    (ha : QuotientGroup.leftRel (CubicCharacters.cubes (KPHilbert.Completion F v)ˣ) a a')
    (hb : QuotientGroup.leftRel (CubicCharacters.cubes (KPHilbert.Completion F v)ˣ) b b') :
    KPHilbert.B3 F ζ hζ v a b = KPHilbert.B3 F ζ hζ v a' b' := by
  obtain ⟨t, ht⟩ := QuotientGroup.leftRel_apply.mp ha
  obtain ⟨u, hu⟩ := QuotientGroup.leftRel_apply.mp hb
  have ht' : a' = a * t ^ 3 := by
    change t ^ 3 = a⁻¹ * a' at ht
    rw [ht, mul_inv_cancel_left]
  have hu' : b' = b * u ^ 3 := by
    change u ^ 3 = b⁻¹ * b' at hu
    rw [hu, mul_inv_cancel_left]
  rw [ht', hu', (KPHilbert.B3_laws F ζ hζ v).1,
    (KPHilbert.B3_laws F ζ hζ v).2.1]
  rw [(KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 t (b * u ^ 3) |>.1,
    (KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 a u |>.2]
  simp

def localPairing (v : KPHilbert.Place F) (a b : LocalD F v) : rootsOfUnity 3 F :=
  Quotient.liftOn₂ a b (KPHilbert.B3 F ζ hζ v) (localSymbol_congr F ζ hζ v)

@[simp] theorem localPairing_representatives (v : KPHilbert.Place F)
    (a b : (KPHilbert.Completion F v)ˣ) :
    localPairing F ζ hζ v (localClass F v a) (localClass F v b) =
      KPHilbert.B3 F ζ hζ v a b := rfl

theorem tame_unit_isotropic (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (a b : LocalD F (Sum.inr q)) (ha : a ∈ U F (Sum.inr q))
    (hb : b ∈ U F (Sum.inr q)) :
    localPairing F ζ hζ (Sum.inr q) a b = 1 := by
  obtain ⟨a, ⟨u, rfl⟩, rfl⟩ := ha
  obtain ⟨b, ⟨w, rfl⟩, rfl⟩ := hb
  exact KPTameCompact.B3_units F q ζ hζ
    (fun h => hgood (Or.inr h)) u w

theorem pairing_finiteSupport (x y : RestrictedClasses F) :
    Function.HasFiniteMulSupport (fun v => localPairing F ζ hζ v (x v) (y v)) := by
  have hgood : ∀ᶠ v : KPHilbert.Place F in Filter.cofinite,
      ∀ q, v = Sum.inr q → ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
    have hf := (KPAdelicCoverRestrictedProduct.bad_finite F).image
      (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)
    filter_upwards [hf.compl_mem_cofinite] with v hv q hq
    intro hbad
    exact hv ⟨q, hbad, hq.symm⟩
  have heq : ∀ᶠ v in Filter.cofinite, localPairing F ζ hζ v (x v) (y v) = 1 := by
    filter_upwards [x.property, y.property, hgood] with v hx hy hv
    cases v with
    | inl w =>
      induction (x (Sum.inl w)) using QuotientGroup.induction_on with
      | H a =>
        induction (y (Sum.inl w)) using QuotientGroup.induction_on with
        | H b => simp [localPairing, KPHilbert.B3, KPHilbert.B6]
    | inr q => exact tame_unit_isotropic F ζ hζ q (hv q rfl) _ _ hx hy
  exact Filter.mem_cofinite.mp heq

def restrictedBeta (x y : RestrictedClasses F) : rootsOfUnity 3 F :=
  ∏ᶠ v, localPairing F ζ hζ v (x v) (y v)

def beta3 (x y : D F) : rootsOfUnity 3 F :=
  restrictedBeta F ζ hζ (classComparison F x) (classComparison F y)

private theorem localPairing_mul_right (v : KPHilbert.Place F) (x y z : LocalD F v) :
    localPairing F ζ hζ v x (y * z) =
      localPairing F ζ hζ v x y * localPairing F ζ hζ v x z := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      induction z using QuotientGroup.induction_on with
      | H z => exact (KPHilbert.B3_laws F ζ hζ v).2.1 x y z

def diagonalMatrix (y : Ideles F) : KPAdelicCoverRestrictedProduct.AdelicGL2 F where
  val := !![(y : KPAdelicCoverRestrictedProduct.Adeles F), 0; 0, 1]
  inv := !![((y⁻¹ : Ideles F) : KPAdelicCoverRestrictedProduct.Adeles F), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

def diagonalHom : Ideles F →* KPAdelicCoverRestrictedProduct.AdelicGL2 F where
  toFun := diagonalMatrix F
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalMatrix]
  map_mul' x y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two]

def diagonalPGL : Ideles F →* KPAdelicCoverRestrictedProduct.AdelicPGL2 F :=
  (QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).comp (diagonalHom F)

def torusPullback : Subgroup
    (KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ × Ideles F) :=
  MonoidHom.eqLocus
    ((KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).comp (MonoidHom.fst _ _))
    ((diagonalPGL F).comp (MonoidHom.snd _ _))

abbrev E := torusPullback F ζ hζ

def torusProjection : E F ζ hζ →* Ideles F :=
  (MonoidHom.snd _ _).comp (torusPullback F ζ hζ).subtype

theorem torusCentral_mem (z : rootsOfUnity 3 F) :
    (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ z, 1) ∈
      torusPullback F ζ hζ := by
  change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
    (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ z) = diagonalPGL F 1
  rw [map_one]
  have hz := KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ
  change KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ z ∈
    (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker
  rw [← hz]
  exact ⟨z, rfl⟩

def torusCentralInjection : rootsOfUnity 3 F →* E F ζ hζ where
  toFun z := ⟨(KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ z, 1),
    torusCentral_mem F ζ hζ z⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

abbrev ExteriorValuations (S : Finset (KPHilbert.Place F)) :=
  Multiplicative ({v : KPHilbert.Place F // v ∉ S} →₀ ZMod 3)

@[instance_reducible] def exteriorValuationsTopology (S : Finset (KPHilbert.Place F)) :
    TopologicalSpace (ExteriorValuations F S) := ⊥

attribute [local instance] exteriorValuationsTopology

abbrev LocalValuationClasses (v : KPHilbert.Place F) := LocalD F v ⧸ U F v
theorem unitValuation_congr (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (u : U F (Sum.inr q)) (a b : LocalD F (Sum.inr q))
    (hab : QuotientGroup.leftRel (U F (Sum.inr q)) a b) :
    localPairing F ζ hζ (Sum.inr q) u.val a =
      localPairing F ζ hζ (Sum.inr q) u.val b := by
  have hmul : a⁻¹ * b ∈ U F (Sum.inr q) := QuotientGroup.leftRel_apply.mp hab
  have hiso := tame_unit_isotropic F ζ hζ q hgood u.val _ u.property hmul
  have heq := localPairing_mul_right F ζ hζ (Sum.inr q) u.val a (a⁻¹ * b)
  simpa [hiso] using heq.symm

def unitValuationPairing (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (u : U F (Sum.inr q)) (a : LocalValuationClasses F (Sum.inr q)) : rootsOfUnity 3 F :=
  Quotient.liftOn a (fun b => localPairing F ζ hζ (Sum.inr q) u.val b)
    (unitValuation_congr F ζ hζ q hgood u)

end
end DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw
