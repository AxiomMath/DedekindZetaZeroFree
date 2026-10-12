module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellKernel

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneCenterInducedDiagonalComparison

open scoped NumberField Valued TensorProduct commutatorElement
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

abbrev CenterModule := FinitePolarization.inducedSpace T.C T.ω.toMonoidHom

def centerTorus (ε : Sign) : Representation ℂ H (CenterModule T) :=
  match ε with
  | .plus => inducedRepresentation T.C T.ω.toMonoidHom
  | .minus => (inducedRepresentation T.C T.ω.toMonoidHom).comp
      A.weyl.toMulEquiv.toMonoidHom

omit [DecidableEq D] in
 theorem scalar_one (z : ℂ) : inducingScalar A z 1 = 1 := by
  simp [inducingScalar, deltaHalf, normPower, localAbs_one]

omit [DecidableEq D] in
 theorem scalar_mul (z : ℂ) (b c : A.B) :
    inducingScalar A z (b * c) = inducingScalar A z b * inducingScalar A z c := by
  have hn (x y : (LocalField F q)ˣ) (s : ℂ) :
      normPower (LocalField F q) (x * y) s =
        normPower (LocalField F q) x s * normPower (LocalField F q) y s := by
    rw [normPower, localAbs_mul, Real.log_mul
      (ne_of_gt (localAbs_pos _ x)) (ne_of_gt (localAbs_pos _ y)), Complex.ofReal_add,
      mul_add, Complex.exp_add]
    rfl
  simp only [inducingScalar, deltaHalf, map_mul, hn]
  ring

omit [DecidableEq D] in

def centerInducingAction (ε : Sign) (z : ℂ) :
    Representation ℂ A.B (CenterModule T) where
  toFun b := inducingScalar A z b • (centerTorus F ζ hζ q T A ε) (A.retract b)
  map_one' := by simp [scalar_one, map_one]
  map_mul' := by
    intro b c
    simp only [scalar_mul, map_mul]
    ext v
    simp [Module.End.mul_apply, smul_smul, mul_comm]

omit [DecidableEq D] in

def centerSectionSpace (ε : Sign) (z : ℂ) :
    Submodule ℂ (Cover F ζ hζ q → CenterModule T) where
  carrier := {f | (∀ (b : A.B) (g : Cover F ζ hζ q),
    f ((b : Cover F ζ hζ q) * g) = centerInducingAction F ζ hζ q T A ε z b (f g)) ∧
    SmoothVector vectorRightTranslation f}
  zero_mem' := by
    constructor
    · intros; simp
    · exact ⟨⊤, by intros; simp⟩
  add_mem' := by
    intro f g hf hg
    constructor
    · intro b x
      change f _ + g _ = centerInducingAction F ζ hζ q T A ε z b (f x + g x)
      rw [hf.1 b x, hg.1 b x, map_add]
    · obtain ⟨J, hJ⟩ := hf.2
      obtain ⟨L, hL⟩ := hg.2
      refine ⟨J ⊓ L, ?_⟩
      intro j hj
      simp [hJ j hj.1, hL j hj.2]
  smul_mem' := by
    intro c f hf
    constructor
    · intro b x
      change c • f _ = centerInducingAction F ζ hζ q T A ε z b (c • f x)
      rw [hf.1 b x, map_smul]
    · obtain ⟨J, hJ⟩ := hf.2
      exact ⟨J, fun j hj => by simp [hJ j hj]⟩

omit [DecidableEq D] in

def centerPrincipalSeries (ε : Sign) (z : ℂ) :
    Representation ℂ (Cover F ζ hζ q) (centerSectionSpace F ζ hζ q T A ε z) :=
  vectorRightTranslation.subrepresentation (centerSectionSpace F ζ hζ q T A ε z)
    (by
      intro g f hf
      constructor
      · intro b x
        change f (((b : Cover F ζ hζ q) * x) * g) =
          centerInducingAction F ζ hζ q T A ε z b (f (x * g))
        rw [mul_assoc, hf.1 b (x * g)]
      · have hs : f ∈ smoothSubmodule vectorRightTranslation :=
          (mem_smoothSubmodule _ f).mpr hf.2
        exact (mem_smoothSubmodule _ _).mp (smoothSubmodule_stable _ g hs))

omit [DecidableEq D] in

def centerCompactPicture (I : IwasawaData A) (ε : Sign) :
    Submodule ℂ (I.compact.toOpenSubgroup → CenterModule T) where
  carrier := {φ | (∀ (b : A.B) (k k' : I.compact.toOpenSubgroup),
    (k' : Cover F ζ hζ q) = (b : Cover F ζ hζ q) * (k : Cover F ζ hζ q) →
    φ k' = centerInducingAction F ζ hζ q T A ε 0 b (φ k)) ∧
    SmoothVector (vectorRightTranslation (G := I.compact.toOpenSubgroup)) φ}
  zero_mem' := by
    constructor
    · intros; simp
    · exact ⟨⊤, by intros; simp⟩
  add_mem' := by
    intro f g hf hg
    constructor
    · intro b k k' he
      change f k' + g k' = centerInducingAction F ζ hζ q T A ε 0 b (f k + g k)
      rw [hf.1 b k k' he, hg.1 b k k' he, map_add]
    · obtain ⟨J, hJ⟩ := hf.2
      obtain ⟨L, hL⟩ := hg.2
      refine ⟨J ⊓ L, ?_⟩
      intro j hj
      simp [hJ j hj.1, hL j hj.2]
  smul_mem' := by
    intro c f hf
    constructor
    · intro b k k' he
      change c • f k' = centerInducingAction F ζ hζ q T A ε 0 b (c • f k)
      rw [hf.1 b k k' he, map_smul]
    · obtain ⟨J, hJ⟩ := hf.2
      exact ⟨J, fun j hj => by simp [hJ j hj]⟩

omit [DecidableEq D] in

def centerCompactTrivialization (I : IwasawaData A) (ε : Sign) (z : ℂ) :
    centerCompactPicture F ζ hζ q T A I ε ≃ₗ[ℂ]
      centerSectionSpace F ζ hζ q T A ε z where
  toFun φ := ⟨fun g => centerInducingAction F ζ hζ q T A ε z (I.borelPart g)
    (φ.val (I.compactPart g)), by
      have hagree (b : A.B) (hb : (b : Cover F ζ hζ q) ∈ I.compact.toOpenSubgroup) :
          centerInducingAction F ζ hζ q T A ε z b =
            centerInducingAction F ζ hζ q T A ε 0 b := by
        ext v
        simp [centerInducingAction, inducingScalar, deltaHalf, normPower,
          I.intersection_norm b hb]
      exact (KPLocalPrincipalSeriesRaw.fixed_iwasawa_laws A.B I.compact.toOpenSubgroup
        (centerInducingAction F ζ hζ q T A ε 0) (centerInducingAction F ζ hζ q T A ε z)
        I.borelPart I.compactPart I.decomposition I.borelPart_compact
        I.compactPart_compact hagree).2.2.2.1 φ.val φ.property⟩
  invFun f := ⟨fun k => f.val (k : Cover F ζ hζ q), by
      have hagree (b : A.B) (hb : (b : Cover F ζ hζ q) ∈ I.compact.toOpenSubgroup) :
          centerInducingAction F ζ hζ q T A ε z b =
            centerInducingAction F ζ hζ q T A ε 0 b := by
        ext v
        simp [centerInducingAction, inducingScalar, deltaHalf, normPower,
          I.intersection_norm b hb]
      exact (KPLocalPrincipalSeriesRaw.fixed_iwasawa_laws A.B I.compact.toOpenSubgroup
        (centerInducingAction F ζ hζ q T A ε 0) (centerInducingAction F ζ hζ q T A ε z)
        I.borelPart I.compactPart I.decomposition I.borelPart_compact
        I.compactPart_compact hagree).2.2.2.2.1 f.val f.property⟩
  map_add' := by intros; apply Subtype.ext; funext g; simp
  map_smul' := by intros; apply Subtype.ext; funext g; simp
  left_inv := by
    intro φ
    apply Subtype.ext
    funext k
    simp [I.borelPart_compact, I.compactPart_compact]
  right_inv := by
    intro f
    apply Subtype.ext
    funext g
    exact (f.property.1 (I.borelPart g) (I.compactPart g)).symm.trans
      (congrArg f.val (I.decomposition g).symm)

omit [DecidableEq D] in

def centerCompactLevel (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel (Cover F ζ hζ q)) :
    Submodule ℂ (centerCompactPicture F ζ hζ q T A I ε) where
  carrier := {φ | ∀ (j : J.toOpenSubgroup) (k k' : I.compact.toOpenSubgroup),
    (k' : Cover F ζ hζ q) = (k : Cover F ζ hζ q) * (j : Cover F ζ hζ q) →
    φ.val k' = φ.val k}
  zero_mem' := by
    change ∀ j k k', _ → _
    intros; rfl
  add_mem' := by
    intro f g hf hg j k k' he
    change f.val k' + g.val k' = f.val k + g.val k
    rw [hf j k k' he, hg j k k' he]
  smul_mem' := by
    intro c f hf j k k' he
    change c • f.val k' = c • f.val k
    rw [hf j k k' he]

omit [DecidableEq D] in
abbrev CenterLevelLaurentOperator (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (ε : Sign) :=
  ℤ →₀ (centerCompactLevel F ζ hζ q T A I (sourceSign ε) J →ₗ[ℂ]
    centerCompactLevel F ζ hζ q T A I (targetSign ε) J)

omit [DecidableEq D] in
def centerEvaluate (I : IwasawaData A) (J : CompactOpenLevel (Cover F ζ hζ q))
    (ε : Sign) (p : CenterLevelLaurentOperator F ζ hζ q T A I J ε) (u : ℂˣ) :
    centerCompactLevel F ζ hζ q T A I (sourceSign ε) J →ₗ[ℂ]
      centerCompactLevel F ζ hζ q T A I (targetSign ε) J :=
  p.sum (fun n M => ((u : ℂ) ^ n) • M)

variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

omit [DecidableEq D] in

def centerIntegralCoordinate (μ : Measure (LocalField F q)) (ε : Sign) (z : ℂ)
    (f : centerSectionSpace F ζ hζ q T A (sourceSign ε) (sourceParameter ε z))
    (g : Cover F ζ hζ q) (h : H) : ℂ :=
  ∫ x : LocalField F q,
    (f.val (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g)).val h ∂μ

omit [DecidableEq D] in

def IsCenterLevelNumerator (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (μ : Measure (LocalField F q))
    (ε : Sign) (p : CenterLevelLaurentOperator F ζ hζ q T A I J ε) : Prop :=
  ∀ z : ℂ, convergenceHalfPlane ε z →
    ∀ (φ : centerCompactLevel F ζ hζ q T A I (sourceSign ε) J)
      (k : I.compact.toOpenSubgroup) (h : H),
    ((centerEvaluate F ζ hζ q T A I J ε p (evaluationUnit (LocalField F q) ε z) φ :
      centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h =
    denominator (LocalField F q) ε z *
      centerIntegralCoordinate F ζ hζ q T A μ ε z
        (centerCompactTrivialization F ζ hζ q T A I (sourceSign ε) (sourceParameter ε z)
          (φ : centerCompactPicture F ζ hζ q T A I (sourceSign ε))) (k : Cover F ζ hζ q) h

omit [DecidableEq D] in
def centerContinuedLevel (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (ε : Sign)
    (p : CenterLevelLaurentOperator F ζ hζ q T A I J ε) (z : ℂ) :
    centerCompactLevel F ζ hζ q T A I (sourceSign ε) J →ₗ[ℂ]
      centerCompactLevel F ζ hζ q T A I (targetSign ε) J :=
  (denominator (LocalField F q) ε z)⁻¹ •
    centerEvaluate F ζ hζ q T A I J ε p (evaluationUnit (LocalField F q) ε z)

omit [DecidableEq D] in

structure TauStandardFamily (I : IwasawaData A) (μ : Measure (LocalField F q)) where
  op : ∀ (ε : Sign) (z : ℂ),
    sectionSpace A P (sourceSign ε) (sourceParameter ε z) →ₗ[ℂ]
      sectionSpace A P (targetSign ε) (targetParameter ε z)
  intertwining : ∀ ε z, denominator (LocalField F q) ε z ≠ 0 →
    ∀ (g : Cover F ζ hζ q) f,
      op ε z (principalSeries A P (sourceSign ε) (sourceParameter ε z) g f) =
        principalSeries A P (targetSign ε) (targetParameter ε z) g (op ε z f)
  numerators : ∀ (J : CompactOpenLevel (Cover F ζ hζ q)),
    (J.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup →
    ∀ ε, ∃! p : LevelLaurentOperator (LocalField F q) A P I J ε,
      IsLevelNumerator (LocalField F q) A P I J μ ε p
  integral_eq : ∀ ε z, convergenceHalfPlane ε z →
    ∀ (f : sectionSpace A P (sourceSign ε) (sourceParameter ε z))
      (g : Cover F ζ hζ q) (h : H),
      Integrable (fun x : LocalField F q =>
        (f.val (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g)).val h) μ ∧
      ((op ε z f).val g).val h = ∫ x : LocalField F q,
        (f.val (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g)).val h ∂μ
  shell_eq : ∀ (J : CompactOpenLevel (Cover F ζ hζ q)) ε
    (p : LevelLaurentOperator (LocalField F q) A P I J ε),
    IsLevelNumerator (LocalField F q) A P I J μ ε p →
    ∀ z, denominator (LocalField F q) ε z ≠ 0 →
    ∀ φ : compactLevel A P I (sourceSign ε) J,
      op ε z (compactTrivialization A P I (sourceSign ε) (sourceParameter ε z)
        (φ : compactPicture A P I (sourceSign ε))) =
      compactTrivialization A P I (targetSign ε) (targetParameter ε z)
        (continuedLevel (LocalField F q) A P I J ε p z φ : compactPicture A P I (targetSign ε))

omit [DecidableEq D] in

structure CenterStandardFamily (I : IwasawaData A) (μ : Measure (LocalField F q)) where
  op : ∀ (ε : Sign) (z : ℂ),
    centerSectionSpace F ζ hζ q T A (sourceSign ε) (sourceParameter ε z) →ₗ[ℂ]
      centerSectionSpace F ζ hζ q T A (targetSign ε) (targetParameter ε z)
  intertwining : ∀ ε z, denominator (LocalField F q) ε z ≠ 0 →
    ∀ (g : Cover F ζ hζ q) f,
      op ε z (centerPrincipalSeries F ζ hζ q T A (sourceSign ε) (sourceParameter ε z) g f) =
        centerPrincipalSeries F ζ hζ q T A (targetSign ε) (targetParameter ε z) g (op ε z f)
  numerators : ∀ (J : CompactOpenLevel (Cover F ζ hζ q)),
    (J.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup →
    ∀ ε, ∃! p : CenterLevelLaurentOperator F ζ hζ q T A I J ε,
      IsCenterLevelNumerator F ζ hζ q T A I J μ ε p
  integral_eq : ∀ ε z, convergenceHalfPlane ε z →
    ∀ (f : centerSectionSpace F ζ hζ q T A (sourceSign ε) (sourceParameter ε z))
      (g : Cover F ζ hζ q) (h : H),
      Integrable (fun x : LocalField F q =>
        (f.val (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g)).val h) μ ∧
      ((op ε z f).val g).val h = centerIntegralCoordinate F ζ hζ q T A μ ε z f g h
  shell_eq : ∀ (J : CompactOpenLevel (Cover F ζ hζ q)) ε
    (p : CenterLevelLaurentOperator F ζ hζ q T A I J ε),
    IsCenterLevelNumerator F ζ hζ q T A I J μ ε p →
    ∀ z, denominator (LocalField F q) ε z ≠ 0 →
    ∀ φ : centerCompactLevel F ζ hζ q T A I (sourceSign ε) J,
      op ε z (centerCompactTrivialization F ζ hζ q T A I (sourceSign ε) (sourceParameter ε z)
        (φ : centerCompactPicture F ζ hζ q T A I (sourceSign ε))) =
      centerCompactTrivialization F ζ hζ q T A I (targetSign ε) (targetParameter ε z)
        (centerContinuedLevel F ζ hζ q T A I J ε p z φ :
          centerCompactPicture F ζ hζ q T A I (targetSign ε))

abbrev Multiplicity := Module.Dual ℂ (InducedModule P)

def centerMatrixCoefficient (v : InducedModule P) (ℓ : Multiplicity T P) : CenterModule T :=
  ⟨fun h => ℓ (tau P h v), by
    intro c h
    change ℓ (tau P ((c : H) * h) v) = (T.ω c : ℂ) * ℓ (tau P h v)
    rw [map_mul]
    change ℓ (tau P (c : H) (tau P h v)) = _
    rw [tau_hasCentralCharacter T P c, map_smul]
    rfl⟩

def centerCoefficientMap : InducedModule P ⊗[ℂ] Multiplicity T P →ₗ[ℂ] CenterModule T :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (centerMatrixCoefficient T P)
    (by intro v w ℓ; apply Subtype.ext; funext h; simp [centerMatrixCoefficient])
    (by intro c v ℓ; apply Subtype.ext; funext h; simp [centerMatrixCoefficient])
    (by intro v ℓ m; apply Subtype.ext; funext h; rfl)
    (by intro c v ℓ; apply Subtype.ext; funext h; rfl))

@[simp] theorem centerCoefficientMap_tmul (v : InducedModule P) (ℓ : Multiplicity T P) (h : H) :
    (centerCoefficientMap T P (v ⊗ₜ[ℂ] ℓ)).val h = ℓ (tau P h v) := rfl

theorem centerCoefficientMap_natural (ε : Sign) (h : H)
    (v : InducedModule P ⊗[ℂ] Multiplicity T P) :
    centerTorus F ζ hζ q T A ε h (centerCoefficientMap T P v) =
      centerCoefficientMap T P (TensorProduct.map
        (match ε with | .plus => tau P h | .minus => weylConjugate P A.weyl h)
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul v ℓ =>
    apply Subtype.ext
    funext x
    cases ε <;>
      change ℓ (tau P (x * _) v) = ℓ (tau P x (tau P _ v)) <;>
      rw [map_mul] <;> rfl
  | add v w hv hw => simp only [map_add, hv, hw]

omit [DecidableEq D] in
def tauEvaluation (ε : Sign) (z : ℂ) (g : Cover F ζ hζ q) :
    sectionSpace A P ε z →ₗ[ℂ] InducedModule P where
  toFun f := f.val g
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem tauSection_has_compact_level (I : IwasawaData A) (ε : Sign) (z : ℂ)
    (f : sectionSpace A P ε z) :
    ∃ (J : CompactOpenLevel (Cover F ζ hζ q)),
      (J.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup ∧
      ∃ φ : compactLevel A P I ε J,
        compactTrivialization A P I ε z (φ : compactPicture A P I ε) = f := by
  obtain ⟨U, hU⟩ := f.property.2
  let J : CompactOpenLevel (Cover F ζ hζ q) :=
    ⟨I.compact.toOpenSubgroup ⊓ U, I.compact.isCompact.inter_right U.isClosed⟩
  have hJ : (J.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤
      I.compact.toOpenSubgroup := fun _ h => h.1
  let φ := (compactTrivialization A P I ε z).symm f
  have hφ : φ ∈ compactLevel A P I ε J := by
    apply (compact_level_identification A P I ε J hJ z φ).mpr
    intro j
    change principalSeries A P ε z (j : Cover F ζ hζ q)
      (compactTrivialization A P I ε z φ) = compactTrivialization A P I ε z φ
    simp only [φ, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact hU (j : Cover F ζ hζ q) j.property.2
  exact ⟨J, hJ, ⟨φ, hφ⟩, (compactTrivialization A P I ε z).apply_symm_apply f⟩

theorem centerSection_has_compact_level (I : IwasawaData A) (ε : Sign) (z : ℂ)
    (f : centerSectionSpace F ζ hζ q T A ε z) :
    ∃ (J : CompactOpenLevel (Cover F ζ hζ q)),
      (J.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup ∧
      ∃ φ : centerCompactLevel F ζ hζ q T A I ε J,
        centerCompactTrivialization F ζ hζ q T A I ε z
          (φ : centerCompactPicture F ζ hζ q T A I ε) = f := by
  obtain ⟨U, hU⟩ := f.property.2
  let J : CompactOpenLevel (Cover F ζ hζ q) :=
    ⟨I.compact.toOpenSubgroup ⊓ U, I.compact.isCompact.inter_right U.isClosed⟩
  let φ := (centerCompactTrivialization F ζ hζ q T A I ε z).symm f
  have hφ : φ ∈ centerCompactLevel F ζ hζ q T A I ε J := by
    intro j k k' he
    change f.val (k' : Cover F ζ hζ q) = f.val (k : Cover F ζ hζ q)
    rw [he]
    exact congrFun (hU (j : Cover F ζ hζ q) j.property.2) (k : Cover F ζ hζ q)
  exact ⟨J, fun _ h => h.1, ⟨φ, hφ⟩,
    (centerCompactTrivialization F ζ hζ q T A I ε z).apply_symm_apply f⟩

private theorem isotropic_square {D : Type*} [CommGroup D] [Finite D]
    (b : D →* (D →* rootsOfUnity 3 ℂ))
    (halt : ∀ d : D, b d d = 1) (hperfect : Function.Bijective b)
    (L : Subgroup D) (hL : FinitePolarization.IsMaximalIsotropic b L) :
    Nat.card D = L.index ^ 2 := by
  classical
  have hexp : ∀ x : D, x ^ 3 = 1 := by
    intro x
    apply hperfect.1
    apply MonoidHom.ext
    intro y
    change b (x ^ 3) y = b 1 y
    simp only [map_pow, map_one, MonoidHom.pow_apply, MonoidHom.one_apply]
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp (b x y).property
  let p : D →* (D →* ℂˣ) := (MonoidHom.compHom (rootsOfUnity 3 ℂ).subtype).comp b
  have hp : Function.Bijective p := by
    constructor
    · intro x y h
      apply hperfect.1
      apply MonoidHom.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun f : D →* ℂˣ => f z) h
    · intro f
      let f' : D →* rootsOfUnity 3 ℂ := f.codRestrict _ (fun x => by
        rw [mem_rootsOfUnity, ← map_pow, hexp, map_one])
      obtain ⟨x, hx⟩ := hperfect.2 f'
      refine ⟨x, ?_⟩
      apply MonoidHom.ext
      intro z
      exact congrArg (fun g : D →* rootsOfUnity 3 ℂ => (g z : ℂˣ)) hx
  have horth := FinitePolarization.orthogonal_eq_of_isMaximalIsotropic b halt hL
  let k := (MonoidHom.domRestrictHom L ℂˣ).ker
  have hmem : ∀ x : D, p x ∈ k ↔ x ∈ L := by
    intro x
    change (MonoidHom.domRestrictHom L ℂˣ) (p x) = 1 ↔ x ∈ L
    have hr : x ∈ L ↔ ∀ l : L, b (l : D) x = 1 := by
      rw [← FinitePolarization.mem_orthogonal, horth]
    rw [hr]
    constructor
    · intro hx l
      have h := congrArg (fun f : L →* ℂˣ => f l) hx
      have h' : b x l = 1 := Subtype.ext h
      rw [FinitePolarization.pairing_swap_inv b halt, h', inv_one]
    · intro hx
      apply MonoidHom.ext
      intro l
      change (b x l : ℂˣ) = 1
      rw [FinitePolarization.pairing_swap_inv b halt, hx, inv_one]
      rfl
  let f : L → k := fun x => ⟨p x, (hmem x).mpr x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact hp.1 (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx⟩ := hp.2 y
      have hxL : x ∈ L := (hmem x).mp (hx ▸ y.property)
      exact ⟨⟨x, hxL⟩, Subtype.ext hx⟩
  have hc : Nat.card L = L.index := by
    rw [Nat.card_congr (Equiv.ofBijective f hf)]
    exact (CommGroup.card_domRestrictHom_ker ℂ L).trans L.index_eq_card.symm
  rw [← L.card_mul_index, hc, pow_two]

 def displacement (rep : D → H) (hrep : ∀ d, T.π (rep d) = d) (x : H) : T.C :=
  ⟨x * (rep (T.π x))⁻¹, by
    rw [← T.quotient_kernel]
    change T.π (x * (rep (T.π x))⁻¹) = 1
    simp [hrep]⟩

omit [DecidableEq D] in

def centerCoordinates (rep : D → H) (hrep : ∀ d, T.π (rep d) = d) :
    CenterModule T ≃ₗ[ℂ] (D → ℂ) where
  toFun v d := v.val (rep d)
  invFun v := ⟨fun x => (T.ω (displacement T rep hrep x) : ℂ) * v (T.π x), by
    intro c x
    have hc : T.π (c : H) = 1 := by
      have : (c : H) ∈ T.π.ker := by rw [T.quotient_kernel]; exact c.property
      exact this
    have hcx : T.π ((c : H) * x) = T.π x := by simp [hc]
    have he : displacement T rep hrep ((c : H) * x) = c * displacement T rep hrep x := by
      apply Subtype.ext
      simp only [displacement, hcx, Subgroup.coe_mul]
      exact mul_assoc _ _ _
    simp only [he, hcx, map_mul, Units.val_mul]
    exact mul_assoc _ _ _⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := by
    intro v
    apply Subtype.ext
    funext x
    have hx : (displacement T rep hrep x : H) * rep (T.π x) = x := by
      dsimp [displacement]; simp
    exact (v.property (displacement T rep hrep x) (rep (T.π x))).symm.trans (by rw [hx])
  right_inv := by
    intro v
    funext d
    have he : displacement T rep hrep (rep d) = 1 := by
      apply Subtype.ext
      simp [displacement, hrep]
    change (T.ω (displacement T rep hrep (rep d)) : ℂ) * v (T.π (rep d)) = v d
    rw [he, map_one, hrep]
    simp

theorem center_quotient_dimension :
    Module.finrank ℂ (CenterModule T) = Nat.card D ∧
    Nat.card D = Module.finrank ℂ (InducedModule P) ^ 2 := by
  classical
  let rep := Function.surjInv T.quotient_surjective
  have hrep : ∀ d, T.π (rep d) = d := Function.surjInv_eq T.quotient_surjective
  constructor
  · rw [(centerCoordinates T rep hrep).finrank_eq]
    letI := Fintype.ofFinite D
    simp [Module.finrank_pi, Nat.card_eq_fintype_card]
  · rw [tau_finrank_eq_index T P, P.L.index_comap_of_surjective T.quotient_surjective]
    exact isotropic_square T.pairing T.alternating T.perfect P.L P.maximal

theorem centerCoefficientMap_conjugate (a : H)
    (t : InducedModule P ⊗[ℂ] Multiplicity T P) :
    ∃ u : InducedModule P ⊗[ℂ] Multiplicity T P, ∀ h : H,
      (centerCoefficientMap T P u).val h =
        ((T.pairing (T.π a) (T.π h) : ℂˣ) : ℂ) * (centerCoefficientMap T P t).val h := by
  let u := TensorProduct.map (tau P a⁻¹) (tau P a).dualMap t
  refine ⟨u, ?_⟩
  intro h
  have hu : (centerCoefficientMap T P u).val h =
      (centerCoefficientMap T P t).val (a * h * a⁻¹) := by
    induction t using TensorProduct.induction_on with
    | zero => simp [u]
    | tmul v ℓ =>
      change ℓ (tau P a (tau P h (tau P a⁻¹ v))) = ℓ (tau P (a * h * a⁻¹) v)
      rw [map_mul, map_mul]; rfl
    | add t s ht hs =>
      change (centerCoefficientMap T P (TensorProduct.map _ _ (t + s))).val h = _
      simpa only [map_add, Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) ht hs
  rw [hu]
  have he : a * h * a⁻¹ = ⁅a, h⁆ * h := by
    simp [commutatorElement_def, mul_assoc]
  rw [he, (centerCoefficientMap T P t).property ⟨⁅a, h⁆, T.commutator_mem a h⟩ h]
  change (T.ω ⟨⁅a, h⁆, T.commutator_mem a h⟩ : ℂ) * _ = _
  rw [T.commutator_pairing a h]

theorem centerCoefficientMap_surjective : Function.Surjective (centerCoefficientMap T P) := by
  classical
  letI := Fintype.ofFinite D
  letI := tau_moduleFinite T P
  letI : (tau P).IsIrreducible := tau_irreducible T P
  letI : Nontrivial (tau P).asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) (tau P).asModule
  letI : Nontrivial (InducedModule P) :=
    (tau P).asModuleEquiv.toEquiv.symm.nontrivial
  let rep := Function.surjInv T.quotient_surjective
  have hrep : ∀ d, T.π (rep d) = d := Function.surjInv_eq T.quotient_surjective
  let e := centerCoordinates T rep hrep
  let S := (e.toLinearMap.comp (centerCoefficientMap T P)).range
  have hsep : ∀ i j : D, i ≠ j → ∃ m : D → ℂ,
      m i ≠ m j ∧ ∀ f ∈ S, (fun d => m d * f d) ∈ S := by
    intro i j hij
    have hfun : ∃ a : D, T.pairing a i ≠ T.pairing a j := by
      by_contra! he
      apply hij
      apply T.perfect.1
      apply MonoidHom.ext
      intro a
      rw [FinitePolarization.pairing_swap_inv T.pairing T.alternating a i,
        FinitePolarization.pairing_swap_inv T.pairing T.alternating a j, he a]
    obtain ⟨d, hd⟩ := hfun
    obtain ⟨a, ha⟩ := T.quotient_surjective d
    refine ⟨fun i => ((T.pairing d i : ℂˣ) : ℂ), ?_, ?_⟩
    · exact fun h => hd (Subtype.ext (Units.ext h))
    · intro f hf
      obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hf
      obtain ⟨u, hu⟩ := centerCoefficientMap_conjugate T P a t
      apply LinearMap.mem_range.mpr
      refine ⟨u, ?_⟩
      funext i
      exact (hu (rep i)).trans (by rw [ha, hrep]; rfl)
  have hsingle : ∀ i : D, Pi.single i (1 : ℂ) ∈ S := by
    intro i
    obtain ⟨v, hv⟩ := exists_ne (0 : InducedModule P)
    have hv' : tau P (rep i) v ≠ 0 := by
      intro h
      apply hv
      have hh := congrArg (tau P (rep i)⁻¹) h
      simpa [← Module.End.mul_apply, ← map_mul] using hh
    obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hv'
    let f := e (centerCoefficientMap T P (v ⊗ₜ[ℂ] ℓ))
    have hf : f ∈ S := LinearMap.mem_range.mpr ⟨v ⊗ₜ[ℂ] ℓ, rfl⟩
    have hfi : f i = 1 := hℓ
    simpa only [hfi] using diagonal_isolation S hsep f hf i
  have hS : S = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro f
    have heq : f = ∑ i : D, Pi.single i (f i) := by
      funext i
      simp [Fintype.sum_pi_single]
    rw [heq]
    apply S.sum_mem
    intro i _
    rw [show Pi.single i (f i) = f i • Pi.single i (1 : ℂ) by
      rw [← Pi.single_smul]; simp]
    exact S.smul_mem _ (hsingle i)
  intro v
  have hv : e v ∈ S := by rw [hS]; trivial
  obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hv
  exact ⟨t, e.injective ht⟩

set_option backward.isDefEq.respectTransparency false in

theorem centerCoefficientMap_bijective : Function.Bijective (centerCoefficientMap T P) := by
  classical
  letI := Fintype.ofFinite D
  let rep := Function.surjInv T.quotient_surjective
  have hrep : ∀ d, T.π (rep d) = d := Function.surjInv_eq T.quotient_surjective
  letI := Module.Finite.of_injective (centerCoordinates T rep hrep).toLinearMap
    (centerCoordinates T rep hrep).injective
  letI := tau_moduleFinite T P
  have hd : Module.finrank ℂ (InducedModule P ⊗[ℂ] Multiplicity T P) =
      Module.finrank ℂ (CenterModule T) := by
    rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq,
      (center_quotient_dimension T P).1, (center_quotient_dimension T P).2, pow_two]
  have hi : Function.Injective (centerCoefficientMap T P) := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℂ) (V := InducedModule P ⊗[ℂ] Multiplicity T P)
      (V₂ := CenterModule T) (f := centerCoefficientMap T P) hd).mpr
    exact centerCoefficientMap_surjective T P
  exact ⟨hi, centerCoefficientMap_surjective T P⟩

def centerCoefficientEquiv : CenterModule T ≃ₗ[ℂ]
    (InducedModule P ⊗[ℂ] Multiplicity T P) :=
  (LinearEquiv.ofBijective (centerCoefficientMap T P) (centerCoefficientMap_bijective T P)).symm

theorem centerCoefficientEquiv_natural (ε : Sign) (h : H) (v : CenterModule T) :
    centerCoefficientEquiv T P (centerTorus F ζ hζ q T A ε h v) =
      TensorProduct.map
        (match ε with | .plus => tau P h | .minus => weylConjugate P A.weyl h)
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P)
        (centerCoefficientEquiv T P v) := by
  apply (centerCoefficientMap_bijective T P).1
  rw [← centerCoefficientMap_natural]
  simp [centerCoefficientEquiv, LinearEquiv.ofBijective_apply]

set_option maxHeartbeats 800000 in

def centerTensorSection (ε : Sign) (z : ℂ) (f : sectionSpace A P ε z)
    (ℓ : Multiplicity T P) : centerSectionSpace F ζ hζ q T A ε z :=
  ⟨fun g => centerCoefficientMap T P (f.val g ⊗ₜ[ℂ] ℓ), by
    constructor
    · intro b g
      change centerCoefficientMap T P (f.val ((b : Cover F ζ hζ q) * g) ⊗ₜ[ℂ] ℓ) = _
      rw [f.property.1]
      have hn := centerCoefficientMap_natural F ζ hζ q T A P ε (A.retract b)
        (f.val g ⊗ₜ[ℂ] ℓ)
      rw [TensorProduct.map_tmul, LinearMap.id_apply] at hn
      cases ε <;>
        change centerCoefficientMap T P ((inducingScalar A z b • _) ⊗ₜ[ℂ] ℓ) =
          inducingScalar A z b • _ <;>
        rw [← TensorProduct.smul_tmul' (R := ℂ) (M := InducedModule P), map_smul]
      all_goals exact congrArg (inducingScalar A z b • ·) hn.symm
    · obtain ⟨U, hU⟩ := f.property.2
      refine ⟨U, ?_⟩
      intro u hu
      funext g
      change centerCoefficientMap T P (f.val (g * u) ⊗ₜ[ℂ] ℓ) =
        centerCoefficientMap T P (f.val g ⊗ₜ[ℂ] ℓ)
      rw [show f.val (g * u) = f.val g from congrFun (hU u hu) g]⟩

def centerSectionTensorMap (ε : Sign) (z : ℂ) :
    sectionSpace A P ε z ⊗[ℂ] Multiplicity T P →ₗ[ℂ]
      centerSectionSpace F ζ hζ q T A ε z :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (centerTensorSection F ζ hζ q T A P ε z)
    (by intro f g ℓ; apply Subtype.ext; funext x
        change centerCoefficientMap T P ((f.val x + g.val x) ⊗ₜ[ℂ] ℓ) = _
        rw [TensorProduct.add_tmul, map_add]; rfl)
    (by intro c f ℓ; apply Subtype.ext; funext x
        change centerCoefficientMap T P ((c • f.val x) ⊗ₜ[ℂ] ℓ) = _
        rw [← TensorProduct.smul_tmul', map_smul]; rfl)
    (by intro f ℓ m; apply Subtype.ext; funext x
        change centerCoefficientMap T P (f.val x ⊗ₜ[ℂ] (ℓ + m)) = _
        rw [TensorProduct.tmul_add, map_add]; rfl)
    (by intro c f ℓ; apply Subtype.ext; funext x
        change centerCoefficientMap T P (f.val x ⊗ₜ[ℂ] (c • ℓ)) = _
        rw [TensorProduct.tmul_smul, map_smul]; rfl))

@[simp] theorem centerSectionTensorMap_tmul (ε : Sign) (z : ℂ)
    (f : sectionSpace A P ε z) (ℓ : Multiplicity T P) (g : Cover F ζ hζ q) :
    (centerSectionTensorMap F ζ hζ q T A P ε z (f ⊗ₜ[ℂ] ℓ)).val g =
      centerCoefficientMap T P (f.val g ⊗ₜ[ℂ] ℓ) := rfl

theorem centerSectionTensorMap_value (ε : Sign) (z : ℂ)
    (t : sectionSpace A P ε z ⊗[ℂ] Multiplicity T P) (g : Cover F ζ hζ q) :
    (centerSectionTensorMap F ζ hζ q T A P ε z t).val g =
      centerCoefficientMap T P (TensorProduct.map (tauEvaluation F ζ hζ q T A P ε z g)
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f ℓ => rfl
  | add t u ht hu =>
    change ((centerSectionTensorMap F ζ hζ q T A P ε z) (t + u)).val g = _
    simpa only [map_add, Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) ht hu

theorem centerSectionTensorMap_natural (ε : Sign) (z : ℂ)
    (g : Cover F ζ hζ q) (t : sectionSpace A P ε z ⊗[ℂ] Multiplicity T P) :
    centerPrincipalSeries F ζ hζ q T A ε z g
        (centerSectionTensorMap F ζ hζ q T A P ε z t) =
      centerSectionTensorMap F ζ hζ q T A P ε z
        (TensorProduct.map (principalSeries A P ε z g)
          (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f ℓ => rfl
  | add t u ht hu => simp only [map_add, ht, hu]

 theorem tensorCoordinate_natural {V W M ι : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup M] [Module ℂ M] [DecidableEq ι]
    (b : Module.Basis ι ℂ M) (L : V →ₗ[ℂ] W) (t : V ⊗[ℂ] M) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b
      (TensorProduct.map L (LinearMap.id : M →ₗ[ℂ] M) t) i =
      L (TensorProduct.equivFinsuppOfBasisRight b t i) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul]
  | add t u ht hu => simp [ht, hu]

theorem centerSectionTensorMap_injective (ε : Sign) (z : ℂ) :
    Function.Injective (centerSectionTensorMap F ζ hζ q T A P ε z) := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ (Multiplicity T P)
  intro t u htu
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  apply Finsupp.ext
  intro i
  apply Subtype.ext
  funext g
  have he := congrArg (fun f : centerSectionSpace F ζ hζ q T A ε z => f.val g) htu
  rw [centerSectionTensorMap_value, centerSectionTensorMap_value] at he
  have hv := (centerCoefficientMap_bijective T P).1 he
  have hh := congrArg (fun t : InducedModule P ⊗[ℂ] Multiplicity T P =>
    TensorProduct.equivFinsuppOfBasisRight b t i) hv
  rw [tensorCoordinate_natural (V := sectionSpace A P ε z) (W := InducedModule P) b (tauEvaluation F ζ hζ q T A P ε z g) t i,
    tensorCoordinate_natural (V := sectionSpace A P ε z) (W := InducedModule P) b (tauEvaluation F ζ hζ q T A P ε z g) u i] at hh
  exact hh

 def centerMultiplicityCoordinate (ε : Sign) (z : ℂ) {ι : Type*}
    [DecidableEq ι] (b : Module.Basis ι ℂ (Multiplicity T P)) (i : ι)
    (f : centerSectionSpace F ζ hζ q T A ε z) : sectionSpace A P ε z :=
  ⟨fun g => TensorProduct.equivFinsuppOfBasisRight b (centerCoefficientEquiv T P (f.val g)) i, by
    constructor
    · intro a g
      change TensorProduct.equivFinsuppOfBasisRight b
        (centerCoefficientEquiv T P (f.val ((a : Cover F ζ hζ q) * g))) i = _
      rw [f.property.1]
      change TensorProduct.equivFinsuppOfBasisRight b
        (centerCoefficientEquiv T P (inducingScalar A z a •
          centerTorus F ζ hζ q T A ε (A.retract a) (f.val g))) i = _
      rw [map_smul, centerCoefficientEquiv_natural]
      simp only [map_smul, Finsupp.smul_apply]
      rw [tensorCoordinate_natural (V := InducedModule P) (W := InducedModule P)]
      cases ε <;> rfl
    · obtain ⟨U, hU⟩ := f.property.2
      refine ⟨U, ?_⟩
      intro u hu
      funext g
      change TensorProduct.equivFinsuppOfBasisRight b (centerCoefficientEquiv T P (f.val (g * u))) i = _
      rw [show f.val (g * u) = f.val g from congrFun (hU u hu) g]⟩

theorem centerSectionTensorMap_surjective (ε : Sign) (z : ℂ) :
    Function.Surjective (centerSectionTensorMap F ζ hζ q T A P ε z) := by
  classical
  letI := tau_moduleFinite T P
  let b := Module.Basis.ofVectorSpace ℂ (Multiplicity T P)
  letI := Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity T P))
  intro f
  let t := ∑ i, centerMultiplicityCoordinate F ζ hζ q T A P ε z b i f ⊗ₜ[ℂ] b i
  refine ⟨t, ?_⟩
  apply Subtype.ext
  funext g
  rw [centerSectionTensorMap_value]
  have ht : TensorProduct.map (tauEvaluation F ζ hζ q T A P ε z g)
      (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t =
      centerCoefficientEquiv T P (f.val g) := by
    change TensorProduct.map _ _ (∑ i, _) = _
    rw [map_sum]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    change (∑ i, TensorProduct.equivFinsuppOfBasisRight b
      (centerCoefficientEquiv T P (f.val g)) i ⊗ₜ[ℂ] b i) = _
    let e := TensorProduct.equivFinsuppOfBasisRight (M := InducedModule P) b
    have he := e.symm_apply_apply (centerCoefficientEquiv T P (f.val g))
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply] at he
    simpa [Finsupp.sum_fintype] using he
  rw [ht]
  exact (LinearEquiv.ofBijective (centerCoefficientMap T P)
    (centerCoefficientMap_bijective T P)).apply_symm_apply (f.val g)

def centerFiberEquiv (ε : Sign) (z : ℂ) :
    centerSectionSpace F ζ hζ q T A ε z ≃ₗ[ℂ]
      (sectionSpace A P ε z ⊗[ℂ] Multiplicity T P) :=
  (LinearEquiv.ofBijective (centerSectionTensorMap F ζ hζ q T A P ε z)
    ⟨centerSectionTensorMap_injective F ζ hζ q T A P ε z,
      centerSectionTensorMap_surjective F ζ hζ q T A P ε z⟩).symm

theorem centerFiberEquiv_value (ε : Sign) (z : ℂ)
    (f : centerSectionSpace F ζ hζ q T A ε z) (g : Cover F ζ hζ q) :
    centerCoefficientEquiv T P (f.val g) =
      TensorProduct.map (tauEvaluation F ζ hζ q T A P ε z g)
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P)
        (centerFiberEquiv F ζ hζ q T A P ε z f) := by
  apply (centerCoefficientMap_bijective T P).1
  rw [← centerSectionTensorMap_value]
  change centerCoefficientMap T P (centerCoefficientEquiv T P (f.val g)) =
    (centerSectionTensorMap F ζ hζ q T A P ε z (centerFiberEquiv F ζ hζ q T A P ε z f)).val g
  have hc : centerCoefficientMap T P (centerCoefficientEquiv T P (f.val g)) = f.val g :=
    (LinearEquiv.ofBijective (centerCoefficientMap T P) (centerCoefficientMap_bijective T P)).apply_symm_apply _
  rw [hc]
  exact congrArg (fun s : centerSectionSpace F ζ hζ q T A ε z => s.val g)
    ((LinearEquiv.ofBijective (centerSectionTensorMap F ζ hζ q T A P ε z)
      ⟨centerSectionTensorMap_injective F ζ hζ q T A P ε z,
        centerSectionTensorMap_surjective F ζ hζ q T A P ε z⟩).apply_symm_apply f).symm

theorem centerFiberEquiv_natural (ε : Sign) (z : ℂ) (g : Cover F ζ hζ q)
    (f : centerSectionSpace F ζ hζ q T A ε z) :
    centerFiberEquiv F ζ hζ q T A P ε z (centerPrincipalSeries F ζ hζ q T A ε z g f) =
      TensorProduct.map (principalSeries A P ε z g)
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P)
        (centerFiberEquiv F ζ hζ q T A P ε z f) := by
  apply centerSectionTensorMap_injective F ζ hζ q T A P ε z
  rw [← centerSectionTensorMap_natural]
  let e := LinearEquiv.ofBijective (centerSectionTensorMap F ζ hζ q T A P ε z)
    ⟨centerSectionTensorMap_injective F ζ hζ q T A P ε z,
      centerSectionTensorMap_surjective F ζ hζ q T A P ε z⟩
  change e (e.symm (centerPrincipalSeries F ζ hζ q T A ε z g f)) =
    centerPrincipalSeries F ζ hζ q T A ε z g (e (e.symm f))
  rw [e.apply_symm_apply, e.apply_symm_apply]

theorem tauDual_finite_coordinates [Fintype D] (ℓ : Multiplicity T P) :
    ∃ (rep : D → H) (c : D → ℂ), ∀ v : InducedModule P,
      ℓ v = ∑ d : D, c d * v.val (rep d) := by
  classical
  let rep := Function.surjInv T.quotient_surjective
  have hrep : ∀ d, T.π (rep d) = d := Function.surjInv_eq T.quotient_surjective
  let ev : InducedModule P →ₗ[ℂ] (D → ℂ) :=
    { toFun := fun v d => v.val (rep d)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hev : Function.Injective ev := by
    intro v w hvw
    apply Subtype.ext
    funext h
    let a : P.L.comap T.π := ⟨h * (rep (T.π h))⁻¹, by
      change T.π (h * (rep (T.π h))⁻¹) ∈ P.L
      simp [hrep]⟩
    have ha : (a : H) * rep (T.π h) = h := by dsimp [a]; simp
    rw [← ha, v.property a, w.property a]
    exact congrArg ((P.ωL a : ℂ) * ·) (congrFun hvw (T.π h))
  let e := LinearEquiv.ofInjective ev hev
  obtain ⟨L, hL⟩ := (ℓ.comp e.symm.toLinearMap).exists_extend
  refine ⟨rep, fun d => L (Pi.single d 1), ?_⟩
  intro v
  have hv : (ev v : D → ℂ) = ∑ d : D, ev v d • Pi.single d (1 : ℂ) := by
    funext d
    simp [← Pi.single_smul, Fintype.sum_pi_single]
  have he : L (ev v) = ℓ v := by
    have hh := LinearMap.congr_fun hL (e v)
    simpa [e] using hh
  rw [← he, hv, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d _
  exact mul_comm _ _

theorem tauStandard_integral_dual (I : IwasawaData A) (μ : Measure (LocalField F q))
    (Jτ : TauStandardFamily F ζ hζ q T A P I μ) (ε : Sign) (z : ℂ)
    (hz : convergenceHalfPlane ε z)
    (f : sectionSpace A P (sourceSign ε) (sourceParameter ε z))
    (g : Cover F ζ hζ q) (ℓ : Multiplicity T P) :
    Integrable (fun x : LocalField F q =>
      ℓ (f.val (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g))) μ ∧
    ℓ ((Jτ.op ε z f).val g) = ∫ x : LocalField F q,
      ℓ (f.val (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g)) ∂μ := by
  classical
  letI := Fintype.ofFinite D
  obtain ⟨rep, c, hc⟩ := tauDual_finite_coordinates T P ℓ
  have hi (d : D) : Integrable (fun x : LocalField F q => c d *
      (f.val (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g)).val (rep d)) μ :=
    (Jτ.integral_eq ε z hz f g (rep d)).1.const_mul (c d)
  constructor
  · simp_rw [hc]
    exact integrable_finset_sum _ (fun d _ => hi d)
  · rw [hc]
    simp_rw [hc]
    rw [integral_finset_sum _ (fun d _ => hi d)]
    apply Finset.sum_congr rfl
    intro d _
    rw [integral_const_mul, (Jτ.integral_eq ε z hz f g (rep d)).2]

def centerTransportedOperator (I : IwasawaData A) (μ : Measure (LocalField F q))
    (Jτ : TauStandardFamily F ζ hζ q T A P I μ) (ε : Sign) (z : ℂ) :
    centerSectionSpace F ζ hζ q T A (sourceSign ε) (sourceParameter ε z) →ₗ[ℂ]
      centerSectionSpace F ζ hζ q T A (targetSign ε) (targetParameter ε z) :=
  (centerSectionTensorMap F ζ hζ q T A P (targetSign ε) (targetParameter ε z)).comp
    ((TensorProduct.map (Jτ.op ε z)
      (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P)).comp
        (centerFiberEquiv F ζ hζ q T A P (sourceSign ε) (sourceParameter ε z)).toLinearMap)

theorem centerTransportedOperator_integral (I : IwasawaData A) (μ : Measure (LocalField F q))
    (Jτ : TauStandardFamily F ζ hζ q T A P I μ) (ε : Sign) (z : ℂ)
    (hz : convergenceHalfPlane ε z)
    (f : centerSectionSpace F ζ hζ q T A (sourceSign ε) (sourceParameter ε z))
    (g : Cover F ζ hζ q) (h : H) :
    Integrable (fun x : LocalField F q =>
      (f.val (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g)).val h) μ ∧
    ((centerTransportedOperator F ζ hζ q T A P I μ Jτ ε z f).val g).val h =
      centerIntegralCoordinate F ζ hζ q T A μ ε z f g h := by
  obtain ⟨t, rfl⟩ := centerSectionTensorMap_surjective F ζ hζ q T A P
    (sourceSign ε) (sourceParameter ε z) f
  have he : centerFiberEquiv F ζ hζ q T A P (sourceSign ε) (sourceParameter ε z)
      (centerSectionTensorMap F ζ hζ q T A P (sourceSign ε) (sourceParameter ε z) t) = t :=
    (LinearEquiv.ofBijective (centerSectionTensorMap F ζ hζ q T A P (sourceSign ε) (sourceParameter ε z))
      ⟨centerSectionTensorMap_injective F ζ hζ q T A P _ _,
        centerSectionTensorMap_surjective F ζ hζ q T A P _ _⟩).symm_apply_apply t
  simp only [centerTransportedOperator, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
  clear he
  induction t using TensorProduct.induction_on with
  | zero => simp [centerIntegralCoordinate]
  | tmul f ℓ =>
    let L : Multiplicity T P := ℓ.comp (tau P h)
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply, centerSectionTensorMap_tmul,
      centerCoefficientMap_tmul, centerIntegralCoordinate, L, LinearMap.comp_apply]
      using tauStandard_integral_dual F ζ hζ q T A P I μ Jτ ε z hz f g L
  | add t u ht hu =>
    constructor
    · simpa only [map_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply] using
        (show Integrable (fun x : LocalField F q =>
          ((centerSectionTensorMap F ζ hζ q T A P (sourceSign ε) (sourceParameter ε z) t).val
            (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g)).val h +
          ((centerSectionTensorMap F ζ hζ q T A P (sourceSign ε) (sourceParameter ε z) u).val
            (kernelW (LocalField F q) A ε * nLift F ζ hζ q x * g)).val h) μ from ht.1.add hu.1)
    · simp only [map_add, Submodule.coe_add, Pi.add_apply]
      rw [ht.2, hu.2]
      unfold centerIntegralCoordinate
      simp only [map_add, Submodule.coe_add, Pi.add_apply]
      exact (integral_add ht.1 hu.1).symm

theorem centerTransportedOperator_intertwining (I : IwasawaData A) (μ : Measure (LocalField F q))
    (Jτ : TauStandardFamily F ζ hζ q T A P I μ) (ε : Sign) (z : ℂ)
    (hz : denominator (LocalField F q) ε z ≠ 0) (g : Cover F ζ hζ q)
    (f : centerSectionSpace F ζ hζ q T A (sourceSign ε) (sourceParameter ε z)) :
    centerTransportedOperator F ζ hζ q T A P I μ Jτ ε z
      (centerPrincipalSeries F ζ hζ q T A (sourceSign ε) (sourceParameter ε z) g f) =
    centerPrincipalSeries F ζ hζ q T A (targetSign ε) (targetParameter ε z) g
      (centerTransportedOperator F ζ hζ q T A P I μ Jτ ε z f) := by
  simp only [centerTransportedOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
    centerFiberEquiv_natural]
  rw [centerSectionTensorMap_natural]
  congr 1
  generalize centerFiberEquiv F ζ hζ q T A P (sourceSign ε) (sourceParameter ε z) f = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v m =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [Jτ.intertwining ε z hz g v]
  | add t u ht hu => simp only [map_add, ht, hu]

open ValuativeRel

private theorem center_laurent_zero (p : LaurentPolynomial ℂ)
    (U : Set ℂˣ) (hU : U.Infinite)
    (hp : ∀ u ∈ U, LaurentPolynomial.eval₂ (RingHom.id ℂ) u p = 0) : p = 0 := by
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow p
  have hroots : {x : ℂ | f.eval x = (0 : Polynomial ℂ).eval x}.Infinite := by
    apply (hU.image (f := fun u : ℂˣ => (u : ℂ)) Units.val_injective.injOn).mono
    rintro x ⟨u, hu, rfl⟩
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℂ) u) hf
    simp only [map_mul, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id,
      hp u hu, zero_mul, Polynomial.eval_zero] at he ⊢
    exact he
  have hz := Polynomial.eq_of_infinite_eval_eq f 0 hroots
  rw [hz, map_zero] at hf
  exact (IsUnit.mul_left_inj (LaurentPolynomial.isUnit_T (R := ℂ) (n : ℤ))).mp (by simpa using hf.symm)

 def center_scalarLaurent {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (p : ℤ →₀ V) (l : V →ₗ[ℂ] ℂ) : LaurentPolynomial ℂ :=
  p.sum (fun n v => LaurentPolynomial.C (l v) * LaurentPolynomial.T n)

private theorem center_scalarLaurent_coeff {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (p : ℤ →₀ V) (l : V →ₗ[ℂ] ℂ) (n : ℤ) :
    (center_scalarLaurent p l).coeff n = l (p n) := by
  classical
  simp only [center_scalarLaurent, ← LaurentPolynomial.single_eq_C_mul_T,
    Finsupp.sum, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply,
    AddMonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    simp [hbn]
  · intro hn
    simp [Finsupp.notMem_support_iff.mp hn]

private theorem center_scalarLaurent_eval {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (p : ℤ →₀ V) (l : V →ₗ[ℂ] ℂ) (u : ℂˣ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) u (center_scalarLaurent p l) =
      l (p.sum (fun n v => (u : ℂ) ^ n • v)) := by
  classical
  simp only [center_scalarLaurent, Finsupp.sum, map_sum,
    LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, Units.val_zpow_eq_zpow_val,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  exact mul_comm _ _
private theorem center_evaluation_norm (ε : Sign) (x : ℝ) :
    ‖(evaluationUnit (LocalField F q) ε (x : ℂ) : ℂ)‖ =
      Real.exp ((if ε = .plus then -x else x) * Real.log (residueCardinality (LocalField F q) : ℝ)) := by
  cases ε with
  | plus =>
    change ‖KPRankOneRootParameter.r (LocalField F q) (x : ℂ)‖ = _
    simp only [KPRankOneRootParameter.r, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero,
      evaluationUnit, if_true]
  | minus =>
    change ‖(KPRankOneRootParameter.r (LocalField F q) (x : ℂ))⁻¹‖ = _
    simp only [KPRankOneRootParameter.r, norm_inv, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero,
      ← Real.exp_neg, neg_mul, neg_neg, reduceCtorEq, if_false]

private theorem center_evaluation_infinite (ε : Sign) :
    {u : ℂˣ | ∃ s : ℂ, convergenceHalfPlane ε s ∧ evaluationUnit (LocalField F q) ε s = u}.Infinite := by
  let a : ℕ → ℝ := fun n => if ε = .plus then (n : ℝ) else -(n : ℝ) - 1
  have ha : Function.Injective a := by
    intro m n h
    dsimp [a] at h
    cases ε <;> simp only [if_true, if_false, reduceCtorEq] at h
    · exact_mod_cast h
    · have : (m : ℝ) = (n : ℝ) := by linarith
      exact_mod_cast this
  have hl : Real.log (residueCardinality (LocalField F q) : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast Finite.one_lt_card (α := IsLocalRing.ResidueField (valuation (LocalField F q)).integer)
  have hinj : Function.Injective (fun n => evaluationUnit (LocalField F q) ε (a n : ℂ)) := by
    intro m n h
    apply ha
    have he := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) h
    rw [center_evaluation_norm, center_evaluation_norm] at he
    have he := Real.exp_injective he
    have he' := (mul_left_inj' hl).mp he
    cases ε <;> simpa using he'
  apply (Set.infinite_range_of_injective hinj).mono
  rintro u ⟨n, rfl⟩
  refine ⟨(a n : ℂ), ?_, rfl⟩
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  cases ε <;> simp only [a, convergenceHalfPlane, if_true, if_false,
    reduceCtorEq, Complex.ofReal_re] <;> linarith

theorem center_level_numerator_unique (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (μ : Measure (LocalField F q)) (ε : Sign)
    (p p' : CenterLevelLaurentOperator F ζ hζ q T A I J ε)
    (hp : IsCenterLevelNumerator F ζ hζ q T A I J μ ε p)
    (hp' : IsCenterLevelNumerator F ζ hζ q T A I J μ ε p') : p = p' := by
  apply Finsupp.ext
  intro n
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply Subtype.ext
  funext k
  apply Subtype.ext
  funext h
  let l : (centerCompactLevel F ζ hζ q T A I (sourceSign ε) J →ₗ[ℂ]
      centerCompactLevel F ζ hζ q T A I (targetSign ε) J) →ₗ[ℂ] ℂ :=
    { toFun := fun M => ((M φ : centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hz : center_scalarLaurent p l - center_scalarLaurent p' l = 0 := by
    apply center_laurent_zero _ _ (center_evaluation_infinite F q ε)
    rintro u ⟨z, hz, rfl⟩
    rw [map_sub, center_scalarLaurent_eval, center_scalarLaurent_eval, sub_eq_zero]
    change ((centerEvaluate F ζ hζ q T A I J ε p (evaluationUnit (LocalField F q) ε z) φ :
      centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h =
        ((centerEvaluate F ζ hζ q T A I J ε p' (evaluationUnit (LocalField F q) ε z) φ :
          centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h
    rw [hp z hz φ k h, hp' z hz φ k h]
  have he := congrArg (fun p : LaurentPolynomial ℂ => p.coeff n) (sub_eq_zero.mp hz)
  rw [center_scalarLaurent_coeff, center_scalarLaurent_coeff] at he
  exact he

theorem center_level_numerator_compatible (I : IwasawaData A)
    (J J' : CompactOpenLevel (Cover F ζ hζ q)) (μ : Measure (LocalField F q)) (ε : Sign)
    (p : CenterLevelLaurentOperator F ζ hζ q T A I J ε)
    (p' : CenterLevelLaurentOperator F ζ hζ q T A I J' ε)
    (hp : IsCenterLevelNumerator F ζ hζ q T A I J μ ε p)
    (hp' : IsCenterLevelNumerator F ζ hζ q T A I J' μ ε p')
    (φ : centerCompactLevel F ζ hζ q T A I (sourceSign ε) J)
    (φ' : centerCompactLevel F ζ hζ q T A I (sourceSign ε) J')
    (hφ : (φ : centerCompactPicture F ζ hζ q T A I (sourceSign ε)) =
      (φ' : centerCompactPicture F ζ hζ q T A I (sourceSign ε))) (n : ℤ) :
    ((p n) φ : centerCompactPicture F ζ hζ q T A I (targetSign ε)) =
      ((p' n) φ' : centerCompactPicture F ζ hζ q T A I (targetSign ε)) := by
  apply Subtype.ext
  funext k
  apply Subtype.ext
  funext h
  let l : (centerCompactLevel F ζ hζ q T A I (sourceSign ε) J →ₗ[ℂ]
      centerCompactLevel F ζ hζ q T A I (targetSign ε) J) →ₗ[ℂ] ℂ :=
    { toFun := fun M => ((M φ : centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let l' : (centerCompactLevel F ζ hζ q T A I (sourceSign ε) J' →ₗ[ℂ]
      centerCompactLevel F ζ hζ q T A I (targetSign ε) J') →ₗ[ℂ] ℂ :=
    { toFun := fun M => ((M φ' : centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hz : center_scalarLaurent p l - center_scalarLaurent p' l' = 0 := by
    apply center_laurent_zero _ _ (center_evaluation_infinite F q ε)
    rintro u ⟨z, hz, rfl⟩
    rw [map_sub, center_scalarLaurent_eval, center_scalarLaurent_eval, sub_eq_zero]
    change ((centerEvaluate F ζ hζ q T A I J ε p (evaluationUnit (LocalField F q) ε z) φ :
      centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h =
        ((centerEvaluate F ζ hζ q T A I J' ε p' (evaluationUnit (LocalField F q) ε z) φ' :
          centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h
    rw [hp z hz φ k h, hp' z hz φ' k h, hφ]
  have he := congrArg (fun p : LaurentPolynomial ℂ => p.coeff n) (sub_eq_zero.mp hz)
  rw [center_scalarLaurent_coeff, center_scalarLaurent_coeff] at he
  exact he

set_option maxHeartbeats 800000 in

theorem centerContinuedLevel_compatible (I : IwasawaData A)
    (J J' : CompactOpenLevel (Cover F ζ hζ q)) (μ : Measure (LocalField F q)) (ε : Sign)
    (p : CenterLevelLaurentOperator F ζ hζ q T A I J ε)
    (p' : CenterLevelLaurentOperator F ζ hζ q T A I J' ε)
    (hp : IsCenterLevelNumerator F ζ hζ q T A I J μ ε p)
    (hp' : IsCenterLevelNumerator F ζ hζ q T A I J' μ ε p')
    (φ : centerCompactLevel F ζ hζ q T A I (sourceSign ε) J)
    (φ' : centerCompactLevel F ζ hζ q T A I (sourceSign ε) J')
    (hφ : (φ : centerCompactPicture F ζ hζ q T A I (sourceSign ε)) =
      (φ' : centerCompactPicture F ζ hζ q T A I (sourceSign ε))) (z : ℂ) :
    (centerContinuedLevel F ζ hζ q T A I J ε p z φ :
      centerCompactPicture F ζ hζ q T A I (targetSign ε)) =
    (centerContinuedLevel F ζ hζ q T A I J' ε p' z φ' :
      centerCompactPicture F ζ hζ q T A I (targetSign ε)) := by
  apply Subtype.ext
  funext k
  apply Subtype.ext
  funext h
  have he : center_scalarLaurent p
      ({ toFun := fun M => ((M φ : centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h
         map_add' := by intros; rfl
         map_smul' := by intros; rfl } : _ →ₗ[ℂ] ℂ) =
      center_scalarLaurent p'
      ({ toFun := fun M => ((M φ' : centerCompactPicture F ζ hζ q T A I (targetSign ε)).val k).val h
         map_add' := by intros; rfl
         map_smul' := by intros; rfl } : _ →ₗ[ℂ] ℂ) := by
    apply LaurentPolynomial.ext
    intro n
    rw [center_scalarLaurent_coeff, center_scalarLaurent_coeff]
    exact congrArg (fun ψ : centerCompactPicture F ζ hζ q T A I (targetSign ε) => (ψ.val k).val h)
      (center_level_numerator_compatible F ζ hζ q T A I J J' μ ε p p' hp hp' φ φ' hφ n)
  have hv := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℂ)
    (evaluationUnit (LocalField F q) ε z)) he
  rw [center_scalarLaurent_eval, center_scalarLaurent_eval] at hv
  change (denominator (LocalField F q) ε z)⁻¹ * _ =
    (denominator (LocalField F q) ε z)⁻¹ * _
  exact congrArg ((denominator (LocalField F q) ε z)⁻¹ * ·) hv

section CompactCoefficientLevels
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 80000

def centerCompactTensorMap (I : IwasawaData A) (ε : Sign) :
    compactPicture A P I ε ⊗[ℂ] Multiplicity T P →ₗ[ℂ]
      centerCompactPicture F ζ hζ q T A I ε :=
  (centerCompactTrivialization F ζ hζ q T A I ε 0).symm.toLinearMap.comp
    ((centerSectionTensorMap F ζ hζ q T A P ε 0).comp
      (TensorProduct.map (compactTrivialization A P I ε 0).toLinearMap
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P)))

theorem centerCompactTensorMap_value (I : IwasawaData A) (ε : Sign)
    (t : compactPicture A P I ε ⊗[ℂ] Multiplicity T P)
    (k : I.compact.toOpenSubgroup) :
    (centerCompactTensorMap F ζ hζ q T A P I ε t).val k =
      centerCoefficientMap T P (TensorProduct.map
        ({ toFun := fun φ : compactPicture A P I ε => φ.val k
           map_add' := by intros; rfl
           map_smul' := by intros; rfl } : compactPicture A P I ε →ₗ[ℂ] InducedModule P)
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ℓ =>
    change centerCoefficientMap T P
      (((compactTrivialization A P I ε 0 φ).val (k : Cover F ζ hζ q)) ⊗ₜ[ℂ] ℓ) = _
    have he := congrArg (fun ψ : compactPicture A P I ε => ψ.val k)
      ((compactTrivialization A P I ε 0).symm_apply_apply φ)
    exact congrArg (fun v => centerCoefficientMap T P (v ⊗ₜ[ℂ] ℓ)) he
  | add t u ht hu => simpa only [map_add, Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) ht hu

theorem centerCompactTensorMap_extend (I : IwasawaData A) (ε : Sign) (z : ℂ)
    (t : compactPicture A P I ε ⊗[ℂ] Multiplicity T P) :
    centerCompactTrivialization F ζ hζ q T A I ε z
      (centerCompactTensorMap F ζ hζ q T A P I ε t) =
    centerSectionTensorMap F ζ hζ q T A P ε z
      (TensorProduct.map (compactTrivialization A P I ε z).toLinearMap
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t) := by
  apply (centerCompactTrivialization F ζ hζ q T A I ε z).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  funext k
  rw [centerCompactTensorMap_value]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ℓ =>
    change centerCoefficientMap T P (φ.val k ⊗ₜ[ℂ] ℓ) =
      centerCoefficientMap T P (((compactTrivialization A P I ε z φ).val
        (k : Cover F ζ hζ q)) ⊗ₜ[ℂ] ℓ)
    have he := congrArg (fun ψ : compactPicture A P I ε => ψ.val k)
      ((compactTrivialization A P I ε z).symm_apply_apply φ)
    exact congrArg (fun v => centerCoefficientMap T P (v ⊗ₜ[ℂ] ℓ)) he.symm
  | add t u ht hu => simpa only [map_add, Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) ht hu

theorem centerCompactTensorMap_bijective (I : IwasawaData A) (ε : Sign) :
    Function.Bijective (centerCompactTensorMap F ζ hζ q T A P I ε) := by
  let e := TensorProduct.congr (compactTrivialization A P I ε 0)
    (LinearEquiv.refl ℂ (Multiplicity T P))
  have he : Function.Bijective
      (TensorProduct.map (compactTrivialization A P I ε 0).toLinearMap
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P)) := e.bijective
  exact (centerCompactTrivialization F ζ hζ q T A I ε 0).symm.bijective.comp
    ((show Function.Bijective (centerSectionTensorMap F ζ hζ q T A P ε 0) from
      ⟨centerSectionTensorMap_injective F ζ hζ q T A P ε 0,
       centerSectionTensorMap_surjective F ζ hζ q T A P ε 0⟩).comp he)

def centerLevelTensorMap (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel (Cover F ζ hζ q)) :
    compactLevel A P I ε J ⊗[ℂ] Multiplicity T P →ₗ[ℂ]
      centerCompactLevel F ζ hζ q T A I ε J :=
  LinearMap.codRestrict (centerCompactLevel F ζ hζ q T A I ε J)
    ((centerCompactTensorMap F ζ hζ q T A P I ε).comp
      (TensorProduct.map (compactLevel A P I ε J).subtype
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P))) (by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact (centerCompactLevel F ζ hζ q T A I ε J).zero_mem
    | tmul φ ℓ =>
      intro j k k' he
      simp only [LinearMap.comp_apply]
      rw [centerCompactTensorMap_value, centerCompactTensorMap_value]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply]
      exact congrArg (fun v => centerCoefficientMap T P (v ⊗ₜ[ℂ] ℓ)) (φ.property j k k' he)
    | add t u ht hu =>
      simp only [map_add]
      exact (centerCompactLevel F ζ hζ q T A I ε J).add_mem ht hu)

private theorem centerLevelTensorMap_injective (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel (Cover F ζ hζ q)) :
    Function.Injective (centerLevelTensorMap F ζ hζ q T A P I ε J) := by
  intro t u he
  have hh := congrArg (fun φ : centerCompactLevel F ζ hζ q T A I ε J => φ.val) he
  have hv := (centerCompactTensorMap_bijective F ζ hζ q T A P I ε).1 hh
  classical
  let b := Module.Basis.ofVectorSpace ℂ (Multiplicity T P)
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  apply Finsupp.ext
  intro i
  apply Subtype.ext
  have hc (t : compactLevel A P I ε J ⊗[ℂ] Multiplicity T P) :
      TensorProduct.equivFinsuppOfBasisRight b
        (TensorProduct.map (compactLevel A P I ε J).subtype
          (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t) i =
      (TensorProduct.equivFinsuppOfBasisRight b t i).val := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul φ ℓ => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul]
    | add t u ht hu => simp [ht, hu]
  exact (hc t).symm.trans ((congrArg (fun x => TensorProduct.equivFinsuppOfBasisRight b x i) hv).trans (hc u))

 def centerCompactMultiplicityCoordinate (I : IwasawaData A) (ε : Sign)
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι ℂ (Multiplicity T P)) (i : ι)
    (φ : centerCompactPicture F ζ hζ q T A I ε) : compactPicture A P I ε :=
  (compactTrivialization A P I ε 0).symm
    (TensorProduct.equivFinsuppOfBasisRight b
      (centerFiberEquiv F ζ hζ q T A P ε 0
        (centerCompactTrivialization F ζ hζ q T A I ε 0 φ)) i)

private theorem compactCoordinate_value (I : IwasawaData A) (ε : Sign)
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι ℂ (Multiplicity T P)) (i : ι)
    (φ : centerCompactPicture F ζ hζ q T A I ε) (k : I.compact.toOpenSubgroup) :
    (centerCompactMultiplicityCoordinate F ζ hζ q T A P I ε b i φ).val k =
      TensorProduct.equivFinsuppOfBasisRight b (centerCoefficientEquiv T P (φ.val k)) i := by
  have hc : (centerCompactTrivialization F ζ hζ q T A I ε 0 φ).val (k : Cover F ζ hζ q) = φ.val k :=
    congrArg (fun ψ : centerCompactPicture F ζ hζ q T A I ε => ψ.val k)
      ((centerCompactTrivialization F ζ hζ q T A I ε 0).symm_apply_apply φ)
  rw [← hc, centerFiberEquiv_value]
  unfold centerCompactMultiplicityCoordinate
  generalize centerFiberEquiv F ζ hζ q T A P ε 0
    (centerCompactTrivialization F ζ hζ q T A I ε 0 φ) = t
  change ((TensorProduct.equivFinsuppOfBasisRight b t i).val (k : Cover F ζ hζ q)) = _
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f ℓ => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul, tauEvaluation]
  | add t u ht hu => simp [ht, hu]

theorem centerLevelTensorMap_bijective (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel (Cover F ζ hζ q)) :
    Function.Bijective (centerLevelTensorMap F ζ hζ q T A P I ε J) := by
  refine ⟨centerLevelTensorMap_injective F ζ hζ q T A P I ε J, ?_⟩
  classical
  letI := tau_moduleFinite T P
  let b := Module.Basis.ofVectorSpace ℂ (Multiplicity T P)
  letI := Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity T P))
  intro φ
  have hcoord (i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity T P)) :
      centerCompactMultiplicityCoordinate F ζ hζ q T A P I ε b i φ.val ∈ compactLevel A P I ε J := by
    intro j k k' he
    rw [compactCoordinate_value, compactCoordinate_value, φ.property j k k' he]
  let t := ∑ i, (⟨centerCompactMultiplicityCoordinate F ζ hζ q T A P I ε b i φ.val,
    hcoord i⟩ : compactLevel A P I ε J) ⊗ₜ[ℂ] b i
  refine ⟨t, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change (centerCompactTensorMap F ζ hζ q T A P I ε
    (TensorProduct.map (compactLevel A P I ε J).subtype
      (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t)).val k = φ.val.val k
  rw [centerCompactTensorMap_value]
  have ht : TensorProduct.map
      ({ toFun := fun ψ : compactPicture A P I ε => ψ.val k
         map_add' := by intros; rfl
         map_smul' := by intros; rfl } : compactPicture A P I ε →ₗ[ℂ] InducedModule P)
      (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P)
      (TensorProduct.map (compactLevel A P I ε J).subtype
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t) =
      centerCoefficientEquiv T P (φ.val.val k) := by
    simp only [t, map_sum, TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply]
    change (∑ i, (centerCompactMultiplicityCoordinate F ζ hζ q T A P I ε b i φ.val).val k ⊗ₜ[ℂ] b i) = _
    simp only [compactCoordinate_value]
    let e := TensorProduct.equivFinsuppOfBasisRight (M := InducedModule P) b
    have he := e.symm_apply_apply (centerCoefficientEquiv T P (φ.val.val k))
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply] at he
    simpa [Finsupp.sum_fintype] using he
  rw [ht]
  exact (LinearEquiv.ofBijective (centerCoefficientMap T P)
    (centerCoefficientMap_bijective T P)).apply_symm_apply _

def centerLevelTensorEquiv (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel (Cover F ζ hζ q)) :
    compactLevel A P I ε J ⊗[ℂ] Multiplicity T P ≃ₗ[ℂ]
      centerCompactLevel F ζ hζ q T A I ε J :=
  LinearEquiv.ofBijective (centerLevelTensorMap F ζ hζ q T A P I ε J)
    (centerLevelTensorMap_bijective F ζ hζ q T A P I ε J)

def centerLevelOperatorTransport (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (ε : Sign) :
    (compactLevel A P I (sourceSign ε) J →ₗ[ℂ] compactLevel A P I (targetSign ε) J) →ₗ[ℂ]
      (centerCompactLevel F ζ hζ q T A I (sourceSign ε) J →ₗ[ℂ]
        centerCompactLevel F ζ hζ q T A I (targetSign ε) J) where
  toFun M := (centerLevelTensorEquiv F ζ hζ q T A P I (targetSign ε) J).toLinearMap.comp
    ((TensorProduct.map M (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P)).comp
      (centerLevelTensorEquiv F ζ hζ q T A P I (sourceSign ε) J).symm.toLinearMap)
  map_add' M N := by
    simp only [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c M := by
    simp only [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul,
      RingHom.id_apply]

def centerLevelLaurentTransport (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (ε : Sign)
    (p : LevelLaurentOperator (LocalField F q) A P I J ε) :
    CenterLevelLaurentOperator F ζ hζ q T A I J ε :=
  Finsupp.mapRange.linearMap (centerLevelOperatorTransport F ζ hζ q T A P I J ε) p

theorem centerLevelLaurentTransport_evaluate (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (ε : Sign)
    (p : LevelLaurentOperator (LocalField F q) A P I J ε) (u : ℂˣ) :
    centerEvaluate F ζ hζ q T A I J ε
      (centerLevelLaurentTransport F ζ hζ q T A P I J ε p) u =
    centerLevelOperatorTransport F ζ hζ q T A P I J ε
      (evaluate (LocalField F q) A P I J ε p u) := by
  unfold centerEvaluate centerLevelLaurentTransport evaluate
  rw [Finsupp.mapRange.linearMap_apply, Finsupp.sum_mapRange_index (by intro; simp)]
  simp only [Finsupp.sum, map_sum, map_smul]

theorem centerLevelLaurentTransport_continued (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (ε : Sign)
    (p : LevelLaurentOperator (LocalField F q) A P I J ε) (z : ℂ) :
    centerContinuedLevel F ζ hζ q T A I J ε
      (centerLevelLaurentTransport F ζ hζ q T A P I J ε p) z =
    centerLevelOperatorTransport F ζ hζ q T A P I J ε
      (continuedLevel (LocalField F q) A P I J ε p z) := by
  unfold centerContinuedLevel continuedLevel
  rw [centerLevelLaurentTransport_evaluate, map_smul]

theorem centerLevelTensorMap_extend (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (z : ℂ)
    (t : compactLevel A P I ε J ⊗[ℂ] Multiplicity T P) :
    centerCompactTrivialization F ζ hζ q T A I ε z
      (centerLevelTensorMap F ζ hζ q T A P I ε J t).val =
    centerSectionTensorMap F ζ hζ q T A P ε z
      (TensorProduct.map
        ((compactTrivialization A P I ε z).toLinearMap.comp (compactLevel A P I ε J).subtype)
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t) := by
  change centerCompactTrivialization F ζ hζ q T A I ε z
    (centerCompactTensorMap F ζ hζ q T A P I ε
      (TensorProduct.map (compactLevel A P I ε J).subtype
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t)) = _
  rw [centerCompactTensorMap_extend]
  congr 1
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ℓ => simp
  | add t u ht hu => simp [ht, hu]

theorem centerLevelLaurentTransport_shell (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (μ : Measure (LocalField F q))
    (Jτ : TauStandardFamily F ζ hζ q T A P I μ) (ε : Sign)
    (p : LevelLaurentOperator (LocalField F q) A P I J ε)
    (hp : IsLevelNumerator (LocalField F q) A P I J μ ε p)
    (z : ℂ) (hz : denominator (LocalField F q) ε z ≠ 0)
    (φ : centerCompactLevel F ζ hζ q T A I (sourceSign ε) J) :
    centerTransportedOperator F ζ hζ q T A P I μ Jτ ε z
      (centerCompactTrivialization F ζ hζ q T A I (sourceSign ε) (sourceParameter ε z) φ.val) =
    centerCompactTrivialization F ζ hζ q T A I (targetSign ε) (targetParameter ε z)
      (centerContinuedLevel F ζ hζ q T A I J ε
        (centerLevelLaurentTransport F ζ hζ q T A P I J ε p) z φ).val := by
  obtain ⟨t, rfl⟩ := (centerLevelTensorMap_bijective F ζ hζ q T A P I (sourceSign ε) J).2 φ
  rw [centerLevelTensorMap_extend, centerLevelLaurentTransport_continued]
  have he : centerLevelOperatorTransport F ζ hζ q T A P I J ε
      (continuedLevel (LocalField F q) A P I J ε p z)
      (centerLevelTensorMap F ζ hζ q T A P I (sourceSign ε) J t) =
    centerLevelTensorMap F ζ hζ q T A P I (targetSign ε) J
      (TensorProduct.map (continuedLevel (LocalField F q) A P I J ε p z)
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P) t) := by
    exact congrArg (centerLevelTensorEquiv F ζ hζ q T A P I (targetSign ε) J)
      (congrArg (TensorProduct.map (continuedLevel (LocalField F q) A P I J ε p z)
        (LinearMap.id : Multiplicity T P →ₗ[ℂ] Multiplicity T P))
        ((centerLevelTensorEquiv F ζ hζ q T A P I (sourceSign ε) J).symm_apply_apply t))
  rw [he, centerLevelTensorMap_extend]
  clear he
  have hf (t : sectionSpace A P (sourceSign ε) (sourceParameter ε z) ⊗[ℂ] Multiplicity T P) :
      centerFiberEquiv F ζ hζ q T A P (sourceSign ε) (sourceParameter ε z)
        (centerSectionTensorMap F ζ hζ q T A P (sourceSign ε) (sourceParameter ε z) t) = t := by
    exact (LinearEquiv.ofBijective (centerSectionTensorMap F ζ hζ q T A P _ _)
      ⟨centerSectionTensorMap_injective F ζ hζ q T A P _ _,
       centerSectionTensorMap_surjective F ζ hζ q T A P _ _⟩).symm_apply_apply t
  simp only [centerTransportedOperator, LinearMap.comp_apply, LinearEquiv.coe_coe, hf]
  congr 1
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul ψ ℓ =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.comp_apply,
      Submodule.subtype_apply]
    exact congrArg (fun f => f ⊗ₜ[ℂ] ℓ) (Jτ.shell_eq J ε p hp z hz ψ)
  | add t u ht hu => simp [ht, hu]

theorem centerLevelLaurentTransport_isNumerator (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (μ : Measure (LocalField F q))
    (Jτ : TauStandardFamily F ζ hζ q T A P I μ) (ε : Sign)
    (p : LevelLaurentOperator (LocalField F q) A P I J ε)
    (hp : IsLevelNumerator (LocalField F q) A P I J μ ε p) :
    IsCenterLevelNumerator F ζ hζ q T A I J μ ε
      (centerLevelLaurentTransport F ζ hζ q T A P I J ε p) := by
  intro z hz φ k h
  have hd := denominator_ne_zero_of_convergence (LocalField F q) ε z hz
  have hs := congrArg (fun f : centerSectionSpace F ζ hζ q T A
      (targetSign ε) (targetParameter ε z) => (f.val (k : Cover F ζ hζ q)).val h)
    (centerLevelLaurentTransport_shell F ζ hζ q T A P I J μ Jτ ε p hp z hd φ)
  have hc : (centerCompactTrivialization F ζ hζ q T A I
      (targetSign ε) (targetParameter ε z)
      (centerContinuedLevel F ζ hζ q T A I J ε
        (centerLevelLaurentTransport F ζ hζ q T A P I J ε p) z φ).val).val
        (k : Cover F ζ hζ q) =
      (centerContinuedLevel F ζ hζ q T A I J ε
        (centerLevelLaurentTransport F ζ hζ q T A P I J ε p) z φ).val.val k := by
    exact congrArg (fun ψ : centerCompactPicture F ζ hζ q T A I (targetSign ε) => ψ.val k)
      ((centerCompactTrivialization F ζ hζ q T A I (targetSign ε)
        (targetParameter ε z)).symm_apply_apply _)
  rw [hc, (centerTransportedOperator_integral F ζ hζ q T A P I μ Jτ ε z hz
    (centerCompactTrivialization F ζ hζ q T A I (sourceSign ε) (sourceParameter ε z) φ.val)
    (k : Cover F ζ hζ q) h).2] at hs
  change _ = denominator (LocalField F q) ε z * _
  rw [hs]
  change _ = denominator (LocalField F q) ε z *
    ((denominator (LocalField F q) ε z)⁻¹ * _)
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

def centerStandardFamilyFromTau (I : IwasawaData A) (μ : Measure (LocalField F q))
    (Jτ : TauStandardFamily F ζ hζ q T A P I μ) :
    CenterStandardFamily F ζ hζ q T A I μ where
  op := centerTransportedOperator F ζ hζ q T A P I μ Jτ
  intertwining := centerTransportedOperator_intertwining F ζ hζ q T A P I μ Jτ
  numerators J hJ ε := by
    obtain ⟨p, hp, _⟩ := Jτ.numerators J hJ ε
    refine ⟨centerLevelLaurentTransport F ζ hζ q T A P I J ε p,
      centerLevelLaurentTransport_isNumerator F ζ hζ q T A P I J μ Jτ ε p hp, ?_⟩
    intro p' hp'
    exact center_level_numerator_unique F ζ hζ q T A I J μ ε p' _ hp'
      (centerLevelLaurentTransport_isNumerator F ζ hζ q T A P I J μ Jτ ε p hp)
  integral_eq := centerTransportedOperator_integral F ζ hζ q T A P I μ Jτ
  shell_eq J ε p hp z hz φ := by
    obtain ⟨J', hJ', φ', hφ'⟩ := centerSection_has_compact_level F ζ hζ q T A I
      (sourceSign ε) (sourceParameter ε z)
      (centerCompactTrivialization F ζ hζ q T A I (sourceSign ε) (sourceParameter ε z) φ.val)
    obtain ⟨pτ, hpτ, _⟩ := Jτ.numerators J' hJ' ε
    have hφ : φ'.val = φ.val := by
      exact (centerCompactTrivialization F ζ hζ q T A I
        (sourceSign ε) (sourceParameter ε z)).injective hφ'
    rw [← hφ', centerLevelLaurentTransport_shell F ζ hζ q T A P I J' μ Jτ ε pτ hpτ z hz φ']
    congr 1
    exact centerContinuedLevel_compatible F ζ hζ q T A I J' J μ ε _ p
      (centerLevelLaurentTransport_isNumerator F ζ hζ q T A P I J' μ Jτ ε pτ hpτ)
      hp φ' φ hφ z

theorem tauContinuedLevel_compatible_any (I : IwasawaData A)
    (J J' : CompactOpenLevel (Cover F ζ hζ q)) (μ : Measure (LocalField F q)) (ε : Sign)
    (p : LevelLaurentOperator (LocalField F q) A P I J ε)
    (p' : LevelLaurentOperator (LocalField F q) A P I J' ε)
    (hp : IsLevelNumerator (LocalField F q) A P I J μ ε p)
    (hp' : IsLevelNumerator (LocalField F q) A P I J' μ ε p')
    (φ : compactLevel A P I (sourceSign ε) J)
    (φ' : compactLevel A P I (sourceSign ε) J')
    (hφ : φ.val = φ'.val) (z : ℂ) :
    (continuedLevel (LocalField F q) A P I J ε p z φ : compactPicture A P I (targetSign ε)) =
    (continuedLevel (LocalField F q) A P I J' ε p' z φ' : compactPicture A P I (targetSign ε)) := by
  apply Subtype.ext
  funext k
  apply Subtype.ext
  funext h
  let l : (compactLevel A P I (sourceSign ε) J →ₗ[ℂ]
      compactLevel A P I (targetSign ε) J) →ₗ[ℂ] ℂ :=
    { toFun := fun M => ((M φ : compactPicture A P I (targetSign ε)).val k).val h
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let l' : (compactLevel A P I (sourceSign ε) J' →ₗ[ℂ]
      compactLevel A P I (targetSign ε) J') →ₗ[ℂ] ℂ :=
    { toFun := fun M => ((M φ' : compactPicture A P I (targetSign ε)).val k).val h
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : center_scalarLaurent p l = center_scalarLaurent p' l' := by
    apply sub_eq_zero.mp
    apply center_laurent_zero _ _ (center_evaluation_infinite F q ε)
    rintro u ⟨s, hs, rfl⟩
    rw [map_sub, center_scalarLaurent_eval, center_scalarLaurent_eval, sub_eq_zero]
    change ((evaluate (LocalField F q) A P I J ε p (evaluationUnit (LocalField F q) ε s) φ :
      compactPicture A P I (targetSign ε)).val k).val h =
      ((evaluate (LocalField F q) A P I J' ε p' (evaluationUnit (LocalField F q) ε s) φ' :
        compactPicture A P I (targetSign ε)).val k).val h
    rw [hp s hs φ k h, hp' s hs φ' k h, hφ]
  have hv := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℂ)
    (evaluationUnit (LocalField F q) ε z)) he
  rw [center_scalarLaurent_eval, center_scalarLaurent_eval] at hv
  change (denominator (LocalField F q) ε z)⁻¹ * _ =
    (denominator (LocalField F q) ε z)⁻¹ * _
  exact congrArg ((denominator (LocalField F q) ε z)⁻¹ * ·) hv

 theorem tau_evaluate_smul (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (ε : Sign)
    (p : LevelLaurentOperator (LocalField F q) A P I J ε) (c : ℂ) (u : ℂˣ) :
    evaluate (LocalField F q) A P I J ε (c • p) u =
      c • evaluate (LocalField F q) A P I J ε p u := by
  unfold evaluate
  rw [Finsupp.sum_smul_index' (by intro; simp)]
  simp only [Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact smul_comm _ _ _

theorem tauLevelNumerator_smul_measure (I : IwasawaData A)
    (J : CompactOpenLevel (Cover F ζ hζ q)) (μ : Measure (LocalField F q)) (ε : Sign)
    (p : LevelLaurentOperator (LocalField F q) A P I J ε)
    (hp : IsLevelNumerator (LocalField F q) A P I J μ ε p) (c : ENNReal) :
    IsLevelNumerator (LocalField F q) A P I J (c • μ) ε ((c.toReal : ℂ) • p) := by
  intro z hz φ k h
  rw [tau_evaluate_smul]
  change (c.toReal : ℂ) * _ = _
  rw [hp z hz φ k h]
  unfold standardIntegralCoordinate
  rw [integral_smul_measure]
  change (c.toReal : ℂ) * (denominator (LocalField F q) ε z * _) =
    denominator (LocalField F q) ε z * ((c.toReal : ℂ) * _)
  ring

def tauStandardFamily_smul_measure (I : IwasawaData A) (μ : Measure (LocalField F q))
    (Jτ : TauStandardFamily F ζ hζ q T A P I μ) (c : ENNReal) (hc : c ≠ ⊤) :
    TauStandardFamily F ζ hζ q T A P I (c • μ) where
  op ε z := (c.toReal : ℂ) • Jτ.op ε z
  intertwining ε z hz g f := by
    simp only [LinearMap.smul_apply, Jτ.intertwining ε z hz, map_smul]
  numerators J hJ ε := by
    obtain ⟨p, hp, _⟩ := Jτ.numerators J hJ ε
    refine ⟨(c.toReal : ℂ) • p, tauLevelNumerator_smul_measure F ζ hζ q T A P I J μ ε p hp c, ?_⟩
    intro p' hp'
    exact level_numerator_unique (LocalField F q) A P I J (c • μ) ε p' _ hp'
      (tauLevelNumerator_smul_measure F ζ hζ q T A P I J μ ε p hp c)
  integral_eq ε z hz f g h := by
    refine ⟨(Jτ.integral_eq ε z hz f g h).1.smul_measure hc, ?_⟩
    rw [integral_smul_measure]
    change (c.toReal : ℂ) * _ = c.toReal • _
    rw [(Jτ.integral_eq ε z hz f g h).2]
    rfl
  shell_eq J ε p hp z hz φ := by
    obtain ⟨J', hJ', ψ, hψ⟩ := tauSection_has_compact_level F ζ hζ q T A P I
      (sourceSign ε) (sourceParameter ε z)
      (compactTrivialization A P I (sourceSign ε) (sourceParameter ε z) φ.val)
    obtain ⟨p', hp', _⟩ := Jτ.numerators J' hJ' ε
    have hv : ψ.val = φ.val := (compactTrivialization A P I
      (sourceSign ε) (sourceParameter ε z)).injective hψ
    rw [LinearMap.smul_apply, ← hψ, Jτ.shell_eq J' ε p' hp' z hz ψ]
    have he := tauContinuedLevel_compatible_any F ζ hζ q T A P I J' J (c • μ) ε
      ((c.toReal : ℂ) • p') p (tauLevelNumerator_smul_measure F ζ hζ q T A P I J' μ ε p' hp' c)
      hp ψ φ hv z
    rw [← he]
    unfold continuedLevel
    rw [tau_evaluate_smul]
    change (c.toReal : ℂ) •
      (compactTrivialization A P I (targetSign ε) (targetParameter ε z))
        ((denominator (LocalField F q) ε z)⁻¹ •
          (evaluate (LocalField F q) A P I J' ε p' (evaluationUnit (LocalField F q) ε z) ψ).val) =
      (compactTrivialization A P I (targetSign ε) (targetParameter ε z))
        ((denominator (LocalField F q) ε z)⁻¹ • (c.toReal : ℂ) •
          (evaluate (LocalField F q) A P I J' ε p' (evaluationUnit (LocalField F q) ε z) ψ).val)
    rw [map_smul, map_smul, map_smul]
    exact smul_comm _ _ _

end CompactCoefficientLevels

theorem center_profile_section_raw (B : Binding F ζ hζ q A P) (z : ℂ)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (v : CenterModule T) :
    ∃ f : centerSectionSpace F ζ hζ q T A .plus z,
      (∀ x, f.val (openCoordinate F ζ hζ q x) = φ x • v) ∧
      (∀ g : Cover F ζ hζ q,
        (¬ ∃ (b : A.B) (x : LocalField F q),
          g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q x) → f.val g = 0) := by
  have ht (t : InducedModule P ⊗[ℂ] Multiplicity T P) :
      ∃ f : centerSectionSpace F ζ hζ q T A .plus z,
        (∀ x, f.val (openCoordinate F ζ hζ q x) = φ x • centerCoefficientMap T P t) ∧
        (∀ g : Cover F ζ hζ q,
          (¬ ∃ (b : A.B) (x : LocalField F q),
            g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q x) → f.val g = 0) := by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul v ℓ =>
      obtain ⟨f, hf, _⟩ := (open_cell_correspondence F ζ hζ q A P B .plus z).2
        (fun x => φ x • v) (hφ.comp (fun c : ℂ => c • v))
        (hcφ.comp_left (g := fun c : ℂ => c • v) (by simp))
      refine ⟨centerTensorSection F ζ hζ q T A P .plus z f ℓ, ?_, ?_⟩
      · intro x
        change centerCoefficientMap T P (f.val (openCoordinate F ζ hζ q x) ⊗ₜ[ℂ] ℓ) = _
        rw [hf.2 x, ← TensorProduct.smul_tmul', map_smul]
      · intro g hg
        change centerCoefficientMap T P (f.val g ⊗ₜ[ℂ] ℓ) = _
        rw [hf.1.2 g hg, TensorProduct.zero_tmul, map_zero]
    | add t u ht hu =>
      obtain ⟨f, hf, hf0⟩ := ht
      obtain ⟨g, hg, hg0⟩ := hu
      refine ⟨f + g, ?_, ?_⟩
      · intro x
        change f.val _ + g.val _ = _
        rw [hf, hg, map_add, smul_add]
      · intro x hx
        change f.val x + g.val x = 0
        rw [hf0 x hx, hg0 x hx, add_zero]
  obtain ⟨t, rfl⟩ := centerCoefficientMap_surjective T P v
  exact ht t

theorem centerSection_open_cell_ext (ε : Sign) (z : ℂ)
    (f f' : centerSectionSpace F ζ hζ q T A ε z)
    (hval : ∀ x, f.val (openCoordinate F ζ hζ q x) =
      f'.val (openCoordinate F ζ hζ q x))
    (hf : ∀ g : Cover F ζ hζ q,
      (¬ ∃ (b : A.B) (x : LocalField F q),
        g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q x) → f.val g = 0)
    (hf' : ∀ g : Cover F ζ hζ q,
      (¬ ∃ (b : A.B) (x : LocalField F q),
        g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q x) → f'.val g = 0) :
    f = f' := by
  apply Subtype.ext
  funext g
  by_cases hg : ∃ (b : A.B) (x : LocalField F q),
      g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q x
  · obtain ⟨b, x, rfl⟩ := hg
    rw [f.property.1, f'.property.1, hval]
  · rw [hf g hg, hf' g hg]

theorem center_pure_coordinate_section (B : Binding F ζ hζ q A P)
    (rep : D → H) (hrep : ∀ d, T.π (rep d) = d) (d : D) (z : ℂ)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃! f : centerSectionSpace F ζ hζ q T A .plus z,
      (∀ x, centerCoordinates T rep hrep (f.val (openCoordinate F ζ hζ q x)) =
        φ x • Pi.single d 1) ∧
      (∀ g : Cover F ζ hζ q,
        (¬ ∃ (b : A.B) (x : LocalField F q),
          g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q x) → f.val g = 0) := by
  let e := centerCoordinates T rep hrep
  obtain ⟨f, hf, hf0⟩ := center_profile_section_raw F ζ hζ q T A P B z φ hφ hcφ
    (e.symm (Pi.single d 1))
  refine ⟨f, ⟨?_, hf0⟩, ?_⟩
  · intro x
    rw [hf x, map_smul, LinearEquiv.apply_symm_apply]
  · intro g hg
    apply centerSection_open_cell_ext F ζ hζ q T A .plus z g f
    · intro x
      apply e.injective
      exact (hg.1 x).trans (by rw [hf x, map_smul, LinearEquiv.apply_symm_apply])
    · exact hg.2
    · exact hf0

end
end DedekindZetaZeroFree.KPRankOneCenterInducedDiagonalComparison
