module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPictureAndHolomorphicFixedSpaces
public import DedekindZetaZeroFree.Metaplectic.Kubota.GL2BruhatCoordinates
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.SubmodulesAndQuotients
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Cubic.NormalizedInductionWeights

@[expose] public section

namespace DedekindZetaZeroFree.KPLocalPrincipalSeries

open scoped Valued
open ValuativeRel KPLocalStoneVonNeumann

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

def residueCardinality : ℕ := Nat.card 𝓀[K]

def localAbs (y : Kˣ) : ℝ :=
  (residueCardinality K : ℝ) ^
    ((WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (y : K))) : ℤ) : ℝ)

private theorem residueCardinality_pos : 0 < (residueCardinality K : ℝ) := by
  exact_mod_cast Nat.card_pos

theorem localAbs_pos (y : Kˣ) : 0 < localAbs K y := by
  exact Real.rpow_pos_of_pos (residueCardinality_pos K) _

theorem localAbs_mul (x y : Kˣ) : localAbs K (x * y) = localAbs K x * localAbs K y := by
  unfold localAbs
  rw [Units.val_mul, map_mul, map_mul, WithZero.log_mul, Int.cast_add,
    Real.rpow_add (residueCardinality_pos K)]
  all_goals simp

theorem localAbs_one : localAbs K 1 = 1 := by
  simp [localAbs]

def normPower (y : Kˣ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log (localAbs K y) : ℂ))

theorem normPower_entire (y : Kˣ) : Differentiable ℂ (normPower K y) := by
  exact (differentiable_id.mul_const _).cexp

 theorem normPower_one (s : ℂ) : normPower K 1 s = 1 := by
  simp [normPower, localAbs_one]

 theorem normPower_mul (x y : Kˣ) (s : ℂ) :
    normPower K (x * y) s = normPower K x s * normPower K y s := by
  simp [normPower, localAbs_mul, Real.log_mul (ne_of_gt (localAbs_pos K x))
    (ne_of_gt (localAbs_pos K y)), mul_add, Complex.exp_add]

variable {K}
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]

structure LocalBorelData (T : LocalHeisenbergData H D) where
  B : Subgroup G
  projection : G →* Matrix.ProjGenLinGroup (Fin 2) K
  torus : H →* B
  torus_injective : Function.Injective torus
  torus_continuous : Continuous torus
  retract : B →* H
  retract_continuous : Continuous retract
  retract_torus : ∀ h : H, retract (torus h) = h
  upperRoot : Multiplicative K →* B
  upperRoot_continuous : Continuous upperRoot
  upperRoot_injective : Function.Injective upperRoot
  upperRoot_projection : ∀ t : Multiplicative K,
    projection (upperRoot t : G) = Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.n K (Multiplicative.toAdd t))
  retract_upperRoot : ∀ t : Multiplicative K, retract (upperRoot t) = 1
  borel_decomposition : ∀ b : B, ∃ t : Multiplicative K,
    b = torus (retract b) * upperRoot t
  coordinate : H →* Kˣ
  coordinate_continuous : Continuous coordinate
  torus_projection : ∀ h : H, projection (torus h : G) =
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K (coordinate h) 1)
  cubeLift : Kˣ →* T.C
  cube_coordinate : ∀ y : Kˣ, coordinate (cubeLift y : H) = y ^ 3
  exceptional_cube : ∀ y : Kˣ,
    (T.ω (cubeLift y) : ℂ) = normPower K (y ^ 3) (1 / 6)
  liftedW : G
  liftedW_projection : projection liftedW =
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w K)
  weyl : H ≃ₜ* H
  weyl_from_lift : ∀ h : H,
    (torus (weyl h) : G) = liftedW⁻¹ * (torus h : G) * liftedW
  weylCenter : T.C ≃* T.C
  weylCenter_coe : ∀ c : T.C, (weylCenter c : H) = weyl (c : H)
  weyl_cube : ∀ y : Kˣ, weylCenter (cubeLift y) = cubeLift y⁻¹

variable {T : LocalHeisenbergData H D}

def deltaHalf (A : LocalBorelData (K := K) (G := G) T) (b : A.B) : ℂ :=
  normPower K (A.coordinate (A.retract b)) (1 / 2)

def inducingScalar (A : LocalBorelData (K := K) (G := G) T)
    (s : ℂ) (b : A.B) : ℂ :=
  deltaHalf A b * normPower K (A.coordinate (A.retract b)) s

inductive Sign where
  | plus
  | minus
  deriving DecidableEq

def borelAction (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (ε : Sign) : Representation ℂ A.B (InducedModule P) :=
  match ε with
  | .plus => (tau P).comp A.retract
  | .minus => (weylConjugate P A.weyl).comp A.retract

def inducingAction (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (ε : Sign) (s : ℂ) :
    Representation ℂ A.B (InducedModule P) where
  toFun b := inducingScalar A s b • borelAction A P ε b
  map_one' := by simp [inducingScalar, deltaHalf, normPower_one]
  map_mul' x y := by
    ext v
    simp only [map_mul, inducingScalar, deltaHalf, normPower_mul,
      LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
    congr 1
    ring

theorem upperRoot_trivial (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (ε : Sign) (s : ℂ) (t : Multiplicative K)
    (v : InducedModule P) : inducingAction A P ε s (A.upperRoot t) v = v := by
  cases ε <;>
    simp [inducingAction, inducingScalar, deltaHalf, A.retract_upperRoot,
      normPower_one, borelAction]

def vectorRightTranslation {V : Type*} [AddCommGroup V] [Module ℂ V] :
    Representation ℂ G (G → V) where
  toFun g :=
    { toFun := fun f x => f (x * g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_assoc]

def sectionSpace (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (ε : Sign) (s : ℂ) :
    Submodule ℂ (G → InducedModule P) where
  carrier := {f | (∀ (b : A.B) (g : G),
    f ((b : G) * g) = inducingAction A P ε s b (f g)) ∧
    SmoothVector vectorRightTranslation f}
  zero_mem' := by
    exact ⟨by intro b g; simp, ⟨⊤, by simp⟩⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_⟩
    · intro b x
      simpa using congrArg₂ (· + ·) (hf.1 b x) (hg.1 b x)
    · exact (mem_smoothSubmodule _ _).mp ((smoothSubmodule _).add_mem
        ((mem_smoothSubmodule _ _).mpr hf.2) ((mem_smoothSubmodule _ _).mpr hg.2))
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · intro b x
      simpa using congrArg (c • ·) (hf.1 b x)
    · exact (mem_smoothSubmodule _ _).mp ((smoothSubmodule _).smul_mem c
        ((mem_smoothSubmodule _ _).mpr hf.2))

theorem sectionSpace_stable (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (ε : Sign) (s : ℂ) (g : G) :
    sectionSpace A P ε s ≤ Submodule.comap (vectorRightTranslation g)
      (sectionSpace A P ε s) := by
  intro f hf
  refine ⟨?_, ?_⟩
  · intro b x
    change f (((b : G) * x) * g) = inducingAction A P ε s b (f (x * g))
    rw [mul_assoc, hf.1 b (x * g)]
  · exact (mem_smoothSubmodule _ _).mp (smoothSubmodule_stable _ g
      ((mem_smoothSubmodule _ _).mpr hf.2))

def principalSeries (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (ε : Sign) (s : ℂ) :
    Representation ℂ G (sectionSpace A P ε s) :=
  vectorRightTranslation.subrepresentation (sectionSpace A P ε s)
    (sectionSpace_stable A P ε s)

abbrev IPlus (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T) :=
  principalSeries A P .plus 0

abbrev IMinus (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T) :=
  principalSeries A P .minus 0

theorem principalSeries_smooth (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (ε : Sign) (s : ℂ) :
    SmoothRepresentation (V := sectionSpace A P ε s) (principalSeries A P ε s) := by
  intro f
  obtain ⟨J, hJ⟩ := f.property.2
  exact ⟨J, fun j hj => Subtype.ext (hJ j hj)⟩

theorem uniformizer_weights (A : LocalBorelData (K := K) (G := G) T)
    (π : Kˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ)) :
    (T.ω (A.cubeLift π) : ℂ) = (((residueCardinality K : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) ∧
    deltaHalf A (A.torus (A.cubeLift π : H)) =
      (((residueCardinality K : ℝ) ^ (-3 / 2 : ℝ) : ℝ) : ℂ) ∧
    (T.ω (A.weylCenter (A.cubeLift π)) : ℂ) =
      (((residueCardinality K : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  have hp : localAbs K π = (residueCardinality K : ℝ) ^ (-1 : ℝ) := by
    simp [localAbs, hπ]
  have hinv (y : Kˣ) : localAbs K y⁻¹ = (localAbs K y)⁻¹ := by
    have hm := localAbs_mul K y y⁻¹
    simp only [mul_inv_cancel, localAbs_one] at hm
    exact eq_inv_of_mul_eq_one_right hm.symm
  have hpow := KPLocalPrincipalSeriesNormWeights.absolute_pow (localAbs K)
    (localAbs_one K) (localAbs_mul K)
  have weights := KPLocalPrincipalSeriesNormWeights.cube_weights (residueCardinality_pos K)
  constructor
  · rw [A.exceptional_cube]
    simpa [normPower, hpow, hp] using weights.1
  constructor
  · simpa [deltaHalf, A.retract_torus, A.cube_coordinate, normPower, hpow, hp]
      using weights.2.1
  · rw [A.weyl_cube, A.exceptional_cube]
    simpa [normPower, hpow, hinv, hp] using weights.2.2

structure IwasawaData (A : LocalBorelData (K := K) (G := G) T) where
  compact : CompactOpenLevel G
  borelPart : G → A.B
  compactPart : G → compact.toOpenSubgroup
  decomposition : ∀ g : G, g = (borelPart g : G) * (compactPart g : G)
  borelPart_compact : ∀ k : compact.toOpenSubgroup, borelPart (k : G) = 1
  compactPart_compact : ∀ k : compact.toOpenSubgroup, compactPart (k : G) = k
  intersection_norm : ∀ b : A.B, (b : G) ∈ compact.toOpenSubgroup →
    localAbs K (A.coordinate (A.retract b)) = 1

omit [IsTopologicalGroup G] in
 theorem intersection_action (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign) (s : ℂ)
    (b : A.B) (hb : (b : G) ∈ I.compact.toOpenSubgroup) :
    inducingAction A P ε s b = inducingAction A P ε 0 b := by
  ext v
  simp [inducingAction, inducingScalar, deltaHalf, normPower,
    I.intersection_norm b hb]

 def compactLaws (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign) (s : ℂ) :=
  KPLocalPrincipalSeriesRaw.fixed_iwasawa_laws A.B I.compact.toOpenSubgroup
    (inducingAction A P ε 0) (inducingAction A P ε s) I.borelPart I.compactPart
    I.decomposition I.borelPart_compact I.compactPart_compact
    (intersection_action A P I ε s)

def compactPicture (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign) :
    Submodule ℂ (I.compact.toOpenSubgroup → InducedModule P) where
  carrier := {φ | (∀ (b : A.B) (k k' : I.compact.toOpenSubgroup),
    (k' : G) = (b : G) * (k : G) →
    φ k' = inducingAction A P ε 0 b (φ k)) ∧
    SmoothVector (vectorRightTranslation (G := I.compact.toOpenSubgroup)) φ}
  zero_mem' := by
    exact ⟨by intro b k k' h; simp, ⟨⊤, by simp⟩⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_⟩
    · intro b k k' h
      simpa using congrArg₂ (· + ·) (hf.1 b k k' h) (hg.1 b k k' h)
    · exact (mem_smoothSubmodule _ _).mp ((smoothSubmodule _).add_mem
        ((mem_smoothSubmodule _ _).mpr hf.2) ((mem_smoothSubmodule _ _).mpr hg.2))
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · intro b k k' h
      simpa using congrArg (c • ·) (hf.1 b k k' h)
    · exact (mem_smoothSubmodule _ _).mp ((smoothSubmodule _).smul_mem c
        ((mem_smoothSubmodule _ _).mpr hf.2))

def extendCompact (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign) (s : ℂ) :
    compactPicture A P I ε →ₗ[ℂ] sectionSpace A P ε s where
  toFun φ := ⟨fun g => inducingAction A P ε s (I.borelPart g) (φ.val (I.compactPart g)),
    (compactLaws A P I ε s).2.2.2.1 φ.val φ.property⟩
  map_add' := by intros; apply Subtype.ext; funext g; simp
  map_smul' := by intros; apply Subtype.ext; funext g; simp

def restrictCompact (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign) (s : ℂ) :
    sectionSpace A P ε s →ₗ[ℂ] compactPicture A P I ε where
  toFun f := ⟨fun k => f.val (k : G),
    (compactLaws A P I ε s).2.2.2.2.1 f.val f.property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def compactTrivialization (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign) (s : ℂ) :
    compactPicture A P I ε ≃ₗ[ℂ] sectionSpace A P ε s where
  toLinearMap := extendCompact A P I ε s
  invFun := restrictCompact A P I ε s
  left_inv := by
    intro φ
    apply Subtype.ext
    exact (compactLaws A P I ε s).2.2.2.2.2.1 φ.val
  right_inv := by
    intro f
    apply Subtype.ext
    exact (compactLaws A P I ε s).2.2.2.2.2.2.1 f.val f.property

def compactLevel (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel G) : Submodule ℂ (compactPicture A P I ε) where
  carrier := {φ | ∀ (j : J.toOpenSubgroup) (k k' : I.compact.toOpenSubgroup),
    (k' : G) = (k : G) * (j : G) → φ.val k' = φ.val k}
  zero_mem' := by intro j k k' h; rfl
  add_mem' := by
    intro f g hf hg j k k' h
    exact congrArg₂ (· + ·) (hf j k k' h) (hg j k k' h)
  smul_mem' := by
    intro c f hf j k k' h
    exact congrArg (c • ·) (hf j k k' h)

theorem compact_level_identification (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel G)
    (hJ : (J.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup)
    (s : ℂ) (φ : compactPicture A P I ε) :
    φ ∈ compactLevel A P I ε J ↔
      compactTrivialization A P I ε s φ ∈
        fixedSubmodule (principalSeries A P ε s) J.toOpenSubgroup := by
  change KPLocalPrincipalSeriesRaw.CompactFixed I.compact.toOpenSubgroup J.toOpenSubgroup φ.val ↔ _
  rw [(compactLaws A P I ε s).2.2.2.2.2.2.2 J.toOpenSubgroup hJ φ.val φ.property]
  constructor
  · intro hh j
    apply Subtype.ext
    exact hh j
  · intro hh j
    exact congrArg Subtype.val (hh j)

 def coordinateEvaluation (P : Polarization T) (h : H) :
    InducedModule P →ₗ[ℂ] ℂ where
  toFun v := v.val h
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

 theorem inducing_coordinate_entire
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (ε : Sign) (h : H) (b : A.B) (v : InducedModule P) :
    Differentiable ℂ (fun s => coordinateEvaluation P h (inducingAction A P ε s b v)) := by
  have hh := ((normPower_entire K (A.coordinate (A.retract b))).const_mul
    (deltaHalf A b)).mul_const ((borelAction A P ε b v).val h)
  change Differentiable ℂ (fun s =>
    (deltaHalf A b * normPower K (A.coordinate (A.retract b)) s) *
      (borelAction A P ε b v).val h)
  exact hh

 def compactFiniteLaws (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel G)
    (hJ : (J.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup) (h : H) :=
  letI := tau_moduleFinite T P
  KPLocalPrincipalSeriesRaw.finite_level_and_holomorphic A.B
    I.compact.toOpenSubgroup J.toOpenSubgroup (inducingAction A P ε 0)
    I.compact.isCompact hJ (inducingAction A P ε) I.borelPart I.compactPart
    (coordinateEvaluation P h) (inducing_coordinate_entire A P ε h)

theorem compact_level_finite (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel G)
    (hJ : (J.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup) :
    Module.Finite ℂ (compactLevel A P I ε J) := by
  let ev : compactLevel A P I ε J →ₗ[ℂ]
      KPLocalPrincipalSeriesRaw.compactFixedSpace A.B I.compact.toOpenSubgroup
        J.toOpenSubgroup (inducingAction A P ε 0) :=
    { toFun := fun φ => ⟨φ.val.val, φ.val.property, φ.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hev : Function.Injective ev := by
    intro φ ψ hh
    change (⟨φ.val.val, φ.val.property, φ.property⟩ :
      KPLocalPrincipalSeriesRaw.compactFixedSpace A.B I.compact.toOpenSubgroup
        J.toOpenSubgroup (inducingAction A P ε 0)) =
      ⟨ψ.val.val, ψ.val.property, ψ.property⟩ at hh
    have he := congrArg (fun f : KPLocalPrincipalSeriesRaw.compactFixedSpace A.B
      I.compact.toOpenSubgroup J.toOpenSubgroup (inducingAction A P ε 0) => f.val) hh
    exact Subtype.ext (Subtype.ext he)
  exact (compactFiniteLaws A P I ε J hJ 1).1 ev hev

theorem compact_level_holomorphic (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (ε : Sign)
    (J : CompactOpenLevel G)
    (hJ : (J.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup)
    (φ : compactLevel A P I ε J) (g x : G) (h : H) :
    Differentiable ℂ (fun s : ℂ =>
      (principalSeries A P ε s g
        (compactTrivialization A P I ε s (φ : compactPicture A P I ε))).val x |>.val h) := by
  exact (compactFiniteLaws A P I ε J hJ h).2
    ⟨φ.val.val, φ.val.property, φ.property⟩ g x

end

end DedekindZetaZeroFree.KPLocalPrincipalSeries
