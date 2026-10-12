module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.OrdinaryBruhatCellFiltration
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TwistedOpenCellIsomorphism
public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInducingData
public import DedekindZetaZeroFree.Metaplectic.Torus.TameValuationCoordinates

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests.Raw

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

abbrev HL : Subgroup (actualTorus F ζ hζ q) := P.L.comap S.heisenberg.π

def IsTamePolarization : Prop :=
  P.L.map S.cubeClassEquiv.toMonoidHom =
    KPTameValuationCoordinates.unitCubeClasses (LocalField F q)

private theorem pgl_diagonal_injective (K : Type*) [Field K] (u v : Kˣ)
    (huv : Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K u 1) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K v 1)) : u = v := by
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp huv
  have h11 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 1) hc
  have h00 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.diagonal_apply] at h11 h00
  apply Units.ext
  calc
    (u : K) = (u : K) * (c : K) := by simp [h11]
    _ = (v : K) := h00

private theorem pgl_weyl_diagonal (K : Type*) [Field K] (u : Kˣ) :
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w K) *
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K u⁻¹ 1) =
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K u 1) *
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w K) := by
  rw [← map_mul, ← map_mul]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨u, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal_apply]

private theorem weyl_coordinate (h : actualTorus F ζ hζ q) :
    S.borel.coordinate (S.borel.weyl h) = (S.borel.coordinate h)⁻¹ := by
  apply pgl_diagonal_injective
  rw [← S.borel.torus_projection]
  rw [S.borel.weyl_from_lift, map_mul, map_mul, map_inv, S.borel.liftedW_projection,
    S.borel.torus_projection]
  apply mul_left_cancel (a := Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (LocalField F q)))
  simp only [← mul_assoc, mul_inv_cancel, one_mul]
  exact (pgl_weyl_diagonal (LocalField F q) (S.borel.coordinate h)).symm

theorem weyl_preserves_HL (hP : IsTamePolarization F ζ hζ q S P)
    (h : HL F ζ hζ q S P) :
    S.borel.weyl (h : actualTorus F ζ hζ q) ∈ HL F ζ hζ q S P := by
  have hm : S.cubeClassEquiv (S.heisenberg.π (h : actualTorus F ζ hζ q)) ∈
      KPTameValuationCoordinates.unitCubeClasses (LocalField F q) := by
    rw [← hP]
    exact ⟨S.heisenberg.π h, h.property, rfl⟩
  have hw : S.cubeClassEquiv (S.heisenberg.π (S.borel.weyl h)) =
      (S.cubeClassEquiv (S.heisenberg.π (h : actualTorus F ζ hζ q)))⁻¹ := by
    rw [S.cube_class, S.cube_class, weyl_coordinate F ζ hζ q S]
    exact map_inv (QuotientGroup.mk' _) _
  change S.heisenberg.π (S.borel.weyl h) ∈ P.L
  have hi := (KPTameValuationCoordinates.unitCubeClasses (LocalField F q)).inv_mem hm
  rw [← hw, ← hP] at hi
  obtain ⟨d, hd, he⟩ := hi
  exact S.cubeClassEquiv.injective he ▸ hd

def weylHL (hP : IsTamePolarization F ζ hζ q S P) :
    HL F ζ hζ q S P →* HL F ζ hζ q S P where
  toFun h := ⟨S.borel.weyl h, weyl_preserves_HL F ζ hζ q S P hP h⟩
  map_one' := Subtype.ext (map_one S.borel.weyl)
  map_mul' x y := Subtype.ext (map_mul S.borel.weyl
    (x : actualTorus F ζ hζ q) (y : actualTorus F ζ hζ q))

run_cmd Lean.Elab.Command.liftTermElabM do
  let name := ``DedekindZetaZeroFree.KPTameJacquetBruhatTests.Raw.weylHL
  let info ← Lean.getConstInfo name
  let _ ← Lean.Meta.mkCongrSimpForConst? name
    (info.levelParams.map Lean.Level.param)
  pure ()

def BL : Subgroup (ActualCover F ζ hζ q) :=
  ((HL F ζ hζ q S P).comap S.borel.retract).map S.borel.B.subtype

def inBorel (b : BL F ζ hζ q S P) : S.borel.B :=
  ⟨b, by
    obtain ⟨a, _, ha⟩ := b.property
    exact ha ▸ a.property⟩

def retractL (b : BL F ζ hζ q S P) : HL F ζ hζ q S P :=
  ⟨S.borel.retract (inBorel F ζ hζ q S P b), by
    obtain ⟨a, ha, he⟩ := b.property
    have he' : inBorel F ζ hζ q S P b = a := Subtype.ext he.symm
    rw [he']
    exact ha⟩

def chiH (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (h : HL F ζ hζ q S P) : ℂ :=
  (match ε with
    | .plus => (P.ωL h : ℂ)
    | .minus => (P.ωL (weylHL F ζ hζ q S P hP h) : ℂ)) *
    normPower (LocalField F q) (S.borel.coordinate h) (1 / 2)

def chi (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (b : BL F ζ hζ q S P) : ℂ :=
  chiH F ζ hζ q S P hP ε (retractL F ζ hζ q S P b)

def scalarSections (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) :
    Submodule ℂ (ActualCover F ζ hζ q → ℂ) where
  carrier := {f | (∀ (b : BL F ζ hζ q S P) (g : ActualCover F ζ hζ q),
    f ((b : ActualCover F ζ hζ q) * g) = chi F ζ hζ q S P hP ε b * f g) ∧
    SmoothVector rightTranslationRepresentation f}
  zero_mem' := ⟨by intros; simp, ⟨⊤, by intros; simp⟩⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, (mem_smoothSubmodule _ _).mp ((smoothSubmodule _).add_mem
      ((mem_smoothSubmodule _ _).mpr hf.2) ((mem_smoothSubmodule _ _).mpr hg.2))⟩
    intro b x
    simp only [Pi.add_apply, hf.1, hg.1, mul_add]
  smul_mem' := by
    intro c f hf
    refine ⟨?_, (mem_smoothSubmodule _ _).mp ((smoothSubmodule _).smul_mem c
      ((mem_smoothSubmodule _ _).mpr hf.2))⟩
    intro b x
    simp only [Pi.smul_apply, smul_eq_mul, hf.1]
    ring

 theorem scalarSections_stable
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) (g : ActualCover F ζ hζ q) :
    scalarSections F ζ hζ q S P hP ε ≤
      (scalarSections F ζ hζ q S P hP ε).comap (rightTranslationRepresentation g) := by
  intro f hf
  refine ⟨?_, (mem_smoothSubmodule _ _).mp (smoothSubmodule_stable _ g
    ((mem_smoothSubmodule _ _).mpr hf.2))⟩
  intro b x
  change f (((b : ActualCover F ζ hζ q) * x) * g) = _
  rw [mul_assoc, hf.1]
  rfl

def scalarAction (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) :
    Representation ℂ (ActualCover F ζ hζ q) (scalarSections F ζ hζ q S P hP ε) :=
  rightTranslationRepresentation.subrepresentation _
    (scalarSections_stable F ζ hζ q S P hP ε)

def eta (π : (LocalField F q)ˣ) (j : Fin 3) : ActualCover F ζ hζ q :=
  KPPGLLocalCover.A F ζ hζ (Sum.inr q) (π ^ j.val)

def expandingBall (π : (LocalField F q)ˣ) (r : ℕ) : Set (LocalField F q) :=
  {x | ∃ o : 𝒪[LocalField F q], x = ((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹ * o}

def jacquetIntegrand (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (a : ActualCover F ζ hζ q)
    (f : scalarSections F ζ hζ q S P hP ε) (x : LocalField F q) : ℂ :=
  f.val (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
    KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) *
    (ψ (Multiplicative.ofAdd (-x)) : ℂ)

run_cmd Lean.Elab.Command.liftTermElabM do
  let _ ← Lean.Meta.getEqnsFor?
    ``DedekindZetaZeroFree.KPTameJacquetBruhatTests.Raw.jacquetIntegrand
  pure ()

def HasStableValue (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q)) (a : ActualCover F ζ hζ q)
    (f : scalarSections F ζ hζ q S P hP ε) (z : ℂ) : Prop :=
  ∃ r₀ : ℕ, ∀ r ≥ r₀,
    IntegrableOn (jacquetIntegrand F ζ hζ q S P hP ε ψ a f)
      (expandingBall F q π r) μ ∧
    (∫ x in expandingBall F q π r,
      jacquetIntegrand F ζ hζ q S P hP ε ψ a f x ∂μ) = z

def HasConductorIntegers (ψ : Multiplicative (LocalField F q) →* ℂˣ) : Prop :=
  ∀ y : LocalField F q,
    (∀ x : 𝒪[LocalField F q], ψ (Multiplicative.ofAdd ((x : LocalField F q) * y)) = 1) ↔
      y ∈ (valuation (LocalField F q)).integer

def splitCongruenceSet (m : ℕ) : Set (ActualCover F ζ hζ q) :=
  Set.range (fun k : KPLocalCube.Gamma F q m =>
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val))

def rootLevelSet (m : ℕ) : Set (LocalField F q) :=
  {x | KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∈ splitCongruenceSet F ζ hζ q m}

def rootMass (μ : Measure (LocalField F q)) (m : ℕ) : ℝ :=
  (μ (rootLevelSet F ζ hζ q m)).toReal

def bruhatSupport (π : (LocalField F q)ˣ) (j : Fin 3) (m : ℕ) :
    Set (ActualCover F ζ hζ q) :=
  {g | ∃ (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q),
    k ∈ splitCongruenceSet F ζ hζ q m ∧
      g = b * eta F ζ hζ q π j * k * KPPGLLocalCover.W F ζ hζ (Sum.inr q)}

abbrev whittakerSpace (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) :=
  algebraicWhittaker (scalarAction F ζ hζ q S P hP ε)
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ

end DedekindZetaZeroFree.KPTameJacquetBruhatTests.Raw

end
