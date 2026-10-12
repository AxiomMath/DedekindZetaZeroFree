module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TamePolarizationsAndTwistedCoinvariants
public import DedekindZetaZeroFree.Theta.Whittaker.TameValuationBases

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetTestDualityScalarization

open scoped NumberField Classical
open NumberField IsDedekindDomain
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetBruhatTests.Raw

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

theorem identity_evaluation_mem
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (f : sectionSpace S.borel P ε 0) :
    (fun g : ActualCover F ζ hζ q => (f.val g).val 1) ∈
      scalarSections F ζ hζ q S P hP ε := by
  change (∀ (b : BL F ζ hζ q S P) (g : ActualCover F ζ hζ q), (f.val ((b : ActualCover F ζ hζ q) * g)).val 1 =
    chi F ζ hζ q S P hP ε b * (f.val g).val 1) ∧ _
  constructor
  · intro b g
    have hc := congrArg (fun v : InducedModule P => v.val 1)
      (f.property.1 (inBorel F ζ hζ q S P b) g)
    change (f.val ((b : ActualCover F ζ hζ q) * g)).val 1 = _ at hc
    rw [hc]
    cases ε
    · change (inducingScalar S.borel 0 (inBorel F ζ hζ q S P b)) *
        (f.val g).val (1 * S.borel.retract (inBorel F ζ hζ q S P b)) = _
      rw [one_mul]
      have hv := (f.val g).property (retractL F ζ hζ q S P b) 1
      simp only [mul_one, retractL, weylHL, MonoidHom.coe_mk, OneHom.coe_mk] at hv
      rw [hv]
      simp [chi, chiH, inducingScalar, deltaHalf, normPower, retractL, weylHL]
      ring
    · change (inducingScalar S.borel 0 (inBorel F ζ hζ q S P b)) *
        (f.val g).val (1 * S.borel.weyl (S.borel.retract
          (inBorel F ζ hζ q S P b))) = _
      rw [one_mul]
      have hv := (f.val g).property
        (weylHL F ζ hζ q S P hP (retractL F ζ hζ q S P b)) 1
      simp only [mul_one, retractL, weylHL, MonoidHom.coe_mk, OneHom.coe_mk] at hv
      rw [hv]
      simp [chi, chiH, inducingScalar, deltaHalf, normPower, retractL, weylHL]
      ring
  · obtain ⟨J, hJ⟩ := f.property.2
    refine ⟨J, ?_⟩
    intro j hj
    funext g
    exact congrArg (fun v : InducedModule P => v.val 1)
      (congrFun (hJ j hj) g)

end DedekindZetaZeroFree.KPTameJacquetTestDualityScalarization

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetTestDualityScalarization

open scoped NumberField Classical
open NumberField IsDedekindDomain
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetBruhatTests.Raw

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

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

private theorem inv_weyl_preserves (hP : IsTamePolarization F ζ hζ q S P)
    (a : HL F ζ hζ q S P) :
    S.borel.weyl.symm (a : actualTorus F ζ hζ q) ∈ HL F ζ hζ q S P := by
  have hw : S.borel.coordinate (S.borel.weyl.symm (a : actualTorus F ζ hζ q)) =
      (S.borel.coordinate a)⁻¹ := by
    have hh := weyl_coordinate F ζ hζ q S (S.borel.weyl.symm (a : actualTorus F ζ hζ q))
    simpa using congrArg Inv.inv hh.symm
  have hm : S.cubeClassEquiv (S.heisenberg.π (a : actualTorus F ζ hζ q)) ∈
      KPTameValuationCoordinates.unitCubeClasses (LocalField F q) := by
    rw [← hP]
    exact ⟨S.heisenberg.π a, a.property, rfl⟩
  have he : S.cubeClassEquiv (S.heisenberg.π (S.borel.weyl.symm (a : actualTorus F ζ hζ q))) =
      (S.cubeClassEquiv (S.heisenberg.π (a : actualTorus F ζ hζ q)))⁻¹ := by
    rw [S.cube_class, S.cube_class, hw]
    exact map_inv (QuotientGroup.mk' _) _
  have hi := (KPTameValuationCoordinates.unitCubeClasses (LocalField F q)).inv_mem hm
  rw [← he, ← hP] at hi
  obtain ⟨d, hd, he⟩ := hi
  change S.heisenberg.π (S.borel.weyl.symm (a : actualTorus F ζ hζ q)) ∈ P.L
  exact S.cubeClassEquiv.injective he ▸ hd

 def twist (ε : Sign) : actualTorus F ζ hζ q ≃* actualTorus F ζ hζ q :=
  match ε with
  | .plus => MulEquiv.refl _
  | .minus => S.borel.weyl.symm.toMulEquiv

 def half (h : actualTorus F ζ hζ q) : ℂ :=
  normPower (LocalField F q) (S.borel.coordinate h) (1 / 2)

private theorem half_one : half F ζ hζ q S 1 = 1 := by
  simp [half, normPower, localAbs_one]

private theorem half_ne (h : actualTorus F ζ hζ q) : half F ζ hζ q S h ≠ 0 :=
  Complex.exp_ne_zero _

private theorem half_mul (x y : actualTorus F ζ hζ q) :
    half F ζ hζ q S (x * y) = half F ζ hζ q S x * half F ζ hζ q S y := by
  simp [half, normPower, map_mul, localAbs_mul,
    Real.log_mul (ne_of_gt (localAbs_pos (LocalField F q) _))
      (ne_of_gt (localAbs_pos (LocalField F q) _)), mul_add, Complex.exp_add]

 def torusBL (h : HL F ζ hζ q S P) : BL F ζ hζ q S P :=
  ⟨(S.borel.torus h : ActualCover F ζ hζ q),
    ⟨S.borel.torus h, by
      change S.borel.retract (S.borel.torus h) ∈ HL F ζ hζ q S P
      rw [S.borel.retract_torus]
      exact h.property, rfl⟩⟩

private theorem torusBL_retract (h : HL F ζ hζ q S P) :
    retractL F ζ hζ q S P (torusBL F ζ hζ q S P h) = h := by
  apply Subtype.ext
  change S.borel.retract (inBorel F ζ hζ q S P _) = _
  have he : inBorel F ζ hζ q S P (torusBL F ζ hζ q S P h) = S.borel.torus h :=
    Subtype.ext rfl
  rw [he, S.borel.retract_torus]

private theorem torus_cov (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (φ : scalarSections F ζ hζ q S P hP ε) (a : HL F ζ hζ q S P)
    (x : actualTorus F ζ hζ q) (g : ActualCover F ζ hζ q) :
    φ.val ((S.borel.torus (twist F ζ hζ q S ε (a * x)) : ActualCover F ζ hζ q) * g) =
    (P.ωL a : ℂ) * half F ζ hζ q S (twist F ζ hζ q S ε a) *
      φ.val ((S.borel.torus (twist F ζ hζ q S ε x) : ActualCover F ζ hζ q) * g) := by
  have hm : twist F ζ hζ q S ε (a : actualTorus F ζ hζ q) ∈ HL F ζ hζ q S P := by
    cases ε
    · exact a.property
    · exact inv_weyl_preserves F ζ hζ q S P hP a
  let a' : HL F ζ hζ q S P := ⟨twist F ζ hζ q S ε a, hm⟩
  have hh := φ.property.1 (torusBL F ζ hζ q S P a')
    ((S.borel.torus (twist F ζ hζ q S ε x) : ActualCover F ζ hζ q) * g)
  rw [chi, torusBL_retract] at hh
  have hc : chiH F ζ hζ q S P hP ε a' =
      (P.ωL a : ℂ) * half F ζ hζ q S (twist F ζ hζ q S ε a) := by
    cases ε
    · rfl
    · simp only [chiH]
      congr 1
      congr 1
      congr 1
      apply Subtype.ext
      exact S.borel.weyl.apply_symm_apply _
  rw [hc] at hh
  simpa only [map_mul, torusBL, a', Subgroup.coe_mul, mul_assoc] using hh

private theorem chiH_one (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) :
    chiH F ζ hζ q S P hP ε 1 = 1 := by
  cases ε <;> simp [chiH, normPower, localAbs_one]

private theorem borel_reduce (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (φ : scalarSections F ζ hζ q S P hP ε) (b : S.borel.B)
    (g : ActualCover F ζ hζ q) :
    φ.val ((b : ActualCover F ζ hζ q) * g) =
      φ.val ((S.borel.torus (S.borel.retract b) : ActualCover F ζ hζ q) * g) := by
  let d : S.borel.B := b * (S.borel.torus (S.borel.retract b))⁻¹
  have hd : S.borel.retract d = 1 := by
    simp [d, S.borel.retract_torus]
  let d' : BL F ζ hζ q S P := ⟨d, ⟨d, by
    change S.borel.retract d ∈ HL F ζ hζ q S P
    rw [hd]
    exact Subgroup.one_mem _, rfl⟩⟩
  have hre : retractL F ζ hζ q S P d' = 1 := by
    apply Subtype.ext
    exact hd
  have hh := φ.property.1 d'
    ((S.borel.torus (S.borel.retract b) : ActualCover F ζ hζ q) * g)
  rw [chi, hre, chiH_one, one_mul] at hh
  simpa only [d', d, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_assoc,
    inv_mul_cancel_right] using hh

 def liftValue (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (φ : scalarSections F ζ hζ q S P hP ε) (g : ActualCover F ζ hζ q)
    (x : actualTorus F ζ hζ q) : ℂ :=
  (half F ζ hζ q S (twist F ζ hζ q S ε x))⁻¹ *
    φ.val ((S.borel.torus (twist F ζ hζ q S ε x) : ActualCover F ζ hζ q) * g)

 theorem liftValue_mem (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (φ : scalarSections F ζ hζ q S P hP ε) (g : ActualCover F ζ hζ q) :
    liftValue F ζ hζ q S P hP ε φ g ∈ InducedModule P := by
  intro a x
  change liftValue F ζ hζ q S P hP ε φ g (a * x) =
    (P.ωL a : ℂ) * liftValue F ζ hζ q S P hP ε φ g x
  unfold liftValue
  rw [torus_cov, map_mul, half_mul]
  have ha := half_ne F ζ hζ q S (twist F ζ hζ q S ε a)
  field_simp

 def liftFiber (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (φ : scalarSections F ζ hζ q S P hP ε) (g : ActualCover F ζ hζ q) :
    InducedModule P :=
  ⟨liftValue F ζ hζ q S P hP ε φ g, liftValue_mem F ζ hζ q S P hP ε φ g⟩

private theorem liftFiber_cov (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (φ : scalarSections F ζ hζ q S P hP ε) (b : S.borel.B)
    (g : ActualCover F ζ hζ q) :
    liftFiber F ζ hζ q S P hP ε φ ((b : ActualCover F ζ hζ q) * g) =
      inducingAction S.borel P ε 0 b (liftFiber F ζ hζ q S P hP ε φ g) := by
  apply Subtype.ext
  funext x
  have hh := borel_reduce F ζ hζ q S P hP ε φ
    (S.borel.torus (twist F ζ hζ q S ε x) * b) g
  simp only [Subgroup.coe_mul, mul_assoc, map_mul, S.borel.retract_torus] at hh
  cases ε <;>
    change (half F ζ hζ q S _)⁻¹ * φ.val (_ * (b * g)) =
      (inducingScalar S.borel 0 b) * liftValue F ζ hζ q S P hP _ φ g _
  all_goals
    rw [hh]
    simp only [inducingScalar, deltaHalf, normPower, zero_mul, Complex.exp_zero, mul_one]
    change (half F ζ hζ q S _)⁻¹ * φ.val _ =
      half F ζ hζ q S (S.borel.retract b) * liftValue F ζ hζ q S P hP _ φ g _
    unfold liftValue
    simp only [twist, MulEquiv.refl_apply, map_mul,
      S.borel.weyl.symm_apply_apply, half_mul]
    have hw : S.borel.weyl.symm.toMulEquiv
        (S.borel.weyl.toMonoidHom (S.borel.retract b)) = S.borel.retract b :=
      S.borel.weyl.symm_apply_apply _
    try rw [hw]
    simp only [Subgroup.coe_mul, mul_assoc]
    field_simp [half_ne]

theorem scalar_section_lift
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (φ : scalarSections F ζ hζ q S P hP ε) :
    ∃ f : sectionSpace S.borel P ε 0,
      ∀ g : ActualCover F ζ hζ q, (f.val g).val 1 = φ.val g := by
  let f : ActualCover F ζ hζ q → InducedModule P :=
    liftFiber F ζ hζ q S P hP ε φ
  have hf : f ∈ sectionSpace S.borel P ε 0 := by
    refine ⟨liftFiber_cov F ζ hζ q S P hP ε φ, ?_⟩
    obtain ⟨J, hJ⟩ := φ.property.2
    refine ⟨J, ?_⟩
    intro j hj
    funext g
    apply Subtype.ext
    funext x
    have hh := congrFun (hJ j hj)
      ((S.borel.torus (twist F ζ hζ q S ε x) : ActualCover F ζ hζ q) * g)
    change φ.val (_ * j) = φ.val _ at hh
    change liftValue F ζ hζ q S P hP ε φ (g * j) x =
      liftValue F ζ hζ q S P hP ε φ g x
    unfold liftValue
    rw [← mul_assoc, hh]
  refine ⟨⟨f, hf⟩, ?_⟩
  intro g
  change liftValue F ζ hζ q S P hP ε φ g 1 = φ.val g
  simp [liftValue, half_one]

end DedekindZetaZeroFree.KPTameJacquetTestDualityScalarization

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetTestDualityScalarization

open scoped NumberField Classical
open NumberField IsDedekindDomain
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

theorem identity_evaluation_ext (ε : Sign)
    (f k : sectionSpace S.borel P ε 0)
    (h : ∀ g : ActualCover F ζ hζ q, (f.val g).val 1 = (k.val g).val 1) :
    f = k := by
  apply Subtype.ext
  funext g
  apply Subtype.ext
  funext x
  cases ε with
  | plus =>
    have he := h ((S.borel.torus x : ActualCover F ζ hζ q) * g)
    rw [f.property.1, k.property.1] at he
    change inducingScalar S.borel 0 (S.borel.torus x) *
        (f.val g).val (1 * S.borel.retract (S.borel.torus x)) =
      inducingScalar S.borel 0 (S.borel.torus x) *
        (k.val g).val (1 * S.borel.retract (S.borel.torus x)) at he
    simp only [S.borel.retract_torus, one_mul] at he
    apply mul_left_cancel₀ (a := inducingScalar S.borel 0 (S.borel.torus x)) _ he
    exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  | minus =>
    have he := h ((S.borel.torus (S.borel.weyl.symm x) : ActualCover F ζ hζ q) * g)
    rw [f.property.1, k.property.1] at he
    change inducingScalar S.borel 0 (S.borel.torus (S.borel.weyl.symm x)) *
        (f.val g).val (1 * S.borel.weyl (S.borel.retract (S.borel.torus (S.borel.weyl.symm x)))) =
      inducingScalar S.borel 0 (S.borel.torus (S.borel.weyl.symm x)) *
        (k.val g).val (1 * S.borel.weyl (S.borel.retract (S.borel.torus (S.borel.weyl.symm x)))) at he
    simp only [S.borel.retract_torus, S.borel.weyl.apply_symm_apply, one_mul] at he
    apply mul_left_cancel₀ (a := inducingScalar S.borel 0 (S.borel.torus (S.borel.weyl.symm x))) _ he
    exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

end DedekindZetaZeroFree.KPTameJacquetTestDualityScalarization

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open Raw

 def whittakerDualEquiv {K G V : Type*} [AddCommGroup K] [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (n : Multiplicative K →* G) (ψ : Multiplicative K →* ℂˣ) :
    Module.Dual ℂ (RootCoinvariants ρ n ψ) ≃ₗ[ℂ] algebraicWhittaker ρ n ψ := by
  let e : RootEquivariantMaps ρ n ψ ℂ ≃ₗ[ℂ] algebraicWhittaker ρ n ψ :=
    { toFun := fun L => ⟨L.val, by
        intro t f
        simpa only [smul_eq_mul] using L.property t f⟩
      invFun := fun L => ⟨L.val, by
        intro t f
        simpa only [smul_eq_mul] using L.property t f⟩
      left_inv := by intro L; rfl
      right_inv := by intro L; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact (rootCoinvariantsUniversalEquiv ρ n ψ ℂ).trans e

private theorem whittaker_bound_of_jacquet_bound {K G V : Type*} [AddCommGroup K]
    [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (n : Multiplicative K →* G) (ψ : Multiplicative K →* ℂˣ)
    (hfinite : FiniteDimensional ℂ (RootCoinvariants ρ n ψ))
    (hbound : Module.finrank ℂ (RootCoinvariants ρ n ψ) ≤ 3) :
    FiniteDimensional ℂ (algebraicWhittaker ρ n ψ) ∧
      Module.finrank ℂ (algebraicWhittaker ρ n ψ) ≤ 3 := by
  letI := hfinite
  let e := whittakerDualEquiv ρ n ψ
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, Subspace.dual_finrank_eq]
  exact hbound

 def whittakerPullback {K G V W : Type*} [AddCommGroup K] [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (n : Multiplicative K →* G) (ψ : Multiplicative K →* ℂˣ)
    (f : V →ₗ[ℂ] W) (hf : ∀ t v, f (ρ (n t) v) = σ (n t) (f v)) :
    algebraicWhittaker σ n ψ →ₗ[ℂ] algebraicWhittaker ρ n ψ where
  toFun L := ⟨L.val.comp f, by
    intro t v
    change L.val (f (ρ (n t) v)) = _
    rw [hf, L.property]
    rfl⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

private theorem whittakerPullback_injective {K G V W : Type*} [AddCommGroup K] [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (n : Multiplicative K →* G) (ψ : Multiplicative K →* ℂˣ)
    (f : V →ₗ[ℂ] W) (hf : ∀ t v, f (ρ (n t) v) = σ (n t) (f v))
    (hsurj : Function.Surjective f) : Function.Injective (whittakerPullback ρ σ n ψ f hf) := by
  intro L M h
  apply Subtype.ext
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := hsurj w
  exact congrArg (fun J : algebraicWhittaker ρ n ψ => J.val v) h

private theorem whittaker_bound_of_surjective {K G V W : Type*} [AddCommGroup K]
    [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (n : Multiplicative K →* G) (ψ : Multiplicative K →* ℂˣ)
    (f : V →ₗ[ℂ] W) (hf : ∀ t v, f (ρ (n t) v) = σ (n t) (f v))
    (hsurj : Function.Surjective f)
    (hfinite : FiniteDimensional ℂ (algebraicWhittaker ρ n ψ))
    (hbound : Module.finrank ℂ (algebraicWhittaker ρ n ψ) ≤ 3) :
    FiniteDimensional ℂ (algebraicWhittaker σ n ψ) ∧
      Module.finrank ℂ (algebraicWhittaker σ n ψ) ≤ 3 := by
  letI := hfinite
  let a := whittakerPullback ρ σ n ψ f hf
  have ha := whittakerPullback_injective ρ σ n ψ f hf hsurj
  exact ⟨Module.Finite.of_injective a ha,
    (LinearMap.finrank_le_finrank_of_injective ha).trans hbound⟩

private theorem uniformizer_exists (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : ∃ π : Kˣ,
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hx0 : x ≠ 0 := by
    intro h
    have hh := congrArg e hx
    apply WithZero.exp_ne_zero (a := (-1 : ℤ))
    simpa [h, e] using hh.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  change e (valuation K x) = _
  rw [hx, e.apply_symm_apply]

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

private theorem canonicalPolarization (hP : IsTamePolarization F ζ hζ q S P) :
    KPLocalTameValuationWhittakerBasis.IsCanonicalTamePolarization F ζ hζ q S P := by
  change P.L = _
  apply le_antisymm
  · intro d hd
    change S.cubeClassEquiv d ∈ KPTameValuationCoordinates.unitCubeClasses (LocalField F q)
    rw [← hP]
    exact ⟨d, hd, rfl⟩
  · intro d hd
    change S.cubeClassEquiv d ∈ KPTameValuationCoordinates.unitCubeClasses (LocalField F q) at hd
    rw [← hP] at hd
    obtain ⟨d', hd', he⟩ := hd
    exact S.cubeClassEquiv.injective he ▸ hd'

omit ζ hζ S P in
private theorem conductor_data
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hconductor : HasConductorIntegers F q ψ) :
    ψ ≠ 1 ∧ KPLocalTameValuationWhittakerBasis.ConductorIntegers F q π ψ := by
  have hn : (π : LocalField F q)⁻¹ ∉ (valuation (LocalField F q)).integer := by
    rw [Valuation.mem_integer_iff]
    intro h
    have he := (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.monotone h
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)⁻¹) ≤
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1 at he
    rw [map_one, map_inv₀, map_inv₀, hπ] at he
    norm_num at he
  have hnψ : ∃ x : 𝒪[LocalField F q],
      ψ (Multiplicative.ofAdd ((x : LocalField F q) * (π : LocalField F q)⁻¹)) ≠ 1 := by
    by_contra h
    push Not at h
    exact hn ((hconductor _).mp h)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := hnψ
    simp [h] at hx
  · intro x
    have ht := (hconductor 1).mpr (by simp)
    simpa using ht x
  · obtain ⟨x, hx⟩ := hnψ
    exact ⟨x, by simpa [div_eq_mul_inv] using hx⟩

omit ζ hζ S P in
 def integerCompacts : TopologicalSpace.PositiveCompacts (LocalField F q) where
  carrier := (valuation (LocalField F q)).integer
  isCompact' := by
    change IsCompact {x | valuation (LocalField F q) x ≤ 1}
    exact IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1
  interior_nonempty' := by
    have ho : IsOpen ((valuation (LocalField F q)).integer : Set (LocalField F q)) := by
      exact (valuation (LocalField F q)).isOpen_integer
    rw [ho.interior_eq]
    exact ⟨0, by simp⟩

private theorem whittaker_dimension_bound_of_scalarization
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hψ : Continuous ψ) (hconductor : HasConductorIntegers F q ψ) (ε : Sign)
    (e : sectionSpace S.borel P ε 0 ≃ₗ[ℂ] scalarSections F ζ hζ q S P hP ε)
    (he : ∀ (f : sectionSpace S.borel P ε 0) (g : ActualCover F ζ hζ q),
      (e f).val g = (f.val g).val 1) :
    FiniteDimensional ℂ (whittakerSpace F ζ hζ q S P hP ε ψ) ∧
      Module.finrank ℂ (whittakerSpace F ζ hζ q S P hP ε ψ) ≤ 3 := by
  letI : AddCommGroup (sectionSpace S.borel P ε 0) := Submodule.addCommGroup _
  letI : Module ℂ (sectionSpace S.borel P ε 0) := Submodule.module _
  obtain ⟨π, hπ⟩ := uniformizer_exists (LocalField F q)
  obtain ⟨hψne, hcond⟩ := conductor_data F q π hπ ψ hconductor
  let μ := Measure.addHaarMeasure (integerCompacts F q)
  have hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1 :=
    Measure.addHaarMeasure_self (K₀ := integerCompacts F q)
  obtain ⟨b, ell, hb⟩ := KPLocalTameValuationWhittakerBasis.actual_whittaker_dual_bases
    F ζ hζ q S P (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)
    htame (canonicalPolarization F ζ hζ q S P hP) π hπ ψ hψ hψne hcond μ hμ ε
  have hroot : S.borel.B.subtype.comp S.borel.upperRoot =
      KPLocalSmoothRepresentation.upperRoot F ζ hζ q := by
    ext t
    exact (S.openCell P).upper_eq t
  have hr : rootTwistedRepresentation (principalSeries S.borel P ε 0)
      (S.borel.B.subtype.comp S.borel.upperRoot) ψ =
      KPCoinvariants.twistedRepresentation ((principalSeries S.borel P ε 0).comp
        (S.borel.B.subtype.comp S.borel.upperRoot)) ψ := by
    apply DFunLike.ext
    intro t
    apply LinearMap.ext
    intro v
    change (↑(ψ t)⁻¹ : ℂ) • (principalSeries S.borel P ε 0
      ((S.borel.B.subtype.comp S.borel.upperRoot) t) v) =
        (ψ t : ℂ)⁻¹ • (principalSeries S.borel P ε 0
      ((S.borel.B.subtype.comp S.borel.upperRoot) t) v)
    rw [Units.val_inv_eq_inv_val]
  have hfin : FiniteDimensional ℂ (RootCoinvariants (principalSeries S.borel P ε 0)
      (S.borel.B.subtype.comp S.borel.upperRoot) ψ) := by
    change FiniteDimensional ℂ (Representation.Coinvariants
      (rootTwistedRepresentation (principalSeries S.borel P ε 0)
        (S.borel.B.subtype.comp S.borel.upperRoot) ψ))
    rw [hr]
    exact Module.Finite.of_basis b
  have hbound : Module.finrank ℂ (RootCoinvariants (principalSeries S.borel P ε 0)
      (S.borel.B.subtype.comp S.borel.upperRoot) ψ) ≤ 3 := by
    change Module.finrank ℂ (Representation.Coinvariants
      (rootTwistedRepresentation (principalSeries S.borel P ε 0)
        (S.borel.B.subtype.comp S.borel.upperRoot) ψ)) ≤ 3
    rw [hr, Module.finrank_eq_card_basis b]
    simp
  obtain ⟨hwfin, hwbound⟩ := whittaker_bound_of_jacquet_bound
    (principalSeries S.borel P ε 0) (S.borel.B.subtype.comp S.borel.upperRoot) ψ hfin hbound
  rw [hroot] at hwfin hwbound
  apply whittaker_bound_of_surjective (principalSeries S.borel P ε 0)
    (scalarAction F ζ hζ q S P hP ε) (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
    ψ e.toLinearMap _ e.surjective hwfin hwbound
  intro t f
  apply Subtype.ext
  funext x
  change (e (principalSeries S.borel P ε 0
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ q t) f)).val x = _
  rw [he]
  change (f.val (x * KPLocalSmoothRepresentation.upperRoot F ζ hζ q t)).val 1 =
    (e f).val (x * KPLocalSmoothRepresentation.upperRoot F ζ hζ q t)
  exact (he f _).symm

theorem whittaker_dimension_bound
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hψ : Continuous ψ) (hunitary : ∀ x, ‖(ψ x : ℂ)‖ = 1)
    (hconductor : HasConductorIntegers F q ψ) (ε : Sign) :
    FiniteDimensional ℂ (whittakerSpace F ζ hζ q S P hP ε ψ) ∧
      Module.finrank ℂ (whittakerSpace F ζ hζ q S P hP ε ψ) ≤ 3 := by
  let a : sectionSpace S.borel P ε 0 →ₗ[ℂ] scalarSections F ζ hζ q S P hP ε :=
    { toFun := fun f => ⟨fun g => (f.val g).val 1,
        KPTameJacquetTestDualityScalarization.identity_evaluation_mem
          F ζ hζ q S P hP ε f⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have ha : Function.Injective a := by
    intro f k h
    apply KPTameJacquetTestDualityScalarization.identity_evaluation_ext
      F ζ hζ q S P ε f k
    intro g
    exact congrArg (fun φ : scalarSections F ζ hζ q S P hP ε => φ.val g) h
  have hs : Function.Surjective a := by
    intro φ
    obtain ⟨f, hf⟩ := KPTameJacquetTestDualityScalarization.scalar_section_lift
      F ζ hζ q S P hP ε φ
    refine ⟨f, ?_⟩
    apply Subtype.ext
    funext g
    exact hf g
  let e := LinearEquiv.ofBijective a ⟨ha, hs⟩
  exact whittaker_dimension_bound_of_scalarization F ζ hζ q S P hP htame
    ψ hψ hconductor ε e (by intros; rfl)

end DedekindZetaZeroFree.KPTameJacquetBruhatTests

end

end
