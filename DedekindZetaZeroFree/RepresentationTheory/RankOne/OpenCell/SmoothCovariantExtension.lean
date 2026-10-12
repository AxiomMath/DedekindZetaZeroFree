module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellKernelData
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.BruhatChartsAndCompactTransversal
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CovariantFunctionsWithCompactRepresentatives

@[expose] public section

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPRankOneBruhatKernelTransport
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

 def muMat (s : LocalField F q) : KubotaRankTwo.GL2 (LocalField F q) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, -s]
    (by simp [Matrix.det_fin_two])

private lemma weylMat_mul_muMat (s : LocalField F q) :
    (KubotaRankTwo.d (LocalField F q) (-1) 1 *
        KPStandardLocalRootLifts.weylSwap (LocalField F q)) * muMat F q s =
      KubotaRankTwo.n (LocalField F q) s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KubotaRankTwo.coe_n, KubotaRankTwo.coe_d, muMat,
      KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply]

private lemma proj_openCoordinate (B : Binding F ζ hζ q A P) (s : LocalField F q) :
    A.projection (openCoordinate F ζ hζ q s) =
      Matrix.ProjGenLinGroup.mk (muMat F q s) := by
  have hsw : A.projection (signedWeyl F ζ hζ q) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (LocalField F q) (-1) 1 *
          KPStandardLocalRootLifts.weylSwap (LocalField F q)) := by
    rw [signedWeyl, B.projection_eq]
    rfl
  have hinv : (KubotaRankTwo.d (LocalField F q) (-1) 1 *
        KPStandardLocalRootLifts.weylSwap (LocalField F q))⁻¹ *
      KubotaRankTwo.n (LocalField F q) s = muMat F q s := by
    rw [← weylMat_mul_muMat F q s]; group
  rw [openCoordinate, map_mul, map_inv, hsw]
  rw [nLift, KPPGLLocalCover.N, B.projection_eq]
  rw [show (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) s).g =
    KubotaRankTwo.n (LocalField F q) s from rfl]
  rw [← map_inv, ← map_mul, hinv]

theorem open_cell_decomposition_unique (B : Binding F ζ hζ q A P)
    (b₁ b₂ : A.B) (s₁ s₂ : LocalField F q)
    (h : (b₁ : Cover F ζ hζ q) * openCoordinate F ζ hζ q s₁ =
      (b₂ : Cover F ζ hζ q) * openCoordinate F ζ hζ q s₂) :
    b₁ = b₂ ∧ s₁ = s₂ := by

  obtain ⟨t₁, ht₁⟩ := A.borel_decomposition b₁
  obtain ⟨t₂, ht₂⟩ := A.borel_decomposition b₂
  have hb₁ : (b₁ : Cover F ζ hζ q) =
      (A.torus (A.retract b₁) : Cover F ζ hζ q) *
        (A.upperRoot t₁ : Cover F ζ hζ q) := congrArg Subtype.val ht₁
  have hb₂ : (b₂ : Cover F ζ hζ q) =
      (A.torus (A.retract b₂) : Cover F ζ hζ q) *
        (A.upperRoot t₂ : Cover F ζ hζ q) := congrArg Subtype.val ht₂

  have hp₁ : A.projection (b₁ : Cover F ζ hζ q) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (LocalField F q) (A.coordinate (A.retract b₁)) 1 *
          KubotaRankTwo.n (LocalField F q) (Multiplicative.toAdd t₁)) := by
    rw [hb₁, map_mul, A.torus_projection, A.upperRoot_projection, ← map_mul]
  have hp₂ : A.projection (b₂ : Cover F ζ hζ q) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (LocalField F q) (A.coordinate (A.retract b₂)) 1 *
          KubotaRankTwo.n (LocalField F q) (Multiplicative.toAdd t₂)) := by
    rw [hb₂, map_mul, A.torus_projection, A.upperRoot_projection, ← map_mul]

  have hproj : A.projection (b₁ : Cover F ζ hζ q) *
        A.projection (openCoordinate F ζ hζ q s₁) =
      A.projection (b₂ : Cover F ζ hζ q) *
        A.projection (openCoordinate F ζ hζ q s₂) := by
    rw [← map_mul, ← map_mul, h]
  rw [proj_openCoordinate F ζ hζ q A P B s₁, proj_openCoordinate F ζ hζ q A P B s₂,
    hp₁, hp₂, ← map_mul, ← map_mul] at hproj

  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hproj
  have h10 := congrArg (fun g : KubotaRankTwo.GL2 (LocalField F q) =>
      (g : Matrix (Fin 2) (Fin 2) (LocalField F q)) 1 0) hu
  have h11 := congrArg (fun g : KubotaRankTwo.GL2 (LocalField F q) =>
      (g : Matrix (Fin 2) (Fin 2) (LocalField F q)) 1 1) hu

  simp [Matrix.GeneralLinearGroup.coe_mul, muMat, KubotaRankTwo.coe_n,
    KubotaRankTwo.coe_d, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two] at h10 h11
  have hu1 : (u : LocalField F q) = 1 := by rw [h10]; simp
  have hs : s₁ = s₂ := by
    rw [hu1, mul_one] at h11
    exact h11
  refine ⟨?_, hs⟩
  have hx : openCoordinate F ζ hζ q s₁ = openCoordinate F ζ hζ q s₂ := by rw [hs]
  rw [hx] at h
  exact Subtype.ext (mul_right_cancel h)

end
end DedekindZetaZeroFree.KPRankOneBruhatKernelTransport

end

section

namespace DedekindZetaZeroFree.KPRankOneBruhatKernelTransport
noncomputable section
set_option autoImplicit false

theorem covariant_extension_of_unique_coordinates
    {G X V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (S : Subgroup G) (ρ : Representation ℂ S V) (c : X → G)
    (hunique : ∀ (b₁ b₂ : S) (x₁ x₂ : X),
      (b₁ : G) * c x₁ = (b₂ : G) * c x₂ → b₁ = b₂ ∧ x₁ = x₂)
    (φ : X → V) :
    ∃ f : G → V,
      (∀ (b : S) (g : G), f ((b : G) * g) = ρ b (f g)) ∧
      (∀ x, f (c x) = φ x) ∧
      (∀ g, (¬ ∃ (b : S) (x : X), g = (b : G) * c x) → f g = 0) := by
  classical

  have key : ∀ g, (∃ (b : S) (x : X), g = (b : G) * c x) →
      ∃ v : V, ∀ (b : S) (x : X), g = (b : G) * c x → v = ρ b (φ x) := by
    rintro g ⟨b₀, x₀, h₀⟩
    refine ⟨ρ b₀ (φ x₀), ?_⟩
    intro b x h
    obtain ⟨hb, hx⟩ := hunique b b₀ x x₀ (h.symm.trans h₀)
    simp only [hb, hx]
  let f : G → V := fun g =>
    if h : ∃ (b : S) (x : X), g = (b : G) * c x then (key g h).choose else 0
  refine ⟨f, ?_, ?_, ?_⟩
  ·
    intro b g
    by_cases hg : ∃ (b' : S) (x' : X), g = (b' : G) * c x'
    · obtain ⟨b', x', hx'⟩ := hg
      have hmem : ∃ (b' : S) (x' : X), g = (b' : G) * c x' := ⟨b', x', hx'⟩
      have h1 : f g = ρ b' (φ x') := by
        simp only [f, dif_pos hmem]
        exact (key g hmem).choose_spec b' x' hx'
      have hbg : ∃ (b'' : S) (x'' : X), (b : G) * g = (b'' : G) * c x'' :=
        ⟨b * b', x', by rw [hx', Subgroup.coe_mul]; group⟩
      have h2 : f ((b : G) * g) = ρ (b * b') (φ x') := by
        simp only [f, dif_pos hbg]
        exact (key ((b : G) * g) hbg).choose_spec (b * b') x'
          (by rw [hx', Subgroup.coe_mul]; group)
      rw [h1, h2, map_mul, Module.End.mul_apply]
    ·
      have hbg : ¬ ∃ (b'' : S) (x'' : X), (b : G) * g = (b'' : G) * c x'' := by
        rintro ⟨b'', x'', hx''⟩
        apply hg
        refine ⟨b⁻¹ * b'', x'', ?_⟩
        have h1 : (b : G) * g = (b : G) * (((b⁻¹ * b'' : S) : G) * c x'') := by
          rw [hx'', Subgroup.coe_mul, Subgroup.coe_inv]
          group
        exact mul_left_cancel h1
      simp only [f, dif_neg hg, dif_neg hbg, map_zero]
  · intro x
    have hc : ∃ (b : S) (x' : X), c x = (b : G) * c x' := ⟨1, x, by simp⟩
    simp only [f, dif_pos hc]
    rw [(key (c x) hc).choose_spec 1 x (by simp), map_one]
    simp
  · intro g hg
    simp only [f, dif_neg hg]

end
end DedekindZetaZeroFree.KPRankOneBruhatKernelTransport

end

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open scoped Topology
namespace DedekindZetaZeroFree.KPRankOneBruhatKernelTransport.OpenCellSmoothnessSteps
open KPJacquetBruhatCharts KPLocalSmoothRepresentation
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

private theorem localAbs_lc : IsLocallyConstant (fun y : (LocalField F q)ˣ => localAbs (LocalField F q) y) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  have he : {x : LocalField F q | valuation (LocalField F q) x = valuation (LocalField F q) (y : LocalField F q)} ∈ nhds (y : LocalField F q) := by
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨Units.mk0 (valuation (LocalField F q) (y : LocalField F q)) (by simp), ?_⟩
    rintro x ⟨t, ht, rfl⟩
    exact Valuation.map_eq_of_sub_lt _ (by simpa using ht)
  have hc := (Units.continuous_val (M := LocalField F q)).continuousAt (x := y)
  filter_upwards [hc.preimage_mem_nhds he] with x hx
  change valuation (LocalField F q) (x : LocalField F q) = valuation (LocalField F q) (y : LocalField F q) at hx
  simp only [localAbs, hx]

private theorem smooth_pullback {G V J : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (j : J →* G) (hj : Continuous j) :
    SmoothRepresentation (ρ.comp j) := by
  intro v
  obtain ⟨U, hU⟩ := hρ v
  refine ⟨U.comap j hj, ?_⟩
  intro x hx
  exact hU (j x) hx

private theorem inducingAction_smooth (ε : Sign) (z : ℂ) : SmoothRepresentation (inducingAction A P ε z) := by
  have hb : SmoothRepresentation (borelAction A P ε) := by
    cases ε
    · exact smooth_pullback (tau P) (tau_smooth T P) A.retract A.retract_continuous
    · exact smooth_pullback (tau P) (tau_smooth T P)
        (A.weyl.toMulEquiv.toMonoidHom.comp A.retract)
        (A.weyl.continuous.comp A.retract_continuous)
  let a : A.B →* ℂˣ := {
    toFun b := Units.mk0 (inducingScalar A z b) (by
      simp [inducingScalar, deltaHalf, normPower])
    map_one' := by
      apply Units.ext
      simpa [inducingScalar, deltaHalf, normPower, localAbs_one]
    map_mul' x y := by
      apply Units.ext
      simp only [Units.val_mk0, Units.val_mul, inducingScalar, deltaHalf]
      simp only [normPower, map_mul, localAbs_mul,
        Real.log_mul (ne_of_gt (localAbs_pos _ _)) (ne_of_gt (localAbs_pos _ _)),
        Complex.ofReal_add, mul_add, Complex.exp_add]
      ring }
  have ha : IsLocallyConstant a := by
    have hc := (localAbs_lc F q).comp_continuous
      (A.coordinate_continuous.comp A.retract_continuous)
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro b
    filter_upwards [hc.eventually_eq b] with c hc
    apply Units.ext
    change inducingScalar A z c = inducingScalar A z b
    change localAbs (LocalField F q) (A.coordinate (A.retract c)) = localAbs (LocalField F q) (A.coordinate (A.retract b)) at hc
    simp only [inducingScalar, deltaHalf, normPower, hc]
  let U : OpenSubgroup A.B := ⟨a.ker, ha.isOpen_fiber 1⟩
  intro v
  obtain ⟨J, hJ⟩ := hb v
  refine ⟨J ⊓ U, ?_⟩
  intro b hb
  have he : inducingScalar A z b = 1 := congrArg Units.val hb.2
  change inducingScalar A z b • borelAction A P ε b v = v
  rw [he, hJ b hb.1, one_smul]

private theorem kernel_mem (B : Binding F ζ hζ q A P) (g : Cover F ζ hζ q)
    (hg : A.projection g = 1) : g ∈ A.B := by
  induction g using QuotientGroup.induction_on with
  | _ g =>
    change A.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) = 1 at hg
    rw [B.projection_eq] at hg
    letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
    have he : Matrix.ProjGenLinGroup.mk g.g = Matrix.ProjGenLinGroup.mk 1 := by simpa using hg
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
    have he' : KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) = 1 := by
      change KPPGLLocalCover.baseQuotient F (Sum.inr q) g.g = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨u⁻¹, ?_⟩
      change Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ = g.g
      have hu' := congrArg (fun a => a * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹) hu
      simpa [← map_mul, mul_assoc] using hu'.symm
    have hm := he'
    rw [← MonoidHom.mem_ker, ← KPPGLLocalCover.range_centralInjection_eq_ker_projection] at hm
    obtain ⟨e, he⟩ := hm
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g ∈ A.B
    rw [← he, ← B.central_eq]
    exact (A.torus (B.centralTorus e)).property

private theorem torus_surj (B : Binding F ζ hζ q A P) (y : (LocalField F q)ˣ) :
    ∃ h : H, A.coordinate h = y := by
  refine ⟨(A.cubeLift y : H) * (B.rootTorus y)⁻¹, ?_⟩
  rw [map_mul, map_inv, A.cube_coordinate, B.coordinate_eq]
  group

private theorem projection_eq_concrete (B : Binding F ζ hζ q A P) :
    A.projection = KPLocalSmoothRepresentation.projection F ζ hζ q := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | _ g =>
    change A.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) = _
    rw [B.projection_eq]
    change _ = KPLocalSmoothRepresentation.ordinaryPGLMap F q
      (KPPGLLocalCover.baseQuotient F (Sum.inr q) g.g)
    rw [KPLocalSmoothRepresentation.ordinaryPGLMap]
    rfl

private theorem borel_eq (B : Binding F ζ hζ q A P) :
    A.B = KPLocalSmoothRepresentation.Borel F ζ hζ q := by
  apply le_antisymm
  · intro b hb
    obtain ⟨t, ht⟩ := A.borel_decomposition ⟨b, hb⟩
    have hb' := congrArg Subtype.val ht
    have hp : A.projection b = Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (LocalField F q) (A.coordinate (A.retract ⟨b, hb⟩)) 1 *
          KubotaRankTwo.n (LocalField F q) (Multiplicative.toAdd t)) := by
      calc
        A.projection b = A.projection _ := congrArg A.projection hb'
        _ = _ := by rw [Subgroup.coe_mul, map_mul, A.torus_projection, A.upperRoot_projection, ← map_mul]
    rw [projection_eq_concrete F ζ hζ q A P B] at hp
    refine ⟨_, hp.symm, ?_⟩
    simp [KubotaRankTwo.d, KubotaRankTwo.n, Units.val_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  · intro b hb
    obtain ⟨M, hM, h10⟩ := hb
    have hd := Matrix.GeneralLinearGroup.det_ne_zero M
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hd
    have ha : M 0 0 ≠ 0 := (mul_ne_zero_iff.mp hd).1
    have hh : M 1 1 ≠ 0 := (mul_ne_zero_iff.mp hd).2
    let y : (LocalField F q)ˣ := Units.mk0 (M 0 0 / M 1 1) (div_ne_zero ha hh)
    obtain ⟨h, he⟩ := torus_surj F ζ hζ q A P B y
    let b' : A.B := A.torus h * A.upperRoot (Multiplicative.ofAdd (M 0 1 / M 0 0))
    have hm : Matrix.ProjGenLinGroup.mk M = Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (LocalField F q) y 1 *
          KubotaRankTwo.n (LocalField F q) (M 0 1 / M 0 0)) := by
      apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
      refine ⟨(Units.mk0 (M 1 1) hh)⁻¹, ?_⟩
      apply Units.ext
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val,
        Units.val_mk0]
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [KubotaRankTwo.d, KubotaRankTwo.n, Units.val_mul, Matrix.mul_apply,
          Fin.sum_univ_two, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply,
          y, h10] <;> try field_simp [ha, hh]
    have hp : A.projection b = A.projection (b' : Cover F ζ hζ q) := by
      rw [projection_eq_concrete F ζ hζ q A P B] at ⊢
      rw [← hM, hm]
      rw [← projection_eq_concrete F ζ hζ q A P B]
      change _ = A.projection ((A.torus h : Cover F ζ hζ q) * _)
      simp only [map_mul, A.torus_projection, A.upperRoot_projection, he]
      rfl
    have hk : b * (b' : Cover F ζ hζ q)⁻¹ ∈ A.B :=
      kernel_mem F ζ hζ q A P B _ (by rw [map_mul, map_inv, hp, mul_inv_cancel])
    simpa using A.B.mul_mem hk b'.property

private theorem orbit_lc {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : SmoothRepresentation ρ) (v : V) :
    IsLocallyConstant (fun g => ρ g v) := by
  obtain ⟨J, hJ⟩ := hρ v
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{x | g⁻¹ * x ∈ J},
    J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using J.one_mem
  · intro x hx
    have he := congrArg (fun w => ρ g w) (hJ (g⁻¹ * x) hx)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using he

private theorem compact_avoids_inverse {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [T1Space K] {S : Set K} (hS : IsCompact S) :
    ∃ U : Set K, IsOpen U ∧ 0 ∈ U ∧ ∀ y ∈ U, ∀ x ∈ S, y * x ≠ 1 := by
  have hO : IsOpen {p : K × K | p.1 * p.2 ≠ 1} :=
    isClosed_singleton.isOpen_compl.preimage (continuous_fst.mul continuous_snd)
  obtain ⟨U, V, hU, hV, h0, hSV, hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : K))) hS hO
      (by rintro ⟨y, x⟩ ⟨hy, hx⟩; change y = 0 at hy; simp [hy])
  refine ⟨U, hU, h0 (Set.mem_singleton 0), ?_⟩
  intro y hy x hx
  exact hUV (show (y, x) ∈ U ×ˢ V from ⟨hy, hSV hx⟩)

private theorem chart_local_constancy
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (KPLocalSmoothRepresentation.Borel F ζ hζ q) E)
    (hρ : SmoothRepresentation ρ) (f : Cover F ζ hζ q → E)
    (hcov : ∀ (b : KPLocalSmoothRepresentation.Borel F ζ hζ q) g,
      f ((b : Cover F ζ hζ q) * g) = ρ b (f g))
    (hlc : IsLocallyConstant (fun x : LocalField F q =>
      f (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * nLift F ζ hζ q x)))
    (hcs : HasCompactSupport (fun x : LocalField F q =>
      f (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * nLift F ζ hζ q x)))
    (hclosed : ∀ b : KPLocalSmoothRepresentation.Borel F ζ hζ q, f b = 0) :
    IsLocallyConstant f := by
  let ψ := fun x : LocalField F q => f (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * nLift F ζ hζ q x)
  have hvalues (x : LocalField F q) : f (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * KPLocalSmoothRepresentation.upperRoot F ζ hζ q (Multiplicative.ofAdd x)) = ψ x := rfl
  let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
  have hm := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
  have hΩ := (charts_open_and_borel_closed F ζ hζ q m hm).1
  have hΔ := (charts_open_and_borel_closed F ζ hζ q m hm).2.1
  have hchart : IsLocallyConstant (fun p : Borel F ζ hζ q ×
      KPRankOneInduction.LocalField F q => f (omegaMap F ζ hζ q p).val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro p
    have hb := ((orbit_lc ρ hρ (ψ p.2)).comp_continuous
      continuous_fst).eventually_eq p
    have hx := (hlc.comp_continuous continuous_snd).eventually_eq p
    filter_upwards [hb, hx] with q0 hqb hqx
    change ψ q0.2 = ψ p.2 at hqx
    change ρ q0.1 (ψ p.2) =
      ρ p.1 (ψ p.2) at hqb
    change f (q0.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        upperRoot F ζ hζ q (Multiplicative.ofAdd q0.2)) = _
    rw [mul_assoc, hcov, hvalues]
    change ρ q0.1 (ψ q0.2) = _
    rw [hqx]
    change ρ q0.1 (ψ p.2) = _
    rw [hqb]
    change _ = f (p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        upperRoot F ζ hζ q (Multiplicative.ofAdd p.2))
    rw [mul_assoc, hcov, hvalues]
  exact (by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro g
    by_cases hg : g ∈ omega F ζ hζ q
    · let q0 : omega F ζ hζ q := ⟨g, hg⟩
      have hc : IsLocallyConstant (fun q0 : omega F ζ hζ q => f q0.val) := by
        have hh := hchart.comp_continuous
          (omegaHomeomorph F ζ hζ q m hm).symm.continuous
        have heq : (fun x : omega F ζ hζ q =>
            f (omegaMap F ζ hζ q ((omegaHomeomorph F ζ hζ q m hm).symm x)).val) =
            (fun x => f x.val) := by
          funext x
          exact congrArg (fun y : omega F ζ hζ q => f y.val)
            ((omegaHomeomorph F ζ hζ q m hm).apply_symm_apply x)
        simpa only [Function.comp_def, heq] using hh
      have he := hc.eventually_eq q0
      rw [← hΩ.isOpenEmbedding_subtypeVal.map_nhds_eq q0]
      exact he
    · have hgB : g ∈ Borel F ζ hζ q := by
        change g ∈ (Borel F ζ hζ q : Set (FiniteCover F ζ hζ q))
        rw [← omega_complement F ζ hζ q]; exact hg
      have hgΔ : g ∈ delta F ζ hζ q := by
        have hh := (charts_cover F ζ hζ q) ▸ Set.mem_univ g
        exact hh.resolve_left hg
      let q0 : delta F ζ hζ q := ⟨g, hgΔ⟩
      have hy0 : deltaCoordinate F ζ hζ q q0 = 0 :=
        (closed_cell_coordinate F ζ hζ q q0).mp hgB
      obtain ⟨U, hU, h0U, havoid⟩ := compact_avoids_inverse hcs
      have hy : Continuous (deltaCoordinate F ζ hζ q) :=
        (continuous_snd.comp (deltaHomeomorph F ζ hζ q m hm).symm.continuous)
      have he : ∀ᶠ r : delta F ζ hζ q in nhds q0,
          deltaCoordinate F ζ hζ q r ∈ U :=
        hy.continuousAt.preimage_mem_nhds (hy0 ▸ hU.mem_nhds h0U)
      have heq : ∀ᶠ r : delta F ζ hζ q in nhds q0, f r.val = f g := by
        filter_upwards [he] with r hr
        have hg0 : f g = 0 := hclosed ⟨g, hgB⟩
        rw [hg0]
        by_cases hrΩ : r.val ∈ omega F ζ hζ q
        · let s : omega F ζ hζ q := ⟨r.val, hrΩ⟩
          let p := (omegaHomeomorph F ζ hζ q m hm).symm s
          have hp : (omegaMap F ζ hζ q p).val = r.val :=
            congrArg Subtype.val ((omegaHomeomorph F ζ hζ q m hm).apply_symm_apply s)
          have hpx : p.2 = (deltaCoordinate F ζ hζ q r)⁻¹ :=
            (overlap_coordinates F ζ hζ q r.val hrΩ r.property).1
          have hxS : p.2 ∉ tsupport (ψ : KPRankOneInduction.LocalField F q → E) := by
            intro hxS
            have hn := havoid _ hr _ hxS
            rw [hpx, mul_inv_cancel₀
              (overlap_coordinates F ζ hζ q r.val hrΩ r.property).2.2] at hn
            exact hn rfl
          rw [← hp]
          change f (p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            upperRoot F ζ hζ q (Multiplicative.ofAdd p.2)) = 0
          rw [mul_assoc, hcov, hvalues]
          change ρ p.1 (ψ p.2) = 0
          rw [image_eq_zero_of_notMem_tsupport hxS, map_zero]
        · have hrB : r.val ∈ Borel F ζ hζ q := by
            change r.val ∈ (Borel F ζ hζ q : Set (FiniteCover F ζ hζ q))
            rw [← omega_complement F ζ hζ q]; exact hrΩ
          exact hclosed ⟨r.val, hrB⟩
      rw [← hΔ.isOpenEmbedding_subtypeVal.map_nhds_eq q0]
      exact heq)

theorem local_constancy_of_open_cell_data (B : Binding F ζ hζ q A P)
    (ε : Sign) (z : ℂ) (f : Cover F ζ hζ q → InducedModule P)
    (hcov : ∀ (b : A.B) (g : Cover F ζ hζ q),
      f ((b : Cover F ζ hζ q) * g) = inducingAction A P ε z b (f g))
    (hlc : IsLocallyConstant (fun s : LocalField F q =>
      f (openCoordinate F ζ hζ q s)))
    (hcs : HasCompactSupport (fun s : LocalField F q =>
      f (openCoordinate F ζ hζ q s)))
    (hoff : ∀ g : Cover F ζ hζ q,
      (¬ ∃ (b : A.B) (s : LocalField F q),
        g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q s) → f g = 0) :
    IsLocallyConstant f := by
  let CB := KPLocalSmoothRepresentation.Borel F ζ hζ q
  have hAB := borel_eq F ζ hζ q A P B
  let j : CB →* A.B := (MulEquiv.subgroupCongr hAB.symm).toMonoidHom
  have hj : Continuous j := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  let ρ := (inducingAction A P ε z).comp j
  have hρ : SmoothRepresentation ρ :=
    smooth_pullback _ (inducingAction_smooth F ζ hζ q A P ε z) j hj
  let c : Cover F ζ hζ q := KPPGLLocalCover.W F ζ hζ (Sum.inr q) * signedWeyl F ζ hζ q
  have hc : c ∈ A.B := by
    rw [hAB]
    have hp : KPLocalSmoothRepresentation.projection F ζ hζ q c =
        Matrix.ProjGenLinGroup.mk
          (KPStandardLocalRootLifts.weylSwap (LocalField F q) *
            (KubotaRankTwo.d (LocalField F q) (-1) 1 *
              KPStandardLocalRootLifts.weylSwap (LocalField F q))) := by
      rw [← projection_eq_concrete F ζ hζ q A P B]
      change A.projection (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * signedWeyl F ζ hζ q) = _
      rw [map_mul, signedWeyl, B.projection_eq]
      have hw : A.projection (KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
          Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap (LocalField F q)) := by
        exact B.projection_eq _
      rw [hw, ← map_mul]
      rfl
    refine ⟨_, hp.symm, ?_⟩
    simp [KubotaRankTwo.d, KPStandardLocalRootLifts.weylSwap, Units.val_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  let cb : A.B := ⟨c, hc⟩
  have hon (x : LocalField F q) :
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) * nLift F ζ hζ q x =
        c * openCoordinate F ζ hζ q x := by
    dsimp [c, openCoordinate]
    group
  have hvalues (x : LocalField F q) :
      f (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * nLift F ζ hζ q x) =
        inducingAction A P ε z cb (f (openCoordinate F ζ hζ q x)) := by
    rw [hon]
    exact hcov cb _
  apply chart_local_constancy F ζ hζ q ρ hρ f
  · intro b g
    exact hcov (j b) g
  · have hh := hlc.comp (inducingAction A P ε z cb)
    simpa only [Function.comp_def, ← hvalues] using hh
  · have hh := hcs.comp_left (g := inducingAction A P ε z cb) (map_zero _)
    simpa only [Function.comp_def, ← hvalues] using hh
  · intro b
    apply hoff
    rintro ⟨d, x, hx⟩
    have hp : (b : Cover F ζ hζ q) ∈ omega F ζ hζ q := by
      let d' : CB := ⟨(d : Cover F ζ hζ q) * c⁻¹,
        by change _ ∈ KPLocalSmoothRepresentation.Borel F ζ hζ q; rw [← hAB]; exact A.B.mul_mem d.property (A.B.inv_mem hc)⟩
      have hm := (omegaMap F ζ hζ q (d', x)).property
      have he : (omegaMap F ζ hζ q (d', x)).val = b := by
        change ((d : Cover F ζ hζ q) * c⁻¹) *
          KPPGLLocalCover.W F ζ hζ (Sum.inr q) * nLift F ζ hζ q x = _
        rw [mul_assoc, hon, hx]
        group
      exact he ▸ hm
    have hb : (b : Cover F ζ hζ q) ∈ (omega F ζ hζ q)ᶜ := by
      rw [omega_complement]
      exact b.property
    exact hb hp

end
end DedekindZetaZeroFree.KPRankOneBruhatKernelTransport.OpenCellSmoothnessSteps

end

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPRankOneBruhatKernelTransport.OpenCellSmoothnessSteps
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

theorem compact_representatives_of_open_cell_support (B : Binding F ζ hζ q A P)
    (ε : Sign) (z : ℂ) (f : Cover F ζ hζ q → InducedModule P)
    (hcov : ∀ (b : A.B) (g : Cover F ζ hζ q),
      f ((b : Cover F ζ hζ q) * g) = inducingAction A P ε z b (f g))
    (hcs : HasCompactSupport (fun s : LocalField F q =>
      f (openCoordinate F ζ hζ q s)))
    (hoff : ∀ g : Cover F ζ hζ q,
      (¬ ∃ (b : A.B) (s : LocalField F q),
        g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q s) → f g = 0) :
    ∃ C : Set (Cover F ζ hζ q), IsCompact C ∧
      ∀ g : Cover F ζ hζ q, f g ≠ 0 →
        ∃ (b : A.B) (c : Cover F ζ hζ q), c ∈ C ∧
          g = (b : Cover F ζ hζ q) * c := by
  classical

  have hcont : Continuous (openCoordinate F ζ hζ q) := by
    have hN : Continuous (nLift F ζ hζ q) := by
      letI := KPPGLLocalCover.finiteTopology F ζ hζ q
        (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)
      exact (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1
    show Continuous (fun s : LocalField F q => (signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q s)
    exact continuous_const.mul hN

  refine ⟨openCoordinate F ζ hζ q '' tsupport
    (fun s : LocalField F q => f (openCoordinate F ζ hζ q s)), ?_, ?_⟩
  · exact hcs.isCompact.image hcont
  · intro g hg
    by_cases h : ∃ (b : A.B) (s : LocalField F q),
        g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q s
    · obtain ⟨b, s, hs⟩ := h
      refine ⟨b, openCoordinate F ζ hζ q s, ⟨s, ?_, rfl⟩, hs⟩

      apply subset_closure
      rw [Function.mem_support]
      intro h0
      exact hg (by rw [hs, hcov b (openCoordinate F ζ hζ q s), h0, map_zero])
    · exact absurd (hoff g h) hg

end
end DedekindZetaZeroFree.KPRankOneBruhatKernelTransport.OpenCellSmoothnessSteps

end

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPRankOneBruhatKernelTransport
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

theorem open_cell_covariant_smooth (B : Binding F ζ hζ q A P)
    (ε : Sign) (z : ℂ) (f : Cover F ζ hζ q → InducedModule P)
    (hcov : ∀ (b : A.B) (g : Cover F ζ hζ q),
      f ((b : Cover F ζ hζ q) * g) = inducingAction A P ε z b (f g))
    (hlc : IsLocallyConstant (fun s : LocalField F q =>
      f (openCoordinate F ζ hζ q s)))
    (hcs : HasCompactSupport (fun s : LocalField F q =>
      f (openCoordinate F ζ hζ q s)))
    (hoff : ∀ g : Cover F ζ hζ q,
      (¬ ∃ (b : A.B) (s : LocalField F q),
        g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q s) → f g = 0) :
    SmoothVector vectorRightTranslation f := by
  have hlocal : IsLocallyConstant f :=
    OpenCellSmoothnessSteps.local_constancy_of_open_cell_data
      F ζ hζ q A P B ε z f hcov hlc hcs hoff
  obtain ⟨C, hC, hrep⟩ :=
    OpenCellSmoothnessSteps.compact_representatives_of_open_cell_support
      F ζ hζ q A P B ε z f hcov hcs hoff
  exact OpenCellSmoothnessSteps.covariant_smooth_of_compact_representatives
    A.B (inducingAction A P ε z) f hcov hlocal C hC hrep

end
end DedekindZetaZeroFree.KPRankOneBruhatKernelTransport

end

section
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPRankOneBruhatKernelTransport
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

theorem open_cell_extension (B : Binding F ζ hζ q A P) (ε : Sign) (z : ℂ)
    (φ : LocalField F q → InducedModule P)
    (hφlc : IsLocallyConstant φ) (hφcs : HasCompactSupport φ) :
    ∃ f : sectionSpace A P ε z,
      IsOpenCellSection F ζ hζ q A P ε z f ∧
        ∀ s, f.val (openCoordinate F ζ hζ q s) = φ s := by
  obtain ⟨f, hcov, hvalues, hoff⟩ :=
    covariant_extension_of_unique_coordinates A.B (inducingAction A P ε z)
      (openCoordinate F ζ hζ q)
      (fun b₁ b₂ s₁ s₂ h =>
        open_cell_decomposition_unique F ζ hζ q A P B b₁ b₂ s₁ s₂ h) φ
  have hrestriction : (fun s : LocalField F q =>
      f (openCoordinate F ζ hζ q s)) = φ := funext hvalues
  have hlc : IsLocallyConstant (fun s : LocalField F q =>
      f (openCoordinate F ζ hζ q s)) := hrestriction ▸ hφlc
  have hcs : HasCompactSupport (fun s : LocalField F q =>
      f (openCoordinate F ζ hζ q s)) := hrestriction ▸ hφcs
  have hsmooth := open_cell_covariant_smooth F ζ hζ q A P B ε z f
    hcov hlc hcs hoff
  refine ⟨⟨f, hcov, hsmooth⟩, ?_, hvalues⟩
  exact ⟨hcs, hoff⟩

end
end DedekindZetaZeroFree.KPRankOneBruhatKernelTransport

end
