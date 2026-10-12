module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.OpenCell.SmoothCovariantExtension
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.NonarchimedeanScaling
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalFieldInverseSubstitution

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPRankOneOpenCellKernel

open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

abbrev LocalField := q.adicCompletion F
abbrev Cover := KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)
abbrev RawCover := KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)

instance coverTopology : TopologicalSpace (Cover F ζ hζ q) :=
  KPPGLLocalCover.finiteTopology F ζ hζ q
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)

instance coverTopologicalGroup : IsTopologicalGroup (Cover F ζ hζ q) :=
  (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2.1

def signedWeylRaw : RawCover F ζ hζ q :=
  KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) *
    KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q)

theorem signedWeyl_matrix :
    (signedWeylRaw F ζ hζ q).g = KubotaRankTwo.w (LocalField F q) := by
  simp only [signedWeylRaw, KPLocalCover.mul_g, KPStandardLocalRootLifts.A,
    KPStandardLocalRootLifts.W, KPLocalCover.sectionMap_g]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KubotaRankTwo.coe_d, KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply]

theorem signedWeyl_eq_prescribed_signed :
    signedWeylRaw F ζ hζ q = KPStandardLocalRootLifts.signedW F ζ hζ (Sum.inr q) := by
  have hm : KubotaRankTwo.d (LocalField F q) (-1) 1 *
      KPStandardLocalRootLifts.weylSwap (LocalField F q) =
      KubotaRankTwo.w (LocalField F q) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.d, KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.w,
        Matrix.mul_apply]
  have hs : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
      (KubotaRankTwo.d (LocalField F q) (-1) 1)
      (KPStandardLocalRootLifts.weylSwap (LocalField F q)) = 1 := by
    simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, hm,
      KubotaRankTwo.X_w, KubotaRankTwo.X_d, KubotaRankTwo.det_d]
    have hX : KubotaRankTwo.X (LocalField F q)
        (KPStandardLocalRootLifts.weylSwap (LocalField F q)) = 1 := by
      apply Units.ext
      simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap]
    have hd : KubotaRankTwo.det (LocalField F q)
        (KPStandardLocalRootLifts.weylSwap (LocalField F q)) = -1 := by
      apply Units.ext
      simp [KubotaRankTwo.det, KPStandardLocalRootLifts.weylSwap, Matrix.det_fin_two]
    obtain ⟨hL, _, _, _, _, ha⟩ := KPHilbert.B3_laws F ζ hζ (Sum.inr q)
    have h1 (b) : KPHilbert.B3 F ζ hζ (Sum.inr q) 1 b = 1 := by
      have h := hL 1 1 b
      simp only [one_mul] at h
      exact mul_eq_left.mp h.symm
    simp only [hX, hd, one_div, inv_one, mul_one, h1, (ha (-1)).1,
      one_mul, one_pow]
  rw [signedWeylRaw, KPStandardLocalRootLifts.signedW, KPStandardLocalRootLifts.A,
    KPStandardLocalRootLifts.W, KPLocalCover.sectionMap_mul, hs, hm]
  simp only [map_one, one_mul]

def signedWeyl : Cover F ζ hζ q :=
  KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (signedWeylRaw F ζ hζ q)

def nLift (s : LocalField F q) : Cover F ζ hζ q :=
  KPPGLLocalCover.N F ζ hζ (Sum.inr q) s

def hLift (v : (LocalField F q)ˣ) : Cover F ζ hζ q :=
  KPPGLLocalCover.A F ζ hζ (Sum.inr q) (v ^ 2)

def bruhatLeft (v : (LocalField F q)ˣ) (s : LocalField F q) : RawCover F ζ hζ q :=
  (signedWeylRaw F ζ hζ q)⁻¹ *
    KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)) *
    (signedWeylRaw F ζ hζ q)⁻¹ * KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) s

def bruhatRight (v : (LocalField F q)ˣ) (s : LocalField F q) : RawCover F ζ hζ q :=
  KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) v⁻¹ *
    (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (v ^ 2) *
      KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
      (signedWeylRaw F ζ hζ q)⁻¹ *
      KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) (s + (v : LocalField F q)))

def kappa (v : (LocalField F q)ˣ) (s : LocalField F q) : rootsOfUnity 3 F :=
  (bruhatLeft F ζ hζ q v s).epsilon / (bruhatRight F ζ hζ q v s).epsilon

private theorem signed_bruhat_matrix_aux {L : Type*} [Field L] (v : Lˣ) (z : L) :
    (KubotaRankTwo.w L)⁻¹ * KubotaRankTwo.n L (-((v⁻¹ : Lˣ) : L)) *
        (KubotaRankTwo.w L)⁻¹ * KubotaRankTwo.n L z =
    Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹ *
      (KubotaRankTwo.d L (v ^ 2) 1 * KubotaRankTwo.n L ((v⁻¹ : Lˣ) : L) *
        (KubotaRankTwo.w L)⁻¹ * KubotaRankTwo.n L (z + (v : L))) := by
  have hw : (KubotaRankTwo.w L)⁻¹ =
      KubotaRankTwo.d L (-1) (-1) * KubotaRankTwo.w L := by
    rw [inv_eq_of_mul_eq_one_right]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.coe_d, KubotaRankTwo.coe_w, Matrix.mul_apply,
        Fin.sum_univ_two]
  let A : Matrix.GeneralLinearGroup (Fin 2) L :=
    (KubotaRankTwo.w L)⁻¹ * KubotaRankTwo.n L (-((v⁻¹ : Lˣ) : L)) *
      (KubotaRankTwo.w L)⁻¹ * KubotaRankTwo.n L z
  let B : Matrix.GeneralLinearGroup (Fin 2) L :=
    KubotaRankTwo.d L (v ^ 2) 1 * KubotaRankTwo.n L ((v⁻¹ : Lˣ) : L) *
      (KubotaRankTwo.w L)⁻¹ * KubotaRankTwo.n L (z + (v : L))
  change A = Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹ * B
  have key : Matrix.GeneralLinearGroup.scalar (Fin 2) v * A = B := by
    dsimp only [A, B]
    rw [hw]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.coe_d, KubotaRankTwo.coe_w, KubotaRankTwo.coe_n,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.scalar_apply] <;>
      field_simp <;> ring
  have h : A = Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹ *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) v * A) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [h, key]

theorem raw_bruhat_identity (v : (LocalField F q)ˣ) (s : LocalField F q) :
    bruhatLeft F ζ hζ q v s =
      KPLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v s) *
        bruhatRight F ζ hζ q v s := by
  have hg : (bruhatLeft F ζ hζ q v s).g = (bruhatRight F ζ hζ q v s).g := by
    simp only [bruhatLeft, bruhatRight, KPLocalCover.mul_g, KPLocalCover.inv_g,
      KPStandardLocalRootLifts.N, KPStandardLocalRootLifts.A,
      KPStandardLocalRootLifts.W, KPScalarSplitCentral.scalarHom,
      KPScalarSplitCentral.scalarLift, KPLocalCover.sectionMap_g]
    rw [signedWeyl_matrix F ζ hζ q]
    exact signed_bruhat_matrix_aux v s
  have he : (bruhatLeft F ζ hζ q v s).epsilon =
      (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v s) *
        bruhatRight F ζ hζ q v s).epsilon := by
    simp only [KPLocalCover.mul_epsilon, KPLocalCover.centralInjection_epsilon,
      KPLocalCover.centralInjection_g, KPLocalCover.sigmaTwo_one_left, mul_one]
    simp only [kappa]
    rw [div_mul_cancel]
  show KPLocalCover.CubicGL2Raw.mk (bruhatLeft F ζ hζ q v s).g
      (bruhatLeft F ζ hζ q v s).epsilon =
    KPLocalCover.CubicGL2Raw.mk
      (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v s) *
        bruhatRight F ζ hζ q v s).g
      (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v s) *
        bruhatRight F ζ hζ q v s).epsilon
  rw [KPLocalCover.CubicGL2Raw.mk.injEq]
  refine ⟨?_, ?_⟩
  · simpa only [KPLocalCover.mul_g, KPLocalCover.centralInjection_g, one_mul] using hg
  · exact he

theorem lifted_bruhat_identity (v : (LocalField F q)ˣ) (s : LocalField F q) :
    (signedWeyl F ζ hζ q)⁻¹ *
      nLift F ζ hζ q (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)) *
      (signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q s =
    KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v s) *
      hLift F ζ hζ q v *
      nLift F ζ hζ q ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
      (signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q (s + (v : LocalField F q)) := by
  have hz : (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) v))⁻¹ = 1 := by
    have h1 : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) v) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (show ∃ y, KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) y =
          KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) v from ⟨v, rfl⟩)
    rw [h1, inv_one]
  have h := congrArg (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q))
    (raw_bruhat_identity F ζ hζ q v s)
  rw [bruhatLeft, bruhatRight] at h
  simp only [map_mul, map_inv] at h
  rw [hz, one_mul] at h
  simpa only [signedWeyl, nLift, hLift, KPPGLLocalCover.centralInjection,
    KPPGLLocalCover.N, KPPGLLocalCover.A, MonoidHom.comp_apply, mul_assoc] using h

variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

structure Binding
    (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
    (P : Polarization T) where
  projection_eq : ∀ g : RawCover F ζ hζ q,
    A.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) =
      Matrix.ProjGenLinGroup.mk g.g
  weyl_eq : A.liftedW = signedWeyl F ζ hζ q
  upper_eq : ∀ s : LocalField F q,
    (A.upperRoot (Multiplicative.ofAdd s) : Cover F ζ hζ q) = nLift F ζ hζ q s
  rootTorus : (LocalField F q)ˣ → H
  torus_eq : ∀ v, (A.torus (rootTorus v) : Cover F ζ hζ q) = hLift F ζ hζ q v
  coordinate_eq : ∀ v, A.coordinate (rootTorus v) = v ^ 2
  centralTorus : rootsOfUnity 3 F → H
  central_eq : ∀ e, (A.torus (centralTorus e) : Cover F ζ hζ q) =
    KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e
  central_coordinate : ∀ e, A.coordinate (centralTorus e) = 1
  eta : rootsOfUnity 3 F →* ℂˣ
  eta_injective : Function.Injective eta
  genuine : ∀ (ε : Sign) e (V : InducedModule P),
    (borelAction A P ε) (A.torus (centralTorus e)) V = (eta e : ℂ) • V

variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

 def rawAliasOpenBruhatCellBinding (B : Binding F ζ hζ q A P) :
    KPRankOneBruhatKernelTransport.Binding F ζ hζ q A P where
  projection_eq := B.projection_eq
  weyl_eq := B.weyl_eq
  upper_eq := B.upper_eq
  rootTorus := B.rootTorus
  torus_eq := B.torus_eq
  coordinate_eq := B.coordinate_eq
  centralTorus := B.centralTorus
  central_eq := B.central_eq
  central_coordinate := B.central_coordinate
  eta := B.eta
  eta_injective := B.eta_injective
  genuine := B.genuine

def openCoordinate (s : LocalField F q) : Cover F ζ hζ q :=
  (signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q s

def IsOpenCellSection (ε : Sign) (z : ℂ) (f : sectionSpace A P ε z) : Prop :=
  HasCompactSupport (fun s : LocalField F q => f.val (openCoordinate F ζ hζ q s)) ∧
    ∀ g : Cover F ζ hζ q,
      (¬ ∃ (b : A.B) (s : LocalField F q), g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q s) →
      f.val g = 0

theorem open_cell_correspondence (B : Binding F ζ hζ q A P) (ε : Sign) (z : ℂ) :
    (∀ f : sectionSpace A P ε z, IsOpenCellSection F ζ hζ q A P ε z f →
      IsLocallyConstant (fun s => f.val (openCoordinate F ζ hζ q s))) ∧
    (∀ φ : LocalField F q → InducedModule P,
      IsLocallyConstant φ → HasCompactSupport φ →
      ∃! f : sectionSpace A P ε z,
        IsOpenCellSection F ζ hζ q A P ε z f ∧
          ∀ s, f.val (openCoordinate F ζ hζ q s) = φ s) := by
  constructor
  · intro f _
    have hl : IsLocallyConstant f.val := by
      obtain ⟨J, hJ⟩ := f.property.2
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have hc : Continuous (fun y : Cover F ζ hζ q => g⁻¹ * y) :=
        continuous_const.mul continuous_id
      have hmem : ∀ᶠ y : Cover F ζ hζ q in nhds g, g⁻¹ * y ∈ J :=
        hc.continuousAt.preimage_mem_nhds (by simpa using J.isOpen.mem_nhds J.one_mem)
      filter_upwards [hmem] with y hy
      have he := congrFun (hJ (g⁻¹ * y) hy) g
      simpa [vectorRightTranslation] using he
    apply hl.comp_continuous
    have hn : Continuous (nLift F ζ hζ q) := by
      have he : nLift F ζ hζ q = fun s =>
          (A.upperRoot (Multiplicative.ofAdd s) : Cover F ζ hζ q) := by
        funext s
        exact (B.upper_eq s).symm
      rw [he]
      exact continuous_subtype_val.comp (A.upperRoot_continuous.comp continuous_ofAdd)
    exact continuous_const.mul hn
  · intro φ hφlc hφcs
    obtain ⟨f, hf⟩ : ∃ f : sectionSpace A P ε z,
        IsOpenCellSection F ζ hζ q A P ε z f ∧
          ∀ s, f.val (openCoordinate F ζ hζ q s) = φ s := by
      exact KPRankOneBruhatKernelTransport.open_cell_extension F ζ hζ q A P
        (rawAliasOpenBruhatCellBinding F ζ hζ q A P B) ε z φ hφlc hφcs
    refine ⟨f, hf, ?_⟩
    intro f' hf'
    apply Subtype.ext
    funext g
    by_cases hg : ∃ (b : A.B) (s : LocalField F q),
        g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q s
    · obtain ⟨b, s, rfl⟩ := hg
      rw [f'.property.1, f.property.1, hf'.2, hf.2]
    · rw [hf'.1.2 g hg, hf.1.2 g hg]

end
end DedekindZetaZeroFree.KPRankOneOpenCellKernel
