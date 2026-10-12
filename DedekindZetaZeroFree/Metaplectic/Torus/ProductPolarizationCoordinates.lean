module

public import DedekindZetaZeroFree.Metaplectic.Torus.LocalPolarizationsAndCharacterExtensions

@[expose] public section

section
open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ProductPolarization
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology localCoverTopology

def restrictedM (P : CompatibleLocalData F ζ hζ) :
    Subgroup (KPGlobalCubicIdelePairing.RestrictedClasses F) where
  carrier := {x | ∀ v, x v ∈ (P.localData v).L}
  one_mem' := by intro v; exact (P.localData v).L.one_mem
  mul_mem' := by intro x y hx hy v; exact (P.localData v).L.mul_mem (hx v) (hy v)
  inv_mem' := by intro x hx v; exact (P.localData v).L.inv_mem (hx v)

def M (P : CompatibleLocalData F ζ hζ) : Subgroup (D F) :=
  (restrictedM F ζ hζ P).comap (KPGlobalCubicIdelePairing.classComparison F)

def pD : E F ζ hζ →* D F :=
  (QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalCenterRationalCharacter.Ideles F))).comp
    (KPGlobalTorusFunctionData.p F ζ hζ)

def B (P : CompatibleLocalData F ζ hζ) : Subgroup (E F ζ hζ) :=
  (M F ζ hζ P).comap (pD F ζ hζ)

def J (P : CompatibleLocalData F ζ hζ) : Subgroup (D F) :=
  KPGlobalPrincipalCubicLagrangian.A F ⊓ M F ζ hζ P

def rawB (P : CompatibleLocalData F ζ hζ) :
    Subgroup (KPGlobalCenterRationalCharacter.Raw F ζ hζ) :=
  ((B F ζ hζ P).map (E F ζ hζ).subtype).comap
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

 theorem diagonal_formula (t : KPGlobalTorusFunctionData.ordinaryTorus F) :
    KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.torusRatio F t) = t.val := by
  let A := Classical.choose t.property
  have hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = t.val ∧
      A 1 0 = 0 ∧ A 0 1 = 0 := Classical.choose_spec t.property
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).1.unit
  let w := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).2.unit
  have hu : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 0 0 := IsUnit.unit_spec _
  have hw : (w : KPAdelicCoverRestrictedProduct.Adeles F) = A 1 1 := IsUnit.unit_spec _
  have heq : A = KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, hu, hA.2.1, hA.2.2]
    exact hw.symm
  change QuotientGroup.mk' _ (KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹)) = t.val
  rw [← hA.1, heq]
  have hs : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) w) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
  rw [(QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).map_mul, hs, mul_one]
 def torusPullbackBridge : E F ζ hζ →* KPGlobalCubicIdelePairing.E F ζ hζ where
  toFun e := ⟨(e.val, KPGlobalTorusFunctionData.p F ζ hζ e),
    (diagonal_formula F ⟨_, e.property⟩).symm⟩
  map_one' := by apply Subtype.ext; exact Prod.ext rfl (map_one _)
  map_mul' x y := by apply Subtype.ext; exact Prod.ext rfl (map_mul _ _ _)

private theorem torusPullbackBridge_injective :
    Function.Injective (torusPullbackBridge F ζ hζ) := by
  intro x y h
  exact Subtype.ext (congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1) h)

private theorem commute_iff_beta (x y : E F ζ hζ) :
    Commute x y ↔ KPGlobalCubicIdelePairing.beta3 F ζ hζ
      (pD F ζ hζ x) (pD F ζ hζ y) = 1 := by
  have h := KPGlobalCubicIdelePairing.commutator_annihilators F ζ hζ
    (torusPullbackBridge F ζ hζ x) (torusPullbackBridge F ζ hζ y)
  constructor
  · intro hc
    exact h.mp (hc.map (torusPullbackBridge F ζ hζ))
  · intro hb
    apply torusPullbackBridge_injective F ζ hζ
    simpa only [map_mul] using (h.mpr hb).eq

 def baseEval (v : KPHilbert.Place F) :
    KPAdelicCoverRestrictedProduct.AdelicPGL2 F →* KPPGLLocalCover.LocalPGL2 F v :=
  QuotientGroup.lift _ ((KPPGLLocalCover.baseQuotient F v).comp
    (KPAdelicCoverRestrictedProduct.matrixEval F v)) (by
      rintro a ⟨w, rfl⟩
      change KPPGLLocalCover.baseQuotient F v
        (KPAdelicCoverRestrictedProduct.matrixEval F v (Matrix.GeneralLinearGroup.scalar (Fin 2) w)) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨KPGlobalCubicIdelePairing.ideleEval F v w, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [KPScalarSplitCentral.scalarMatrix, KPAdelicCoverRestrictedProduct.matrixEval,
          Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, KPGlobalCubicIdelePairing.ideleEval])
 theorem eval_diagonal (v : KPHilbert.Place F) (y : KPGlobalCubicIdelePairing.Ideles F) :
    baseEval F v (KPGlobalCubicIdelePairing.diagonalPGL F y) =
      KPPGLLocalCover.baseQuotient F v (diagonalHom F v (KPGlobalCubicIdelePairing.ideleEval F v y)) := by
  change KPPGLLocalCover.baseQuotient F v
    (KPAdelicCoverRestrictedProduct.matrixEval F v (KPGlobalCubicIdelePairing.diagonalHom F y)) = _
  apply congrArg (KPPGLLocalCover.baseQuotient F v)
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPAdelicCoverRestrictedProduct.matrixEval, KPGlobalCubicIdelePairing.diagonalHom,
      KPGlobalCubicIdelePairing.diagonalMatrix, diagonalHom, KubotaRankTwo.coe_d,
      KPGlobalCubicIdelePairing.ideleEval]
private theorem raw_local (P : CompatibleLocalData F ζ hζ)
    (x : rawB F ζ hζ P) (v : KPHilbert.Place F) :
    ∃ b : localPreimage F ζ hζ v (P.localData v).L,
      b.val.val = KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) := by
  obtain ⟨b, hb, he⟩ := x.property
  let e : E F ζ hζ := b
  have hproj : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ b.val =
      KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.p F ζ hζ e) :=
    (diagonal_formula F ⟨_, b.property⟩).symm
  have he' : b.val = KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) := he
  have hlocal : KPPGLLocalCover.projection F ζ hζ v
      (KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v)) =
      KPPGLLocalCover.baseQuotient F v (diagonalHom F v
        (KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ e))) := by
    have h := congrArg (baseEval F v) hproj
    rw [he'] at h
    rw [eval_diagonal] at h
    change KPPGLLocalCover.baseQuotient F v
      (KPAdelicCoverRestrictedProduct.matrixEval F v
        (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x.val)) = _ at h
    rw [KPAdelicCoverRestrictedProduct.restrictedProjection_eval] at h
    exact h
  let g : LocalE F ζ hζ v := ⟨KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v),
    ⟨KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ e), hlocal.symm⟩⟩
  have hratio : localRatio F ζ hζ v g =
      KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ e) :=
    (localRatioValue_eq F ζ hζ v hlocal.symm).symm
  refine ⟨⟨g, ?_⟩, rfl⟩
  change KPGlobalCubicIdelePairing.localClass F v (localRatio F ζ hζ v g) ∈ (P.localData v).L
  rw [hratio]
  exact hb v

private theorem diagonal_injective :
    Function.Injective (KPGlobalCubicIdelePairing.diagonalPGL F) := by
  intro y y' h
  change QuotientGroup.mk' _ (KPGlobalCubicIdelePairing.diagonalHom F y) =
    QuotientGroup.mk' _ (KPGlobalCubicIdelePairing.diagonalHom F y') at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hzN, hz⟩ := h
  obtain ⟨w, hw⟩ := hzN
  have key : KPGlobalCubicIdelePairing.diagonalHom F y *
      Matrix.GeneralLinearGroup.scalar (Fin 2) w =
      KPGlobalCubicIdelePairing.diagonalHom F y' := by
    rw [hw]; exact hz
  have h11 := congrArg (fun g : KPAdelicCoverRestrictedProduct.AdelicGL2 F =>
    (g : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 1 1) key
  have h00 := congrArg (fun g : KPAdelicCoverRestrictedProduct.AdelicGL2 F =>
    (g : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 0 0) key
  simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two] at h11 h00
  have hw1 : w = 1 := h11
  subst hw1
  exact Units.ext (by simpa using h00)

private theorem pD_surjective : Function.Surjective (pD F ζ hζ) := by
  intro d
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (CubicCharacters.cubes (KPGlobalCenterRationalCharacter.Ideles F)) d
  obtain ⟨g, hg⟩ := KPAdelicCoverRestrictedProduct.pglProjection_surjective F ζ hζ
    (KPGlobalCubicIdelePairing.diagonalPGL F y)
  have ht : g ∈ KPGlobalTorusFunctionData.torus F ζ hζ := by
    refine ⟨KPGlobalCubicIdelePairing.diagonalHom F y, hg.symm, ?_, ?_⟩
    · simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
    · simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  let e : E F ζ hζ := ⟨g, ht⟩
  have hp : KPGlobalTorusFunctionData.p F ζ hζ e = y := by
    apply diagonal_injective F
    exact (diagonal_formula F ⟨_, e.property⟩).trans hg
  refine ⟨e, ?_⟩
  change QuotientGroup.mk' _ (KPGlobalTorusFunctionData.p F ζ hζ e) = _
  rw [hp]

 def localPairingHom (v : KPHilbert.Place F) :
    LocalD F v →* (LocalD F v →* rootsOfUnity 3 F) where
  toFun x :=
    { toFun := KPGlobalCubicIdelePairing.localPairing F ζ hζ v x
      map_one' := by
        induction x using QuotientGroup.induction_on with
        | H x =>
          change KPGlobalCubicIdelePairing.localPairing F ζ hζ v
            (KPGlobalCubicIdelePairing.localClass F v x) 1 = 1
          rw [← map_one (KPGlobalCubicIdelePairing.localClass F v),
            KPGlobalCubicIdelePairing.localPairing_representatives]
          simpa only [one_pow] using ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 x 1).2
      map_mul' y z := by
        induction x using QuotientGroup.induction_on with
        | H x =>
          induction y using QuotientGroup.induction_on with
          | H y =>
            induction z using QuotientGroup.induction_on with
            | H z => exact (KPHilbert.B3_laws F ζ hζ v).2.1 x y z }
  map_one' := by
    apply MonoidHom.ext
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      change KPGlobalCubicIdelePairing.localPairing F ζ hζ v 1
        (KPGlobalCubicIdelePairing.localClass F v y) = 1
      rw [← map_one (KPGlobalCubicIdelePairing.localClass F v),
        KPGlobalCubicIdelePairing.localPairing_representatives]
      simpa only [one_pow] using ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 1 y).1
  map_mul' x y := by
    apply MonoidHom.ext
    intro z
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        induction z using QuotientGroup.induction_on with
        | H z => exact (KPHilbert.B3_laws F ζ hζ v).1 x y z

private theorem maximal_mem_of_annihilates {G : Type*} [CommGroup G]
    (b : G →* (G →* rootsOfUnity 3 F)) (halt : ∀ x, b x x = 1)
    (L : Subgroup G) (hL : IsMaximalIsotropic F (fun x y => b x y) L)
    (x : G) (hx : ∀ l ∈ L, b x l = 1) : x ∈ L := by
  have hswap (u v : G) : b v u = (b u v)⁻¹ := by
    have h := halt (v * u)
    simp only [map_mul, MonoidHom.mul_apply, halt, one_mul, mul_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have hxl (l : G) (hl : l ∈ L) (n : ℤ) : b (x ^ n) l = 1 := by
    simp only [map_zpow, MonoidHom.zpow_apply, hx l hl, one_zpow]
  have hlx (l : G) (hl : l ∈ L) (n : ℤ) : b l (x ^ n) = 1 := by
    rw [hswap, hxl l hl n, inv_one]
  have hxx (n p : ℤ) : b (x ^ n) (x ^ p) = 1 := by
    simp only [map_zpow, MonoidHom.zpow_apply, halt, one_zpow]
  have hiso : ∀ u ∈ L ⊔ Subgroup.zpowers x, ∀ v ∈ L ⊔ Subgroup.zpowers x,
      b u v = 1 := by
    intro u hu v hv
    obtain ⟨l, hl, u', hu', rfl⟩ := Subgroup.mem_sup.mp hu
    obtain ⟨m, hm, v', hv', rfl⟩ := Subgroup.mem_sup.mp hv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    obtain ⟨p, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    simp only [map_mul, MonoidHom.mul_apply, hL.1 l hl m hm,
      hlx l hl p, hxl m hm n, hxx n p, mul_one, one_mul]
  have heq := hL.2 _ le_sup_left hiso
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

private theorem product_maximal_isotropic (P : CompatibleLocalData F ζ hζ) :
    IsMaximalIsotropic F (KPGlobalCubicIdelePairing.beta3 F ζ hζ) (M F ζ hζ P) := by
  obtain ⟨e, he⟩ := KPGlobalCubicIdelePairing.restricted_cube_quotient F
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    change (∏ᶠ v, KPGlobalCubicIdelePairing.localPairing F ζ hζ v
      (KPGlobalCubicIdelePairing.classComparison F x v)
      (KPGlobalCubicIdelePairing.classComparison F y v)) = 1
    have h : ∀ v, KPGlobalCubicIdelePairing.localPairing F ζ hζ v
        (KPGlobalCubicIdelePairing.classComparison F x v)
        (KPGlobalCubicIdelePairing.classComparison F y v) = 1 := by
      intro v
      exact (P.localData v).maximal.1 _ (hx v) _ (hy v)
    simp only [h, finprod_one]
  · intro N hMN hN
    apply le_antisymm _ hMN
    intro x hx
    change ∀ v, KPGlobalCubicIdelePairing.classComparison F x v ∈ (P.localData v).L
    intro v
    apply maximal_mem_of_annihilates F (localPairingHom F ζ hζ v) ?_
      (P.localData v).L (P.localData v).maximal
    · intro l hl
      let t : KPGlobalCubicIdelePairing.RestrictedClasses F :=
        RestrictedProduct.mulSingle (KPGlobalCubicIdelePairing.U F) v l
      obtain ⟨y, hy⟩ := e.surjective t
      have hy' : KPGlobalCubicIdelePairing.classComparison F y = t := (he y).symm.trans hy
      have hym : y ∈ M F ζ hζ P := by
        change ∀ w, KPGlobalCubicIdelePairing.classComparison F y w ∈ (P.localData w).L
        intro w
        rw [hy']
        by_cases hw : w = v
        · subst w
          simpa only [t, RestrictedProduct.mulSingle_eq_same] using hl
        · simpa only [t, RestrictedProduct.mulSingle_eq_of_ne _ _ hw] using (P.localData w).L.one_mem
      have hxy := hN x hx y (hMN hym)
      change (∏ᶠ w, KPGlobalCubicIdelePairing.localPairing F ζ hζ w
        (KPGlobalCubicIdelePairing.classComparison F x w)
        (KPGlobalCubicIdelePairing.classComparison F y w)) = 1 at hxy
      rw [hy', finprod_eq_single _ v] at hxy
      · change KPGlobalCubicIdelePairing.localPairing F ζ hζ v
          (KPGlobalCubicIdelePairing.classComparison F x v) l = 1
        simpa only [t, RestrictedProduct.mulSingle_eq_same] using hxy
      · intro w hw
        rw [show t w = 1 from RestrictedProduct.mulSingle_eq_of_ne _ _ hw]
        exact (localPairingHom F ζ hζ w _).map_one
    · intro z
      induction z using QuotientGroup.induction_on with
      | H z => exact ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 z).1

theorem product_polarization (P : CompatibleLocalData F ζ hζ) :
    KPLocalPolarization.IsMaximalAbelian (B F ζ hζ P) ∧
    ∀ (x : rawB F ζ hζ P) (v : KPHilbert.Place F),
      ∃ b : localPreimage F ζ hζ v (P.localData v).L,
        b.val.val = KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) := by
  refine ⟨?_, fun x v => raw_local F ζ hζ P x v⟩
  have hM := product_maximal_isotropic F ζ hζ P
  refine ⟨fun x hx y hy => (commute_iff_beta F ζ hζ x y).mpr
    (hM.1 _ hx _ hy), ?_⟩
  intro N hBN hN
  have hNM : N.map (pD F ζ hζ) = M F ζ hζ P := by
    apply hM.2
    · intro d hd
      obtain ⟨x, rfl⟩ := pD_surjective F ζ hζ d
      exact Subgroup.mem_map.mpr ⟨x, hBN hd, rfl⟩
    · intro x hx y hy
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      exact (commute_iff_beta F ζ hζ u v).mp (hN u hu v hv)
  apply le_antisymm _ hBN
  intro x hx
  change pD F ζ hζ x ∈ M F ζ hζ P
  rw [← hNM]
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem raw_coordinate_mem (P : CompatibleLocalData F ζ hζ)
    (x : rawB F ζ hζ P) (v : KPHilbert.Place F) :
    ∃ b : localPreimage F ζ hζ v (P.localData v).L,
      b.val.val = KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) :=
  raw_local F ζ hζ P x v

end
end DedekindZetaZeroFree.ProductPolarization

end

section
open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ProductPolarization
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology localCoverTopology

structure FiniteAdjustment (P : CompatibleLocalData F ζ hζ) where
  S : Finset (HeightOneSpectrum (𝓞 F))
  chi : ∀ v : KPHilbert.Place F, (P.localData v).L →ₜ* ℂˣ
  unitary : ∀ v (x : (P.localData v).L), ‖(chi v x : ℂ)‖ = 1
  complex_unchanged : ∀ w : InfinitePlace F, chi (Sum.inl w) = 1
  outside_unchanged : ∀ q, q ∉ S → chi (Sum.inr q) = 1

def adjustedLocalValue (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (v : KPHilbert.Place F)
    (b : localPreimage F ζ hζ v (P.localData v).L) : ℂˣ :=
  (P.localData v).lambda b * T.chi v ⟨localProjection F ζ hζ v b.val, b.property⟩

def rawCoordinate (P : CompatibleLocalData F ζ hζ)
    (x : rawB F ζ hζ P) (v : KPHilbert.Place F) :
    localPreimage F ζ hζ v (P.localData v).L :=
  Classical.choose (raw_coordinate_mem F ζ hζ P x v)

def rawProduct (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (x : rawB F ζ hζ P) : ℂˣ :=
  ∏ᶠ v, adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v)

def rawProjection (P : CompatibleLocalData F ζ hζ) : rawB F ζ hζ P → B F ζ hζ P :=
  fun x =>
    let h := Subgroup.mem_map.mp x.property
    ⟨⟨KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val),
      by obtain ⟨b, hb, he⟩ := h; exact he ▸ b.property⟩,
      by
        obtain ⟨b, hb, he⟩ := h
        convert hb using 1
        exact Subtype.ext he.symm⟩

set_option maxHeartbeats 500000

 instance local_group (v : KPHilbert.Place F) :
    IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  cases v with
  | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
  | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2
 instance adelic_group :
    IsTopologicalGroup (KPAdelicCoverRestrictedProduct.CubicGL2Adelic F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.1
 instance compact_open_fact : Fact (∀ v, IsOpen
    (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) :=
  ⟨KPAdelicCoverRestrictedProduct.compact_open F ζ hζ⟩

 def flatten (P : CompatibleLocalData F ζ hζ) :
    ((B F ζ hζ P).map (E F ζ hζ).subtype) ≃ₜ B F ζ hζ P where
  toFun x :=
    ⟨⟨x.val, by obtain ⟨b, hb, he⟩ := x.property; exact he ▸ b.property⟩,
      by
        obtain ⟨b, hb, he⟩ := x.property
        have he' : (⟨x.val, by obtain ⟨b, hb, he⟩ := x.property; exact he ▸ b.property⟩ : E F ζ hζ) = b :=
          Subtype.ext (show b.val = x.val from he).symm
        exact he' ▸ hb⟩
  invFun x := ⟨x.val.val, Subgroup.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

private theorem projection_quotient (P : CompatibleLocalData F ζ hζ) :
    Topology.IsQuotientMap (rawProjection F ζ hζ P) := by
  have hq : IsOpenQuotientMap
      ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ) ∘
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)) :=
    QuotientGroup.isOpenQuotientMap_mk.comp QuotientGroup.isOpenQuotientMap_mk
  exact ((flatten F ζ hζ P).isQuotientMap.comp
    (hq.restrictPreimage ((B F ζ hζ P).map (E F ζ hζ).subtype : Set _)).isQuotientMap)

private theorem coordinate_continuous (P : CompatibleLocalData F ζ hζ)
    (v : KPHilbert.Place F) : Continuous (fun x : rawB F ζ hζ P => rawCoordinate F ζ hζ P x v) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have he : (fun x : rawB F ζ hζ P => (rawCoordinate F ζ hζ P x v).val.val) =
      fun x => KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) := by
    funext x
    exact Classical.choose_spec (raw_coordinate_mem F ζ hζ P x v)
  change Continuous (fun x : rawB F ζ hζ P => (rawCoordinate F ζ hζ P x v).val.val)
  rw [he]
  exact QuotientGroup.continuous_mk.comp ((RestrictedProduct.continuous_eval v).comp continuous_subtype_val)

private theorem matrix_ratio (P : CompatibleLocalData F ζ hζ) (x : rawB F ζ hζ P)
    (v : KPHilbert.Place F) :
    ∃ z : (KPHilbert.Completion F v)ˣ,
      diagonalHom F v (localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val) *
        KPScalarSplitCentral.scalarMatrix F v z = KPLocalCover.projection F ζ hζ v (x.val v) := by
  have h := localRatioValue_spec F ζ hζ v (rawCoordinate F ζ hζ P x v).val
  rw [show (rawCoordinate F ζ hζ P x v).val.val =
      KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) from
      Classical.choose_spec (raw_coordinate_mem F ζ hζ P x v),
    KPPGLLocalCover.projection_coverQuotient] at h
  rw [KPPGLLocalCover.baseQuotient, QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨s, ⟨z, hz⟩, hs⟩ := h
  exact ⟨z, hz ▸ hs⟩
private theorem ratio_raw_formula (P : CompatibleLocalData F ζ hζ) (x : rawB F ζ hζ P)
    (v : KPHilbert.Place F) :
    (localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val : KPHilbert.Completion F v) =
      (x.val v).g 0 0 / (x.val v).g 1 1 := by
  obtain ⟨z, hz⟩ := matrix_ratio F ζ hζ P x v
  have h00 := congrArg (fun g : KPLocalCover.LocalGL2 F v =>
    (g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 0) hz
  have h11 := congrArg (fun g : KPLocalCover.LocalGL2 F v =>
    (g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 1) hz
  rw [Matrix.GeneralLinearGroup.coe_mul, show diagonalHom F v = diagonalHom F v from rfl,
    show diagonalHom F v (localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val) =
      KubotaRankTwo.d (KPHilbert.Completion F v) (localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val) 1 from rfl,
    KubotaRankTwo.coe_d, Matrix.GeneralLinearGroup.coe_scalar] at h00 h11
  simp [Matrix.mul_apply, Matrix.scalar, KPLocalCover.projection] at h00 h11
  change (localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val : KPHilbert.Completion F v) * z = (x.val v).g 0 0 at h00
  change (z : KPHilbert.Completion F v) = (x.val v).g 1 1 at h11
  rw [← h00, ← h11]
  exact (mul_div_cancel_right₀ _ (Units.ne_zero z)).symm

private theorem ratio_raw_continuous (P : CompatibleLocalData F ζ hζ)
    (v : KPHilbert.Place F) : Continuous
      (fun x : rawB F ζ hζ P => localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val) := by
  letI : ContinuousInv₀ (KPHilbert.Completion F v) := by cases v <;> infer_instance
  have hp : Continuous (KPLocalCover.projection F ζ hζ v) := by
    cases v with
    | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.2.1.continuous
    | inr q => exact (KPLocalChartTopology.finite_projection F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1.continuous
  letI : ContinuousMul (KPHilbert.Completion F v) := by cases v <;> infer_instance
  have hv : Continuous (fun g : KPLocalCover.LocalGL2 F v =>
      (g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v))) := Units.continuous_val
  have hc (i j : Fin 2) : Continuous (fun x : rawB F ζ hζ P => (x.val v).g i j) :=
    (continuous_apply_apply i j).comp (hv.comp
      (hp.comp ((RestrictedProduct.continuous_eval v).comp continuous_subtype_val)))
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  have he : (fun x : rawB F ζ hζ P =>
      (localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val : KPHilbert.Completion F v)) =
      fun x => (x.val v).g 0 0 / (x.val v).g 1 1 :=
    funext (fun x => ratio_raw_formula F ζ hζ P x v)
  change Continuous (fun x : rawB F ζ hζ P =>
      (localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val : KPHilbert.Completion F v))
  rw [he]
  refine (hc 0 0).div (hc 1 1) fun x => ?_
  obtain ⟨z, hz⟩ := matrix_ratio F ζ hζ P x v
  have h11 := congrArg (fun g : KPLocalCover.LocalGL2 F v =>
    (g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 1) hz
  rw [Matrix.GeneralLinearGroup.coe_mul,
    show diagonalHom F v (localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val) =
      KubotaRankTwo.d (KPHilbert.Completion F v) (localRatio F ζ hζ v (rawCoordinate F ζ hζ P x v).val) 1 from rfl,
    KubotaRankTwo.coe_d, Matrix.GeneralLinearGroup.coe_scalar] at h11
  simp [Matrix.mul_apply, Matrix.scalar, KPLocalCover.projection] at h11
  change (z : KPHilbert.Completion F v) = (x.val v).g 1 1 at h11
  rw [← h11]
  exact Units.ne_zero z

private theorem adjusted_raw_continuous (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (v : KPHilbert.Place F) : Continuous
      (fun x : rawB F ζ hζ P => adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v)) := by
  apply ((P.localData v).lambda.continuous.comp (coordinate_continuous F ζ hζ P v)).mul
  apply (T.chi v).continuous.comp
  apply Continuous.subtype_mk
  exact QuotientGroup.continuous_mk.comp (ratio_raw_continuous F ζ hζ P v)
private theorem good_value_one (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (q : HeightOneSpectrum (𝓞 F))
    (hq : IsUnramified F ζ hζ q (P.localData (Sum.inr q))) (hS : q ∉ T.S)
    (x : rawB F ζ hζ P) (hx : x.val (Sum.inr q) ∈ KPAdelicCoverRestrictedProduct.compact F ζ hζ (Sum.inr q)) :
    adjustedLocalValue F ζ hζ P T (Sum.inr q) (rawCoordinate F ζ hζ P x (Sum.inr q)) = 1 := by
  have hb : (rawCoordinate F ζ hζ P x (Sum.inr q)).val.val ∈
      KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q) := by
    rw [show (rawCoordinate F ζ hζ P x (Sum.inr q)).val.val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (x.val (Sum.inr q)) from
      Classical.choose_spec (raw_coordinate_mem F ζ hζ P x (Sum.inr q))]
    exact Subgroup.mem_map.mpr ⟨_, hx, rfl⟩
  simp only [adjustedLocalValue, hq.2.2 _ hb, T.outside_unchanged q hS]
  simp

private theorem adjusted_locallyFinite (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) : LocallyFinite (fun v =>
      Function.mulSupport (fun x : rawB F ζ hζ P => adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v))) := by
  have hb : {q | ¬ IsUnramified F ζ hζ q (P.localData (Sum.inr q))}.Finite :=
    Filter.eventually_cofinite.mp P.unramified_almost_everywhere
  let exc : Set (KPHilbert.Place F) := Set.range Sum.inl ∪
    Sum.inr '' ({q | ¬ IsUnramified F ζ hζ q (P.localData (Sum.inr q))} ∪ (T.S : Set _))
  have hexc : exc.Finite := (Set.finite_range Sum.inl).union
    ((hb.union T.S.finite_toSet).image Sum.inr)
  intro x
  let U : Set (rawB F ζ hζ P) := {y | ∀ v,
    x.val v ∈ KPAdelicCoverRestrictedProduct.compact F ζ hζ v →
      y.val v ∈ KPAdelicCoverRestrictedProduct.compact F ζ hζ v}
  have hU : IsOpen U := (RestrictedProduct.isOpen_forall_imp_mem
    (KPAdelicCoverRestrictedProduct.compact_open F ζ hζ)).preimage continuous_subtype_val
  refine ⟨U, hU.mem_nhds (fun _ h => h), ?_⟩
  apply (hexc.union (Filter.eventually_cofinite.mp x.val.property)).subset
  intro v hv
  by_contra hn
  have hnexc : v ∉ exc := fun h => hn (Or.inl h)
  have hx : x.val v ∈ KPAdelicCoverRestrictedProduct.compact F ζ hζ v :=
    not_not.mp (fun h => hn (Or.inr h))
  obtain ⟨y, hyv, hyU⟩ := hv
  change adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P y v) ≠ 1 at hyv
  cases v with
  | inl w => exact hnexc (Or.inl ⟨w, rfl⟩)
  | inr q =>
    have hq : IsUnramified F ζ hζ q (P.localData (Sum.inr q)) :=
      not_not.mp (fun h => hnexc (Or.inr ⟨q, Or.inl h, rfl⟩))
    have hS : q ∉ T.S := fun h => hnexc (Or.inr ⟨q, Or.inr h, rfl⟩)
    exact hyv (good_value_one F ζ hζ P T q hq hS y (hyU _ hx))

theorem product_topology (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) :
    Continuous (rawProduct F ζ hζ P T) ∧
      Topology.IsQuotientMap (rawProjection F ζ hζ P) := by
  exact ⟨continuous_finprod (adjusted_raw_continuous F ζ hζ P T)
      (adjusted_locallyFinite F ζ hζ P T), projection_quotient F ζ hζ P⟩

end
end DedekindZetaZeroFree.ProductPolarization

end

section
open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ProductPolarization
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology localCoverTopology
private theorem rawCoordinate_val (P : CompatibleLocalData F ζ hζ)
    (x : rawB F ζ hζ P) (v : KPHilbert.Place F) :
    (rawCoordinate F ζ hζ P x v).val.val =
      KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) :=
  Classical.choose_spec (raw_coordinate_mem F ζ hζ P x v)
private theorem rawProduct_finiteSupport (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (x : rawB F ζ hζ P) :
    Function.HasFiniteMulSupport
      (fun v => adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v)) := by
  have hx : ∀ᶠ q in Filter.cofinite,
      x.val (Sum.inr q) ∈ KPAdelicCoverRestrictedProduct.compact F ζ hζ (Sum.inr q) :=
    Filter.eventually_cofinite.mpr
      ((Filter.eventually_cofinite.mp x.val.property).preimage Sum.inr_injective.injOn)
  have hS : ∀ᶠ q in Filter.cofinite, q ∉ T.S := by
    apply Filter.eventually_cofinite.mpr
    simpa using T.S.finite_toSet
  have hg : ∀ᶠ q in Filter.cofinite,
      adjustedLocalValue F ζ hζ P T (Sum.inr q) (rawCoordinate F ζ hζ P x (Sum.inr q)) = 1 := by
    filter_upwards [hx, P.unramified_almost_everywhere, hS] with q hq hu hS
    simp only [adjustedLocalValue, T.outside_unchanged q hS]
    change (P.localData (Sum.inr q)).lambda (rawCoordinate F ζ hζ P x (Sum.inr q)) * 1 = 1
    rw [mul_one]
    apply hu.2.2
    rw [rawCoordinate_val]
    exact Subgroup.mem_map.mpr ⟨x.val (Sum.inr q), hq, rfl⟩
  have hf := Filter.eventually_cofinite.mp hg
  apply Set.Finite.subset ((Set.finite_range (Sum.inl : InfinitePlace F → KPHilbert.Place F)).union
    (hf.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)))
  intro v hv
  cases v with
  | inl w => exact Or.inl ⟨w, rfl⟩
  | inr q => exact Or.inr ⟨q, hv, rfl⟩
private theorem localMatrix_diagonal (v : KPHilbert.Place F)
    (b : LocalE F ζ hζ v) (g : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (hg : KPPGLLocalCover.coverQuotient F ζ hζ v g = b.val) :
    g.g 1 0 = 0 ∧ g.g 0 1 = 0 := by
  have h := localRatioValue_spec F ζ hζ v b
  rw [← hg, KPPGLLocalCover.projection_coverQuotient] at h
  change QuotientGroup.mk' (KPPGLLocalCover.scalarSubgroup F v)
    (diagonalHom F v (localRatioValue F ζ hζ v b)) =
      QuotientGroup.mk' (KPPGLLocalCover.scalarSubgroup F v) g.g at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, ⟨u, rfl⟩, hz⟩ := h
  have h10 := congrArg (fun a : KPLocalCover.LocalGL2 F v => (a : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 0) hz
  have h01 := congrArg (fun a : KPLocalCover.LocalGL2 F v => (a : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 1) hz
  constructor
  · simpa [diagonalHom, Matrix.mul_apply, Fin.sum_univ_two, KPScalarSplitCentral.scalarMatrix] using h10.symm
  · simpa [diagonalHom, Matrix.mul_apply, Fin.sum_univ_two, KPScalarSplitCentral.scalarMatrix] using h01.symm
private theorem single_mem_E (v : KPHilbert.Place F)
    (b : LocalE F ζ hζ v) (g : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (hg : KPPGLLocalCover.coverQuotient F ζ hζ v g = b.val) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ v g) ∈ E F ζ hζ := by
  obtain ⟨h10,h01⟩ := localMatrix_diagonal F ζ hζ v b g hg
  have hoff (i j : Fin 2) (hij : i ≠ j) :
      KPAdelicCoverRestrictedProduct.projection F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ v g) i j = 0 := by
    have hgij : g.g i j = 0 := by fin_cases i <;> fin_cases j <;> simp_all
    apply Prod.ext
    · funext w
      have he := KPAdelicCoverRestrictedProduct.projection_localInjection F ζ hζ v (Sum.inl w) g
      have hcoeff := congrArg (fun A : KPLocalCover.LocalGL2 F (Sum.inl w) =>
        (A : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w))) i j) he
      change (KPAdelicCoverRestrictedProduct.projection F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ v g) i j).1 w =
        (Pi.mulSingle v g (Sum.inl w)).g i j at hcoeff
      change _ = (0 : KPHilbert.Completion F (Sum.inl w))
      rw [hcoeff]
      by_cases hv : v = Sum.inl w
      · subst v; simpa using hgij
      · simp [Pi.mulSingle_eq_of_ne (Ne.symm hv), hij]
    · apply Subtype.ext
      funext q
      have he := KPAdelicCoverRestrictedProduct.projection_localInjection F ζ hζ v (Sum.inr q) g
      have hcoeff := congrArg (fun A : KPLocalCover.LocalGL2 F (Sum.inr q) =>
        (A : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inr q))) i j) he
      change (KPAdelicCoverRestrictedProduct.projection F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ v g) i j).2 q =
        (Pi.mulSingle v g (Sum.inr q)).g i j at hcoeff
      change _ = (0 : KPHilbert.Completion F (Sum.inr q))
      refine hcoeff.trans ?_
      by_cases hv : v = Sum.inr q
      · subst v; simpa using hgij
      · simp [Pi.mulSingle_eq_of_ne (Ne.symm hv), hij]
  exact ⟨KPAdelicCoverRestrictedProduct.projection F ζ hζ
    (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ v g), rfl,
    hoff 1 0 (by decide), hoff 0 1 (by decide)⟩
open scoped commutatorElement
private theorem raw_commutator_single (x : KPGlobalCenterRationalCharacter.Raw F ζ hζ)
    (v : KPHilbert.Place F) (g : KPLocalCover.CubicGL2Raw F ζ hζ v) :
    ⁅x, KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ v g⁆ =
      KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ v ⁅x v, g⁆ := by
  ext w
  change ⁅x w, Pi.mulSingle v g w⁆ = Pi.mulSingle v ⁅x v, g⁆ w
  by_cases hv : v = w
  · subst w; simp
  · simp [Pi.mulSingle_eq_of_ne (Ne.symm hv)]
private theorem raw_local_center (P : CompatibleLocalData F ζ hζ)
    (z : KPGlobalCenterRationalCharacter.Z F ζ hζ)
    (x : rawB F ζ hζ P)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = z.val.val)
    (v : KPHilbert.Place F) :
    (rawCoordinate F ζ hζ P x v).val ∈ localCenter F ζ hζ v := by
  rw [(local_center_character F ζ hζ v).1]
  apply Subgroup.mem_center_iff.mpr
  intro b
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    (KPPGLLocalCover.splitScalarSubgroup F ζ hζ v) b.val
  have hg' : KPPGLLocalCover.coverQuotient F ζ hζ v g = b.val := hg
  let t : E F ζ hζ := ⟨KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ v g),
    single_mem_E F ζ hζ v b g hg'⟩
  have hc : ⁅KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val), t.val⁆ = 1 := by
    rw [hx]
    exact commutatorElement_eq_one_iff_commute.mpr
      ((show Commute z.val t from (Subgroup.mem_center_iff.mp z.property t).symm).map (E F ζ hζ).subtype)
  obtain ⟨j, hj, _, hjformula⟩ := KPAdelicCoverRestrictedProduct.local_pgl_injection F ζ hζ v
  apply commutatorElement_eq_one_iff_commute.mp
  apply Subtype.ext
  change ⁅b.val, (rawCoordinate F ζ hζ P x v).val.val⁆ = 1
  apply hj
  rw [map_one]
  rw [hg'.symm, rawCoordinate_val, ← map_commutatorElement]
  rw [hjformula]
  have hh := raw_commutator_single F ζ hζ x.val v g
  have hmap := congrArg (fun y => KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ y)) hh
  change ⁅KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val), t.val⁆ =
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ v ⁅x.val v, g⁆) at hmap
  have hraw : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ v ⁅x.val v, g⁆) = 1 :=
    hmap.symm.trans hc
  rw [← commutatorElement_inv, map_inv, map_inv, hraw, inv_one]
private theorem B_raw_lift (P : CompatibleLocalData F ζ hζ) (b : B F ζ hζ P) :
    ∃ x : rawB F ζ hζ P, KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val := by
  obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective
    (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ) b.val.val
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective
    (KPAdelicCoverRestrictedProduct.M F ζ hζ) y
  have h : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x) = b.val.val :=
    (congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ) hx).trans hy
  refine ⟨⟨x, ?_⟩, h⟩
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x) ∈
      (B F ζ hζ P).map (E F ζ hζ).subtype
  rw [h]
  exact Subgroup.mem_map.mpr ⟨b.val, b.property, rfl⟩
private theorem center_values (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (lam : B F ζ hζ P → ℂˣ)
    (hlam : ∀ (b : B F ζ hζ P) (x : rawB F ζ hζ P),
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val →
      lam b = rawProduct F ζ hζ P T x)
    (b : B F ζ hζ P) (z : KPGlobalCenterRationalCharacter.Z F ζ hζ)
    (hz : b.val = z.val) : lam b = KPGlobalCenterRationalCharacter.omegaA F ζ hζ z := by
  obtain ⟨x,hx⟩ := B_raw_lift F ζ hζ P b
  have hxz := hx.trans (congrArg Subtype.val hz)
  let xc : KPGlobalCenterRationalCharacter.rawCenter F ζ hζ := ⟨x.val, by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) ∈
        (KPGlobalCenterRationalCharacter.Z F ζ hζ).map (E F ζ hζ).subtype
    rw [hxz]
    exact Subgroup.mem_map.mpr ⟨z.val, z.property, rfl⟩⟩
  rw [hlam b x hx, KPGlobalCenterRationalCharacter.omegaA_raw_formula F ζ hζ z xc hxz]
  apply finprod_congr
  intro v
  let c : localCenter F ζ hζ v :=
    ⟨(rawCoordinate F ζ hζ P x v).val, raw_local_center F ζ hζ P z x hxz v⟩
  have hc : localProjection F ζ hζ v (rawCoordinate F ζ hζ P x v).val = 1 := c.property
  have he : (⟨localProjection F ζ hζ v (rawCoordinate F ζ hζ P x v).val,
      (rawCoordinate F ζ hζ P x v).property⟩ : (P.localData v).L) = 1 := Subtype.ext hc
  unfold adjustedLocalValue
  rw [he, map_one, mul_one, (P.localData v).extends_center _ c rfl]
  exact localOmega_raw_formula F ζ hζ v c (x.val v) (rawCoordinate_val F ζ hζ P x v).symm
private theorem ordinaryTorus_commute (x y : KPGlobalTorusFunctionData.ordinaryTorus F) :
    Commute x.val y.val := by
  obtain ⟨a,ha,h10,h01⟩ := x.property
  obtain ⟨b,hb,hb10,hb01⟩ := y.property
  rw [← ha, ← hb]
  apply Commute.map
  change a * b = b * a
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h01, hb10, hb01, mul_comm]
private theorem cube_center (b : E F ζ hζ) : b ^ 3 ∈ KPGlobalCenterRationalCharacter.Z F ζ hζ := by
  apply Subgroup.mem_center_iff.mpr
  intro y
  have hc : ⁅b.val, y.val⁆ ∈ (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr
      (ordinaryTorus_commute F ⟨_,b.property⟩ ⟨_,y.property⟩)
  rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel] at hc
  obtain ⟨ε, hε⟩ := hc
  have hcentral : ⁅b.val,y.val⁆ ∈ Subgroup.center (KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ) :=
    KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,hε⟩
  have hcomm : Commute b.val ⁅b.val,y.val⁆ := Subgroup.mem_center_iff.mp hcentral b.val
  have hpow : ⁅b.val,y.val⁆ ^ 3 = 1 := by
    rw [← hε, ← map_pow]
    have he : ε ^ 3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 ε.val).mp ε.property
    rw [he, map_one]
  have hbc : Commute (b.val ^ 3) y.val := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← hcomm.commutatorElement_pow_left, hpow]
  apply Subtype.ext
  exact hbc.eq.symm
private theorem rawProduct_pow (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (x : rawB F ζ hζ P) :
    rawProduct F ζ hζ P T (x ^ 3) = rawProduct F ζ hζ P T x ^ 3 := by
  have hcoord (v : KPHilbert.Place F) : rawCoordinate F ζ hζ P (x ^ 3) v =
      rawCoordinate F ζ hζ P x v ^ 3 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [rawCoordinate_val]
    change KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v ^ 3) =
      (rawCoordinate F ζ hζ P x v).val.val ^ 3
    rw [map_pow, rawCoordinate_val]
  have hadj (v : KPHilbert.Place F) :
      adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v ^ 3) =
      adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v) ^ 3 := by
    unfold adjustedLocalValue
    rw [map_pow, mul_pow]
    congr 1
    have h : (⟨localProjection F ζ hζ v (rawCoordinate F ζ hζ P x v ^ 3).val,
        (rawCoordinate F ζ hζ P x v ^ 3).property⟩ : (P.localData v).L) =
        (⟨localProjection F ζ hζ v (rawCoordinate F ζ hζ P x v).val,
        (rawCoordinate F ζ hζ P x v).property⟩ : (P.localData v).L) ^ 3 := by
      apply Subtype.ext
      exact map_pow _ _ _
    rw [h, map_pow]
  unfold rawProduct
  simp only [hcoord, hadj]
  exact (finprod_pow (rawProduct_finiteSupport F ζ hζ P T x) 3).symm
private theorem lam_pow (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (lam : B F ζ hζ P → ℂˣ)
    (hlam : ∀ (b : B F ζ hζ P) (x : rawB F ζ hζ P),
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val →
      lam b = rawProduct F ζ hζ P T x)
    (b : B F ζ hζ P) : lam (b ^ 3) = lam b ^ 3 := by
  obtain ⟨x,hx⟩ := B_raw_lift F ζ hζ P b
  have hp : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (x ^ 3).val) = (b ^ 3).val.val := by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (x.val ^ 3)) = b.val.val ^ 3
    rw [map_pow, map_pow, hx]
  rw [hlam (b ^ 3) (x ^ 3) hp, rawProduct_pow, hlam b x hx]

theorem product_character_values (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (lam : B F ζ hζ P → ℂˣ)
    (hlam : ∀ (b : B F ζ hζ P) (x : rawB F ζ hζ P),
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val →
      lam b = rawProduct F ζ hζ P T x) :
    (∀ (b : B F ζ hζ P) (z : KPGlobalCenterRationalCharacter.Z F ζ hζ),
      b.val = z.val → lam b = KPGlobalCenterRationalCharacter.omegaA F ζ hζ z) ∧
    (∀ b : B F ζ hζ P, ‖(lam b : ℂ)‖ =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ b.val : ℝ≥0) : ℝ)) := by
  refine ⟨center_values F ζ hζ P T lam hlam, ?_⟩
  intro b
  let z : KPGlobalCenterRationalCharacter.Z F ζ hζ :=
    ⟨b.val ^ 3, cube_center F ζ hζ b.val⟩
  have hc := center_values F ζ hζ P T lam hlam (b ^ 3) z rfl
  rw [lam_pow F ζ hζ P T lam hlam b] at hc
  have hn := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) hc
  rw [Units.val_pow_eq_pow_val, norm_pow,
    KPGlobalCenterRationalCharacter.omegaA_norm] at hn
  change ‖(lam b : ℂ)‖ ^ 3 =
    ((KPGlobalCenterRationalCharacter.nu F ζ hζ (b.val ^ 3) : ℝ≥0) : ℝ) at hn
  rw [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow] at hn
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) (by decide : 3 ≠ 0)).mp hn

end
end DedekindZetaZeroFree.ProductPolarization

end
