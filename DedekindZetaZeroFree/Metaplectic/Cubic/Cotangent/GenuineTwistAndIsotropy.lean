module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.CountableShrinkingCharts
public import DedekindZetaZeroFree.Metaplectic.Cubic.Cotangent.OverlapCocycleIdentities
public import DedekindZetaZeroFree.Analysis.InnerProductSpaces.OrthogonalComplexification

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContCotangentActualGenuineTwistIsotropy

open KPContCotangentActualOverlap
open KPContCotangentRealOrthogonalComplexification

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

abbrev V (F : Type) [Field F] [NumberField F] :=
  EuclideanSpace ℝ (Fin (d F) × Fin 3)
abbrev E (F : Type) [Field F] [NumberField F] :=
  EuclideanSpace ℂ (Fin (d F) × Fin 3)

variable {i : Fin (H.atlas U).componentCount}
variable {a b c : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
  (U := U) (R := R) (P := P) (H := H) i}

def Q (ψ : Arrow a b) (x : M F) : V F →L[ℝ] V F :=
  (CotangentLogCoframe.C (d F) (ψ.psi x)).toContinuousLinearMap.comp
    ((fderiv ℝ ψ.psi x).comp
      (CotangentLogCoframe.H (d F) x).toContinuousLinearMap)

theorem Q_inner (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (v w : V F) :
    inner ℝ (Q ψ x v) (Q ψ x w) = inner ℝ v w := by
  change inner ℝ
    (CotangentLogCoframe.C (d F) (ψ.psi x)
      (fderiv ℝ ψ.psi x (CotangentLogCoframe.H (d F) x v)))
    (CotangentLogCoframe.C (d F) (ψ.psi x)
      (fderiv ℝ ψ.psi x (CotangentLogCoframe.H (d F) x w))) = _
  rw [CotangentLogCoframe.inner_C, (smooth_metric ψ).2 x hx]
  rw [← CotangentLogCoframe.inner_C]
  simp [CotangentLogCoframe.H]

def q (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) : V F ≃ₗᵢ[ℝ] V F :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (Q ψ x).toLinearMap
      norm_map' := (LinearMap.norm_map_iff_inner_map_map (Q ψ x)).2 (Q_inner ψ x hx) }
    (by
      apply LinearMap.surjective_of_injective
      exact (show V F →ₗᵢ[ℝ] V F from
        { toLinearMap := (Q ψ x).toLinearMap
          norm_map' := (LinearMap.norm_map_iff_inner_map_map (Q ψ x)).2 (Q_inner ψ x hx) }).injective)

theorem q_toContinuousLinearMap (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) :
    (q ψ x hx).toContinuousLinearEquiv.toContinuousLinearMap = Q ψ x := by
  ext v
  rfl

 theorem complexification_Q_apply (ψ : Arrow a b) (x : M F)
    (hx : x ∈ ψ.domain) (v : E F) :
    operatorComplexification (Fin (d F) × Fin 3) (Q ψ x) v =
      orthogonalComplexification (Fin (d F) × Fin 3) (q ψ x hx) v := by
  rw [← q_toContinuousLinearMap ψ x hx,
    ← orthogonalComplexification_toContinuousLinearMap]
  rfl

def twistedOperator (ψ : Arrow a b) (x : M F) : E F →L[ℂ] E F :=
  ψ.phase x • operatorComplexification (Fin (d F) × Fin 3) (Q ψ x)

def T (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) : E F ≃ₗᵢ[ℂ] E F :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (twistedOperator ψ x).toLinearMap
      norm_map' := by
        intro v
        change ‖ψ.phase x • operatorComplexification (Fin (d F) × Fin 3) (Q ψ x) v‖ = _
        rw [norm_smul, (unitary_phase ψ).2.2.1 x hx,
          complexification_Q_apply ψ x hx, LinearIsometryEquiv.norm_map, one_mul] }
    (by
      apply LinearMap.surjective_of_injective
      intro v w h
      change ψ.phase x • operatorComplexification (Fin (d F) × Fin 3) (Q ψ x) v =
        ψ.phase x • operatorComplexification (Fin (d F) × Fin 3) (Q ψ x) w at h
      rw [complexification_Q_apply ψ x hx, complexification_Q_apply ψ x hx] at h
      apply (orthogonalComplexification (Fin (d F) × Fin 3) (q ψ x hx)).injective
      have hz : ψ.phase x ≠ 0 := by
        intro hz
        have hn := (unitary_phase ψ).2.2.1 x hx
        simp [hz] at hn
      exact (smul_right_injective _ hz) h)

theorem T_apply (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (v : E F) :
    T ψ x hx v = ψ.phase x •
      orthogonalComplexification (Fin (d F) × Fin 3) (q ψ x hx) v := by
  change twistedOperator ψ x v = _
  exact congrArg (ψ.phase x • ·) (complexification_Q_apply ψ x hx v)

theorem T_toContinuousLinearMap (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) :
    (T ψ x hx).toContinuousLinearEquiv.toContinuousLinearMap =
      twistedOperator ψ x := by
  ext v
  rfl

theorem smooth_operators (ψ : Arrow a b) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Q ψ) ψ.domain ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (twistedOperator ψ) ψ.domain := by
  have hψ := (smooth_metric ψ).1
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞) (Q ψ) ψ.domain :=
    ((CotangentLogCoframe.contDiff_C (d F)).contDiffOn.comp hψ
      (Set.mapsTo_univ _ _)).clm_comp
        ((hψ.fderiv_of_isOpen ψ.isOpen_domain (by simp)).clm_comp
          (CotangentLogCoframe.contDiff_H (d F)).contDiffOn)
  exact ⟨hQ, (unitary_phase ψ).2.1.smul
    (contDiffOn_operatorComplexification (Fin (d F) × Fin 3) ψ.isOpen_domain hQ)⟩

theorem q_identity (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) (x : M F)
    (hx : x ∈ a.omega) :
    q (identity a) x hx = LinearIsometryEquiv.refl ℝ (V F) := by
  apply LinearIsometryEquiv.ext
  intro v
  change Q (identity a) x v = v
  simp [Q, KPContCotangentActualGroupoidIdentities.identity_psi, CotangentLogCoframe.H]

theorem T_identity (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) (x : M F)
    (hx : x ∈ a.omega) :
    T (identity a) x hx = LinearIsometryEquiv.refl ℂ (E F) := by
  apply LinearIsometryEquiv.ext
  intro v
  have h := T_apply (identity a) x hx v
  rw [KPContCotangentActualGroupoidIdentities.identity_phase, q_identity,
    orthogonalComplexification_refl] at h
  simpa using h

theorem Q_comp (θ : Arrow b c) (ψ : Arrow a b) (x : M F)
    (hx : x ∈ ψ.domain) (hθ : ψ.psi x ∈ θ.domain) :
    Q (comp θ ψ) x = (Q θ (ψ.psi x)).comp (Q ψ x) := by
  have hψ : DifferentiableAt ℝ ψ.psi x :=
    ((smooth_metric ψ).1.differentiableOn (by simp) x hx).differentiableAt
      (ψ.isOpen_domain.mem_nhds hx)
  have hθ : DifferentiableAt ℝ θ.psi (ψ.psi x) :=
    ((smooth_metric θ).1.differentiableOn (by simp) _ hθ).differentiableAt
      (θ.isOpen_domain.mem_nhds hθ)
  unfold Q
  rw [KPContCotangentActualGroupoidIdentities.comp_psi, fderiv_comp x hθ hψ]
  ext v k
  simp [Function.comp_apply, CotangentLogCoframe.H]

theorem T_comp (θ : Arrow b c) (ψ : Arrow a b) (x : M F)
    (hx : x ∈ ψ.domain) (hθ : ψ.psi x ∈ θ.domain) :
    T (comp θ ψ) x ⟨hx, hθ⟩ = (T ψ x hx).trans (T θ (ψ.psi x) hθ) := by
  apply LinearIsometryEquiv.ext
  intro v
  change twistedOperator (comp θ ψ) x v =
    twistedOperator θ (ψ.psi x) (twistedOperator ψ x v)
  simp only [twistedOperator, KPContCotangentActualGroupoidIdentities.comp_phase,
    Q_comp θ ψ x hx hθ, operatorComplexification_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [mul_comm (θ.phase (ψ.psi x)) (ψ.phase x)]

theorem T_inner (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (v w : E F) :
    inner ℂ (T ψ x hx v) (T ψ x hx w) = inner ℂ v w := by
  exact (T ψ x hx).inner_map_map v w

def B (ψ : Arrow a b) (x : M F) :
    Matrix (Fin (d F) × Fin 3) (Fin (d F) × Fin 3) ℝ :=
  fun k l => Q ψ x (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℝ l) k

theorem inverse_transpose (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) :
    (B ψ x).transpose * B ψ x = 1 ∧
    B ψ x * (B ψ x).transpose = 1 ∧
    ((B ψ x).transpose)⁻¹ = B ψ x := by
  have hleft : (B ψ x).transpose * B ψ x = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ l, Q ψ x (EuclideanSpace.basisFun _ ℝ j) l *
      Q ψ x (EuclideanSpace.basisFun _ ℝ k) l) = _
    rw [show (∑ l, Q ψ x (EuclideanSpace.basisFun _ ℝ j) l *
        Q ψ x (EuclideanSpace.basisFun _ ℝ k) l) =
      inner ℝ (Q ψ x (EuclideanSpace.basisFun _ ℝ j))
        (Q ψ x (EuclideanSpace.basisFun _ ℝ k)) by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
        simp only [star_trivial]
        exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
    rw [Q_inner ψ x hx]
    exact (orthonormal_iff_ite.mp (EuclideanSpace.basisFun _ ℝ).orthonormal) j k
  have hright : B ψ x * (B ψ x).transpose = 1 := mul_eq_one_comm.mp hleft
  exact ⟨hleft, hright, Matrix.inv_eq_left_inv hright⟩

theorem covector_evaluation (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain)
    (v : V F) (u : M F) :
    inner ℝ (q ψ x hx v)
        (CotangentLogCoframe.C (d F) (ψ.psi x) (fderiv ℝ ψ.psi x u)) =
      inner ℝ v (CotangentLogCoframe.C (d F) x u) := by
  have hq (w : V F) : q ψ x hx w = Q ψ x w :=
    congrArg (fun f : V F →L[ℝ] V F => f w) (q_toContinuousLinearMap ψ x hx)
  rw [hq]
  have h := Q_inner ψ x hx v (CotangentLogCoframe.C (d F) x u)
  simpa [Q, CotangentLogCoframe.H] using h

open KPContActualCotangentCountableShrinking

variable (A : ShrunkChart F ζ hζ U R P H)

def isotropyChart : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) A.component where
  kind := .orbifold A.center A.larger
  places := placeEquiv F ζ hζ
  splitting := fun _ => 1
  splitting_locallyConstant := IsLocallyConstant.const 1

 theorem central_comm (ε : rootsOfUnity 3 F)
    (c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
      ⟨ε, rfl⟩) c).symm

def liftedIsotropy : Subgroup (A.Isotropy × rootsOfUnity 3 F) where
  carrier := {p | ∃ u : U.toOpenSubgroup,
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ p.1.val *
        (H.atlas U).representative A.component =
      KPCuspGenuineMonodromy.central F ζ hζ p.2⁻¹ *
        (H.atlas U).representative A.component * u.val}
  one_mem' := by
    refine ⟨1, ?_⟩
    simp
  mul_mem' := by
    rintro p q ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u * v, ?_⟩
    change KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (p.1.val * q.1.val) *
      (H.atlas U).representative A.component =
      KPCuspGenuineMonodromy.central F ζ hζ (p.2 * q.2)⁻¹ *
        (H.atlas U).representative A.component * (u.val * v.val)
    rw [map_mul, mul_assoc, hv]
    calc
      _ = KPCuspGenuineMonodromy.central F ζ hζ q.2⁻¹ *
        (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ p.1.val *
          (H.atlas U).representative A.component) * v.val := by
            rw [← mul_assoc, ← mul_assoc, ← central_comm q.2⁻¹]
            group
      _ = _ := by
        rw [hu]
        simp only [mul_inv_rev, map_mul]
        group
  inv_mem' := by
    rintro p ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    change KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ p.1.val⁻¹ *
      (H.atlas U).representative A.component =
      KPCuspGenuineMonodromy.central F ζ hζ (p.2⁻¹)⁻¹ *
        (H.atlas U).representative A.component * u.val⁻¹
    rw [map_inv, inv_inv]
    have he := congrArg (fun y =>
      (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ p.1.val)⁻¹ * y * u.val⁻¹) hu
    simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at he
    rw [mul_assoc _ u.val u.val⁻¹, mul_inv_cancel, mul_one,
      ← central_comm p.2⁻¹] at he
    rw [map_inv] at he
    have := congrArg (fun y => KPCuspGenuineMonodromy.central F ζ hζ p.2 * y) he
    simpa [← mul_assoc] using this.symm

abbrev Gamma := ↥(liftedIsotropy A)

theorem finite_Gamma : Finite (Gamma A) := by
  letI : Finite A.Isotropy := KPContSectorPhaseComponentCharts.chart_stabilizer_finite
    F ζ hζ U R P H A.component A.center A.larger
  infer_instance

theorem central_label_mem (ε : rootsOfUnity 3 F)
    (hε : KPCuspGenuineMonodromy.central F ζ hζ ε ∈ U.toOpenSubgroup) :
    (1, ε) ∈ liftedIsotropy A := by
  refine ⟨⟨KPCuspGenuineMonodromy.central F ζ hζ ε, hε⟩, ?_⟩
  change KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ 1 *
    (H.atlas U).representative A.component =
    KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
      (H.atlas U).representative A.component * KPCuspGenuineMonodromy.central F ζ hζ ε
  rw [map_one, one_mul, central_comm ε⁻¹, map_inv]
  simp [mul_assoc]

def isotropyArrow (γ : Gamma A) : Arrow (isotropyChart A) (isotropyChart A) where
  gamma := γ.val.1.val
  root := γ.val.2
  levelLift := Classical.choose γ.property
  finite_comparison := Classical.choose_spec γ.property
  domain := (isotropyChart A).omega
  isOpen_domain := (isotropyChart A).isOpen_omega
  source := Set.Subset.refl _
  target := by
    intro x hx
    let δ : KPContSectorPhaseComponentCharts.ArchComponent F ζ hζ U R P H A.component :=
      ⟨KPContSectorPhaseComponentCharts.complexProjectiveEmbedding F
        (γ.val.1.val : KPCuspArithmetic.PGL2 F),
        Subgroup.mem_map.mpr ⟨γ.val.1.val, γ.val.1.val.property, rfl⟩⟩
    have hδ : δ • A.center = A.center := by
      change KPContSectorPhaseComponentCharts.complexProjectiveEmbedding F
        (γ.val.1.val : KPCuspArithmetic.PGL2 F) • A.center = A.center
      rw [KPContSectorPhaseComponentCharts.complexProjectiveEmbedding_smul]
      exact γ.val.1.property
    have hi := A.larger.invariant ⟨δ, hδ⟩
    have hm := Set.mem_image_of_mem (fun y : KPCuspGenuineMonodromy.SymmetricSpace F => (⟨δ, hδ⟩ :
      MulAction.stabilizer (KPContSectorPhaseComponentCharts.ArchComponent
        F ζ hζ U R P H A.component) A.center) • y)
      (show labeledA (placeEquiv F ζ hζ) x ∈ A.larger.neighborhood from hx)
    rw [hi] at hm
    change labeledA (placeEquiv F ζ hζ)
      (coordinateMap (isotropyChart A) (isotropyChart A) γ.val.1.val x) ∈ A.larger.neighborhood
    simp only [coordinateMap, isotropyChart, ChartKind.representative, inv_one,
      one_mul, mul_one]
    have hr (places) (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
        labeledA places (labeledAInv places y) = y := by
      funext k
      simp [labeledA, labeledAInv]
    rw [hr]
    change KPContSectorPhaseComponentCharts.complexProjectiveEmbedding F
      (γ.val.1.val : KPCuspArithmetic.PGL2 F) • labeledA (placeEquiv F ζ hζ) x ∈
        A.larger.neighborhood at hm
    rw [KPContSectorPhaseComponentCharts.complexProjectiveEmbedding_smul] at hm
    exact hm

instance gammaMulAction : MulAction (Gamma A) (M F) where
  smul γ x := (isotropyArrow A γ).psi x
  one_smul := by
    intro x
    change (identity (isotropyChart A)).psi x = x
    rw [KPContCotangentActualGroupoidIdentities.identity_psi]
    rfl
  mul_smul := by
    intro γ δ x
    change (comp (isotropyArrow A γ) (isotropyArrow A δ)).psi x =
      (isotropyArrow A γ).psi ((isotropyArrow A δ).psi x)
    rw [KPContCotangentActualGroupoidIdentities.comp_psi]
    rfl

 theorem T_same_labels (e f : Arrow a b) (hγ : e.gamma = f.gamma)
    (hroot : e.root = f.root) (x : M F) (he : x ∈ e.domain) (hf : x ∈ f.domain) :
    T e x he = T f x hf := by
  apply LinearIsometryEquiv.ext
  intro v
  change twistedOperator e x v = twistedOperator f x v
  simp only [twistedOperator, Arrow.phase, Arrow.psi, Q, hγ, hroot]

def stabilizerRepresentation (x : M F) (hx : x ∈ (isotropyChart A).omega) :
    MulAction.stabilizer (Gamma A) x →* (E F ≃ₗᵢ[ℂ] E F) where
  toFun γ := T (isotropyArrow A γ.val) x hx
  map_one' := by
    change T (isotropyArrow A 1) x hx = LinearIsometryEquiv.refl ℂ (E F)
    exact (T_same_labels (isotropyArrow A 1) (identity (isotropyChart A))
      rfl rfl x hx hx).trans (T_identity _ x hx)
  map_mul' := by
    intro γ δ
    change T (isotropyArrow A (γ.val * δ.val)) x hx =
      (T (isotropyArrow A δ.val) x hx).trans (T (isotropyArrow A γ.val) x hx)
    have hδ : (isotropyArrow A δ.val).psi x = x := δ.property
    have htarget : (isotropyArrow A δ.val).psi x ∈ (isotropyArrow A γ.val).domain := by
      change (isotropyArrow A δ.val).psi x ∈ (isotropyChart A).omega
      rw [hδ]
      exact hx
    have hc := T_comp (isotropyArrow A γ.val) (isotropyArrow A δ.val) x hx htarget
    have hs := T_same_labels (isotropyArrow A (γ.val * δ.val))
      (comp (isotropyArrow A γ.val) (isotropyArrow A δ.val)) rfl rfl x hx ⟨hx, htarget⟩
    exact hs.trans (by simpa only [hδ] using hc)

def Fixed (x : M F) (hx : x ∈ (isotropyChart A).omega) : Submodule ℂ (E F) :=
  ⨅ γ : MulAction.stabilizer (Gamma A) x,
    LinearMap.ker ((T (isotropyArrow A γ.val) x hx).toLinearEquiv.toLinearMap -
      LinearMap.id)

theorem mem_Fixed_iff (x : M F) (hx : x ∈ (isotropyChart A).omega) (v : E F) :
    v ∈ Fixed A x hx ↔ ∀ γ : Gamma A, (gammaMulAction A).smul γ x = x →
      T (isotropyArrow A γ) x hx v = v := by
  simp only [Fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h γ hγ
    exact h ⟨γ, hγ⟩
  · intro h γ
    exact h γ.val γ.property

def EquivariantTensorField (W : M F → E F) : Prop :=
  ∀ (γ : Gamma A) (x : M F) (hx : x ∈ (isotropyChart A).omega),
    W ((gammaMulAction A).smul γ x) = T (isotropyArrow A γ) x hx (W x)

theorem equivariant_mem_Fixed (W : M F → E F) (hW : EquivariantTensorField A W)
    (x : M F) (hx : x ∈ (isotropyChart A).omega) :
    W x ∈ Fixed A x hx := by
  rw [mem_Fixed_iff]
  intro γ hγ
  simpa [hγ] using (hW γ x hx).symm

theorem Fixed_eq_bot_of_central_phase (ε : rootsOfUnity 3 F)
    (hε : KPCuspGenuineMonodromy.central F ζ hζ ε ∈ U.toOpenSubgroup)
    (hχ : (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) ≠ 1)
    (x : M F) (hx : x ∈ (isotropyChart A).omega) :
    Fixed A x hx = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  rw [Submodule.mem_bot]
  let γ : Gamma A := ⟨(1, ε), central_label_mem A ε hε⟩
  have hγ : (isotropyArrow A γ).psi = id := by
    change (identity (isotropyChart A)).psi = id
    exact KPContCotangentActualGroupoidIdentities.identity_psi _
  have hfix := (mem_Fixed_iff A x hx v).mp hv γ
    (show (gammaMulAction A).smul γ x = x from congrFun hγ x)
  change twistedOperator (isotropyArrow A γ) x v = v at hfix
  have hQ : Q (isotropyArrow A γ) x = ContinuousLinearMap.id ℝ (V F) := by
    ext w k
    simp [Q, hγ, CotangentLogCoframe.H]
  have hphase : (isotropyArrow A γ).phase x = (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) := by
    change (KPCuspGenuineMonodromy.chi F ζ hζ (1 * ε * 1⁻¹) : ℂ) = _
    simp
  simp only [twistedOperator, hQ, hphase, operatorComplexification_id,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hfix
  have hz : ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) - 1) • v = 0 := by
    rw [sub_smul, one_smul, hfix, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχ)

end DedekindZetaZeroFree.KPContCotangentActualGenuineTwistIsotropy

namespace DedekindZetaZeroFree

open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentRealOrthogonalComplexification
open KPContActualCotangentCountableShrinking

theorem kp_cont_cotangent_actual_genuine_twist_isotropy
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    (∀ (i : Fin (H.atlas U).componentCount)
      (a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
        (U := U) (R := R) (P := P) (H := H) i) (ψ : Arrow a b),
      ContDiffOn ℝ (⊤ : ℕ∞) (Q ψ) ψ.domain ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (twistedOperator ψ) ψ.domain ∧
      ∀ (x : M F) (hx : x ∈ ψ.domain),
        (q ψ x hx).toContinuousLinearEquiv.toContinuousLinearMap = Q ψ x ∧
        (T ψ x hx).toContinuousLinearEquiv.toContinuousLinearMap = twistedOperator ψ x ∧
        (∀ v : E F, T ψ x hx v = ψ.phase x •
          orthogonalComplexification (Fin (d F) × Fin 3) (q ψ x hx) v) ∧
        (∀ v w : E F, inner ℂ (T ψ x hx v) (T ψ x hx w) = inner ℂ v w) ∧
        (B ψ x).transpose * B ψ x = 1 ∧
        B ψ x * (B ψ x).transpose = 1 ∧
        ((B ψ x).transpose)⁻¹ = B ψ x ∧
        (∀ (v : V F) (u : M F),
          inner ℝ (q ψ x hx v)
              (CotangentLogCoframe.C (d F) (ψ.psi x) (fderiv ℝ ψ.psi x u)) =
            inner ℝ v (CotangentLogCoframe.C (d F) x u))) ∧
    (∀ (i : Fin (H.atlas U).componentCount)
      (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
        (U := U) (R := R) (P := P) (H := H) i)
      (x : M F) (hx : x ∈ a.omega),
      q (identity a) x hx = LinearIsometryEquiv.refl ℝ (V F) ∧
      T (identity a) x hx = LinearIsometryEquiv.refl ℂ (E F)) ∧
    (∀ (i : Fin (H.atlas U).componentCount)
      (a b c : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
        (U := U) (R := R) (P := P) (H := H) i)
      (θ : Arrow b c) (ψ : Arrow a b) (x : M F)
      (hx : x ∈ ψ.domain) (hθ : ψ.psi x ∈ θ.domain),
      Q (comp θ ψ) x = (Q θ (ψ.psi x)).comp (Q ψ x) ∧
      T (comp θ ψ) x ⟨hx, hθ⟩ = (T ψ x hx).trans (T θ (ψ.psi x) hθ)) ∧
    (∀ (A : ShrunkChart F ζ hζ U R P H),
      Finite (Gamma A) ∧
      (∀ (ε : rootsOfUnity 3 F),
        KPCuspGenuineMonodromy.central F ζ hζ ε ∈ U.toOpenSubgroup →
          (1, ε) ∈ liftedIsotropy A) ∧
      ∀ (x : M F) (hx : x ∈ (isotropyChart A).omega),
        (∀ γ : MulAction.stabilizer (Gamma A) x,
          stabilizerRepresentation A x hx γ = T (isotropyArrow A γ.val) x hx) ∧
        (∀ v : E F, v ∈ Fixed A x hx ↔ ∀ γ : Gamma A,
          (gammaMulAction A).smul γ x = x → T (isotropyArrow A γ) x hx v = v) ∧
        (∀ W : M F → E F, EquivariantTensorField A W → W x ∈ Fixed A x hx) ∧
        (∀ (ε : rootsOfUnity 3 F),
          KPCuspGenuineMonodromy.central F ζ hζ ε ∈ U.toOpenSubgroup →
          (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) ≠ 1 → Fixed A x hx = ⊥)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i a b ψ
    refine ⟨(smooth_operators ψ).1, (smooth_operators ψ).2, ?_⟩
    intro x hx
    obtain ⟨hl, hr, hi⟩ := inverse_transpose ψ x hx
    exact ⟨q_toContinuousLinearMap ψ x hx, T_toContinuousLinearMap ψ x hx,
      T_apply ψ x hx, T_inner ψ x hx, hl, hr, hi, covector_evaluation ψ x hx⟩
  · intro i a x hx
    exact ⟨q_identity a x hx, T_identity a x hx⟩
  · intro i a b c θ ψ x hx hθ
    exact ⟨Q_comp θ ψ x hx hθ, T_comp θ ψ x hx hθ⟩
  · intro A
    refine ⟨finite_Gamma A, central_label_mem A, ?_⟩
    intro x hx
    exact ⟨fun _ => rfl, mem_Fixed_iff A x hx,
      fun W hW => equivariant_mem_Fixed A W hW x hx,
      fun ε hε hχ => Fixed_eq_bot_of_central_phase A ε hε hχ x hx⟩

end DedekindZetaZeroFree

end
