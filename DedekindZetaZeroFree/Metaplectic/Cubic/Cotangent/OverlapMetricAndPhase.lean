module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Haar.SphericalSectorRealization
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Cotangent.LogarithmicCoframe

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContCotangentActualOverlap

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev d := Module.finrank ℚ F / 2
abbrev M := HyperbolicChart.Space (d F)

def placeEquiv : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F) := by
  apply finCongr
  exact (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1.symm

inductive ChartKind (i : Fin (H.atlas U).componentCount) where
  | orbifold (x : KPCuspGenuineMonodromy.SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
  | cusp (j : Fin ((H.atlas U).cuspAtlas i).cuspCount)
      (a : Fin (((H.atlas U).cuspAtlas i).geometry j).atlas.chartCount)

variable {F ζ hζ U R P H}

def ChartKind.representative {i} (a : ChartKind F ζ hζ U R P H i) :
    KPCuspArithmetic.PGL2 F :=
  match a with
  | .orbifold _ _ => 1
  | .cusp j _ => ((H.atlas U).cuspAtlas i).representative j

def ChartKind.archDomain {i} (a : ChartKind F ζ hζ U R P H i) :
    Set (KPCuspGenuineMonodromy.SymmetricSpace F) :=
  match a with
  | .orbifold _ O => O.neighborhood
  | .cusp j k => KPCuspCharts.toArch F ''
      {p : KPCuspCharts.Coordinates F |
        p.1.2 ∈ (((H.atlas U).cuspAtlas i).geometry j).atlas.shapeLift k ∧
        ((H.atlas U).cuspAtlas i).threshold < p.2}

def labeledA (places : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (x : M F) : KPCuspGenuineMonodromy.SymmetricSpace F :=
  fun k => CotangentLogCoframe.A (d F) x (places.symm k)

def labeledAInv (places : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (x : KPCuspGenuineMonodromy.SymmetricSpace F) : M F :=
  (CotangentLogCoframe.A (d F)).symm (fun k => x (places k))

structure LiftedChart (i : Fin (H.atlas U).componentCount) where
  kind : ChartKind F ζ hζ U R P H i
  places : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F)
  splitting : M F → rootsOfUnity 3 F
  splitting_locallyConstant : IsLocallyConstant
    (fun x : {x : M F | labeledA places x ∈ kind.archDomain} => splitting x.val)

def LiftedChart.omega {i} (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) : Set (M F) :=
  labeledA a.places ⁻¹' a.kind.archDomain

def coordinateMap {i} (a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)) :
    M F → M F :=
  fun x => labeledAInv b.places
    ((b.kind.representative⁻¹ * (γ : KPCuspArithmetic.PGL2 F) *
      a.kind.representative) • labeledA a.places x)

structure Arrow {i} (a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) where
  gamma : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)
  root : rootsOfUnity 3 F
  levelLift : U.toOpenSubgroup
  finite_comparison : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ gamma *
      (H.atlas U).representative i =
    KPCuspGenuineMonodromy.central F ζ hζ root⁻¹ *
      (H.atlas U).representative i * levelLift.val
  domain : Set (M F)
  isOpen_domain : IsOpen domain
  source : domain ⊆ a.omega
  target : Set.MapsTo (coordinateMap a b gamma) domain b.omega

def Arrow.psi {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b) : M F → M F :=
  coordinateMap a b e.gamma

def Arrow.phase {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b) (x : M F) : ℂ :=
  (KPCuspGenuineMonodromy.chi F ζ hζ
    (b.splitting (e.psi x) * e.root * (a.splitting x)⁻¹) : ℂ)

def LiftedChart.coefficient {i} (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i)
    (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H) (x : M F) : ℂ :=
  (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ) *
    (s i).val (a.kind.representative • labeledA a.places x)

def Pσ (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : KPArch.Space n) : KPArch.Space n :=
  fun k => x (σ k)

private theorem labeledAInv_labeledA
    (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F)) (x : M F) :
    labeledAInv p (labeledA p x) = x := by
  simp [labeledAInv, labeledA]

private theorem labeledA_labeledAInv
    (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (x : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA p (labeledAInv p x) = x := by
  funext k
  simp [labeledAInv, labeledA]

private theorem continuous_labeledA
    (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F)) : Continuous (labeledA p) := by
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous

 theorem coordinateMap_one {i} (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) : coordinateMap a a 1 = id := by
  funext x
  simp [coordinateMap, labeledAInv_labeledA]

theorem LiftedChart.isOpen_omega {i} (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) : IsOpen a.omega := by
  apply IsOpen.preimage (continuous_labeledA a.places)
  cases a.kind with
  | orbifold x O => exact O.isOpen
  | cusp j k =>
    change IsOpen (KPCuspCharts.toArch F '' _)
    apply (KPCuspCharts.toArchHomeomorph F
      (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2).isOpenMap
    exact (((H.atlas U).cuspAtlas i).geometry j).atlas.open_shapeLift k
      |>.preimage (continuous_snd.comp continuous_fst) |>.inter
        (isOpen_lt continuous_const continuous_snd)

def identity {i} (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) : Arrow a a where
  gamma := 1
  root := 1
  levelLift := 1
  finite_comparison := by simp
  domain := a.omega
  isOpen_domain := a.isOpen_omega
  source := Set.Subset.refl _
  target := by simpa [coordinateMap_one] using (Set.mapsTo_id a.omega)

 theorem continuous_coordinateMap {i}
    (a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) i)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)) :
    Continuous (coordinateMap a b γ) := by
  apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
  apply continuous_pi_iff.mpr
  intro k
  exact (continuous_apply (b.places k)).comp
    ((KPCuspSiegel.continuous_action F _).comp (continuous_labeledA a.places))

 theorem coordinateMap_mul {i}
    (a b c : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) i)
    (θ ψ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)) :
    coordinateMap a c (θ * ψ) = coordinateMap b c θ ∘ coordinateMap a b ψ := by
  funext x
  simp only [Function.comp_apply, coordinateMap, labeledA_labeledAInv, Subgroup.coe_mul]
  congr 1
  rw [← mul_smul]
  congr 1
  group

 theorem central_commute (ε : rootsOfUnity 3 F)
    (c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) c).symm

def comp {i} {a b c : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i}
    (θ : Arrow b c) (ψ : Arrow a b) : Arrow a c where
  gamma := θ.gamma * ψ.gamma
  root := θ.root * ψ.root
  levelLift := θ.levelLift * ψ.levelLift
  finite_comparison := by
    rw [Subgroup.coe_mul, map_mul, mul_assoc, ψ.finite_comparison]
    rw [← mul_assoc, ← mul_assoc, ← central_commute]
    simp only [mul_assoc]
    rw [← mul_assoc
      ((KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ) ↑θ.gamma), θ.finite_comparison]
    simp [mul_inv_rev, map_mul, mul_assoc]
  domain := ψ.domain ∩ ψ.psi ⁻¹' θ.domain
  isOpen_domain := ψ.isOpen_domain.inter
    (θ.isOpen_domain.preimage (continuous_coordinateMap a b ψ.gamma))
  source := fun _ hx => ψ.source hx.1
  target := by
    intro x hx
    rw [coordinateMap_mul a b c θ.gamma ψ.gamma]
    exact θ.target hx.2

theorem actual_local_formula {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b) :
    ∃ g : Fin (d F) → Matrix.GeneralLinearGroup (Fin 2) ℂ,
      (∀ k, Matrix.ProjGenLinGroup.mk (g k) =
        Matrix.ProjGenLinGroup.map (KPCusp.complexPlace F (a.places k)).embedding
          (b.kind.representative⁻¹ * (e.gamma : KPCuspArithmetic.PGL2 F) *
            a.kind.representative)) ∧
      Set.EqOn e.psi
        (fun x => (CotangentLogCoframe.A (d F)).symm
          (Pσ (d F) (b.places.trans a.places.symm)
            (KPArch.productAction (d F) g (CotangentLogCoframe.A (d F) x))))
        e.domain := by
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective
    (b.kind.representative⁻¹ * (e.gamma : KPCuspArithmetic.PGL2 F) * a.kind.representative)
  refine ⟨fun k => Matrix.GeneralLinearGroup.map
    (KPCusp.complexPlace F (a.places k)).embedding B, ?_, ?_⟩
  · intro k
    rw [← hB]
    rfl
  · intro x _
    simp only [Arrow.psi, coordinateMap, labeledAInv]
    rw [← hB]
    change (CotangentLogCoframe.A (d F)).symm
      (fun k => KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk B)
        (labeledA a.places x) (b.places k)) = _
    rw [KPCuspSiegel.action_mk]
    congr 1
    funext k
    simp [KPCuspSiegel.glAction, KPArch.productAction, Pσ, labeledA]

 def permCLM (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    KPArch.Space n →L[ℝ] KPArch.Space n :=
  ContinuousLinearMap.pi (fun k => ContinuousLinearMap.proj (σ k))

private theorem metric_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) (x v : KPArch.Space n) :
    KPArch.metric n (Pσ n σ x) (Pσ n σ v) = KPArch.metric n x v := by
  exact Equiv.sum_comp σ (fun k =>
    (KPArch.height (x k))⁻¹ ^ 2 * ‖(v k).1‖ ^ 2 + (v k).2 ^ 2)

 def formula (n : ℕ) (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (σ : Equiv.Perm (Fin n)) (x : HyperbolicChart.Space n) :=
  (CotangentLogCoframe.A n).symm (permCLM n σ (KPArch.productAction n g (CotangentLogCoframe.A n x)))

private theorem formula_smooth (n : ℕ) (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (σ : Equiv.Perm (Fin n)) : ContDiff ℝ (⊤ : ℕ∞) (formula n g σ) := by
  exact (CotangentLogCoframe.A n).symm.contDiff.comp
    ((permCLM n σ).contDiff.comp (((KPArch.productAction_contDiff n g).of_le
      (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top)).comp
      (CotangentLogCoframe.A n).contDiff))

private theorem formula_quadratic (n : ℕ)
    (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) ℂ) (σ : Equiv.Perm (Fin n))
    (x v : HyperbolicChart.Space n) :
    HyperbolicChart.metric n (formula n g σ x)
      (fderiv ℝ (formula n g σ) x v) (fderiv ℝ (formula n g σ) x v) =
      HyperbolicChart.metric n x v v := by
  have hder := (CotangentLogCoframe.A n).symm.hasFDerivAt.comp x
    ((permCLM n σ).hasFDerivAt.comp x
      (((KPArch.productAction_contDiff n g).differentiable (by simp)
        (CotangentLogCoframe.A n x)).hasFDerivAt.comp x
          (CotangentLogCoframe.A n).hasFDerivAt))
  change HasFDerivAt (formula n g σ) _ x at hder
  rw [← CotangentLogCoframe.metric_A, hder.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    formula, ContinuousLinearEquiv.apply_symm_apply]
  change KPArch.metric n (Pσ n σ _) (Pσ n σ _) = _
  rw [metric_perm]
  exact (KPArch.metric_invariant n g (CotangentLogCoframe.A n x)
    (CotangentLogCoframe.A n v)).trans (CotangentLogCoframe.metric_A n x v)

private theorem metric_polarization (n : ℕ) (x u w : HyperbolicChart.Space n) :
    HyperbolicChart.metric n x (u+w) (u+w) =
      HyperbolicChart.metric n x u u + 2 * HyperbolicChart.metric n x u w +
        HyperbolicChart.metric n x w w := by
  simp only [← CotangentLogCoframe.inner_C, map_add, inner_add_left, inner_add_right,
    real_inner_comm (CotangentLogCoframe.C n x w) (CotangentLogCoframe.C n x u)]
  ring

theorem smooth_metric {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b) :
    ContDiffOn ℝ (⊤ : ℕ∞) e.psi e.domain ∧
    ∀ x ∈ e.domain, ∀ u w : M F,
      HyperbolicChart.metric (d F) (e.psi x)
          (fderiv ℝ e.psi x u) (fderiv ℝ e.psi x w) =
        HyperbolicChart.metric (d F) x u w := by
  obtain ⟨g, _, heq⟩ := actual_local_formula e
  change Set.EqOn e.psi (formula (d F) g (b.places.trans a.places.symm)) e.domain at heq
  have hs := formula_smooth (d F) g (b.places.trans a.places.symm)
  refine ⟨hs.contDiffOn.congr heq, ?_⟩
  intro x hx u w
  have he := heq.eventuallyEq_of_mem (e.isOpen_domain.mem_nhds hx)
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [heq hx, hd]
  have hq := formula_quadratic (d F) g (b.places.trans a.places.symm) x
  have hp := hq (u+w)
  rw [map_add, metric_polarization, metric_polarization, hq u, hq w] at hp
  linarith

private theorem phase_locallyConstant {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b) :
    IsLocallyConstant (fun x : e.domain => e.phase x.val) := by
  have ha := a.splitting_locallyConstant.comp_continuous
    (show Continuous (fun x : e.domain => (⟨x.val, e.source x.property⟩ : a.omega)) from
      continuous_subtype_val.subtype_mk _)
  have hb := b.splitting_locallyConstant.comp_continuous
    (show Continuous (fun x : e.domain => (⟨e.psi x.val, e.target x.property⟩ : b.omega)) from
      ((continuous_coordinateMap a b e.gamma).comp continuous_subtype_val).subtype_mk _)
  exact ((hb.mul (IsLocallyConstant.const e.root)).mul (ha.comp Inv.inv)).comp
    (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ z : ℂ))

private theorem phase_smooth {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b) :
    ContDiffOn ℝ (⊤ : ℕ∞) e.phase e.domain := by
  rw [e.isOpen_domain.contDiffOn_iff]
  intro x hx
  have h := (phase_locallyConstant e).eventually_eq (⟨x, hx⟩ : e.domain)
  have hm := map_nhds_subtype_val (⟨x, hx⟩ : e.domain)
  rw [e.isOpen_domain.nhdsWithin_eq hx] at hm
  have he : ∀ᶠ y in 𝓝 x, e.phase y = e.phase x := by
    rw [← hm]
    exact h
  exact contDiffAt_const.congr_of_eventuallyEq he

private theorem phase_norm {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b) (x : M F) :
    ‖e.phase x‖ = 1 := by
  exact (KPCuspGenuineMonodromy.unitary_chart_cocycle F ζ hζ U
    ((H.atlas U).representative i) ((H.atlas U).line i).rho
    (fun _ => 1) (IsLocallyConstant.const 1)).1 _

set_option maxHeartbeats 1000000 in
private theorem root_ambiguity {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b)
    (v : KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) :
    (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho e.gamma) : ℂ) * v.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ e.root : ℂ) * v.val := by
  let ρ := ((H.atlas U).line i).rho
  obtain ⟨u, hu⟩ := ((H.atlas U).line i).finite_comparison e.gamma
  have he := e.finite_comparison.symm.trans hu
  rw [central_commute, central_commute] at he
  have hc : KPCuspGenuineMonodromy.central F ζ hζ e.root⁻¹ * e.levelLift.val =
      KPCuspGenuineMonodromy.central F ζ hζ (ρ e.gamma)⁻¹ * u.val := by
    apply mul_left_cancel (a := (H.atlas U).representative i)
    simpa [mul_assoc] using he
  have hh : KPCuspGenuineMonodromy.central F ζ hζ (ρ e.gamma * e.root⁻¹) =
      u.val * e.levelLift.val⁻¹ := by
    have hd := congrArg (fun z : KPCuspGenuineMonodromy.FiniteCover F ζ hζ =>
      KPCuspGenuineMonodromy.central F ζ hζ (ρ e.gamma) * z * e.levelLift.val⁻¹) hc
    simpa [map_mul, map_inv, mul_assoc] using hd
  have hm : KPCuspGenuineMonodromy.central F ζ hζ (ρ e.gamma * e.root⁻¹) ∈ U.toOpenSubgroup := by
    rw [hh]
    exact U.toOpenSubgroup.mul_mem u.property (U.toOpenSubgroup.inv_mem e.levelLift.property)
  have hv := v.property (ρ e.gamma * e.root⁻¹) hm
  have hd := congrArg (fun z : ℂ => (KPCuspGenuineMonodromy.chi F ζ hζ e.root : ℂ) * z) hv
  change (KPCuspGenuineMonodromy.chi F ζ hζ (ρ e.gamma) : ℂ) * v.val =
    (KPCuspGenuineMonodromy.chi F ζ hζ e.root : ℂ) * v.val
  simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hd
  rw [mul_comm (KPCuspGenuineMonodromy.chi F ζ hζ (ρ e.gamma) : ℂ),
    ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul] at hd
  exact hd

theorem unitary_phase {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b) :
    IsLocallyConstant (fun x : e.domain => e.phase x.val) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e.phase e.domain ∧
    (∀ x ∈ e.domain, ‖e.phase x‖ = 1) ∧
    (∀ (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
      (x : M F), x ∈ e.domain →
      b.coefficient s (e.psi x) = e.phase x * a.coefficient s x) := by
  refine ⟨phase_locallyConstant e, phase_smooth e, fun x _ => phase_norm e x, ?_⟩
  intro s x _
  have ht : b.kind.representative • labeledA b.places (e.psi x) =
      (e.gamma : KPCuspArithmetic.PGL2 F) •
        (a.kind.representative • labeledA a.places x) := by
    simp only [Arrow.psi, coordinateMap, labeledA_labeledAInv, ← mul_smul]
    congr 1
    group
  have ha := root_ambiguity e
    ⟨(s i).val (a.kind.representative • labeledA a.places x),
      (s i).property.1 _⟩
  simp only [LiftedChart.coefficient, ht, (s i).property.2 e.gamma, ha, Arrow.phase,
    map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [mul_assoc, mul_assoc, ← mul_assoc
    (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ)⁻¹,
    inv_mul_cancel₀ (Units.ne_zero _), one_mul]

end DedekindZetaZeroFree.KPContCotangentActualOverlap

namespace DedekindZetaZeroFree

open KPContCotangentActualOverlap

end DedekindZetaZeroFree

end
