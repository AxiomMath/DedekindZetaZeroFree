module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Cotangent.GenuineTwistAndIsotropy

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContCotangentOverlapRationalBranches

open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def omega (a : ShrunkChart F ζ hζ U R P H) : Set (M F) :=
  labeledA (placeEquiv F ζ hζ) ⁻¹' a.domain

def q (a : ShrunkChart F ζ hζ U R P H) (x : M F) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
    (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
      (labeledA (placeEquiv F ζ hζ) x))

def targetChart (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) a.component :=
  h.symm ▸ isotropyChart b

structure ActualBranch (a b : ShrunkChart F ζ hζ U R P H) where
  component_eq : a.component = b.component
  arrow : Arrow (isotropyChart a) (targetChart a b component_eq)
  source_shrinking : arrow.domain ⊆ omega a
  target_shrinking : Set.MapsTo arrow.psi arrow.domain (omega b)
  target_larger : Set.MapsTo arrow.psi arrow.domain (isotropyChart b).omega

abbrev Branch (a b : ShrunkChart F ζ hζ U R P H) := Option (ActualBranch a b)

namespace Branch

variable {a b : ShrunkChart F ζ hζ U R P H}

def domain : Branch a b → Set (M F)
  | none => ∅
  | some e => e.arrow.domain

def psi : Branch a b → M F → M F
  | none => id
  | some e => e.arrow.psi

def inverse : Branch a b → M F → M F
  | none => id
  | some e => coordinateMap (targetChart a b e.component_eq) (isotropyChart a)
      e.arrow.gamma⁻¹

def targetDomain (e : Branch a b) : Set (M F) := e.psi '' e.domain

def transport : (e : Branch a b) → (x : M F) → x ∈ e.domain → E F ≃ₗᵢ[ℂ] E F
  | none, _, hx => False.elim hx
  | some e, x, hx => T e.arrow x hx

theorem target_mem (e : Branch a b) (x : M F) (hx : x ∈ e.domain) :
    e.psi x ∈ (isotropyChart b).omega := by
  cases e with
  | none => exact False.elim hx
  | some e => exact e.target_larger hx

structure Properties (e : Branch a b) : Prop where
  source_open : IsOpen e.domain
  target_open : IsOpen e.targetDomain
  source_subset : e.domain ⊆ omega a
  target_subset : e.targetDomain ⊆ omega b
  inverse_target : Set.MapsTo e.inverse e.targetDomain e.domain
  left_inverse : ∀ x ∈ e.domain, e.inverse (e.psi x) = x
  right_inverse : ∀ x ∈ e.targetDomain, e.psi (e.inverse x) = x
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) e.psi e.domain
  inverse_smooth : ContDiffOn ℝ (⊤ : ℕ∞) e.inverse e.targetDomain
  quotient_compatibility : ∀ x ∈ e.domain, q b (e.psi x) = q a x

end Branch

structure Enumeration (a b : ShrunkChart F ζ hζ U R P H) where
  branch : ℕ → Branch a b
  properties : ∀ k, (branch k).Properties
  covers : (⋃ k, (branch k).domain) =
    {x | x ∈ omega a ∧ q a x ∈ b.baseDomain}
  local_comparison : ∀ (k l : ℕ) (x : M F),
    x ∈ (branch k).domain ∩ (branch l).domain →
    ∃ (γ : Gamma b) (V : Set (M F)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ (branch k).domain ∩ (branch l).domain ∧
      ∀ (y : M F) (hy : y ∈ V),
        ∃ (hk : y ∈ (branch k).domain) (hl : y ∈ (branch l).domain),
          (branch l).psi y = (isotropyArrow b γ).psi ((branch k).psi y) ∧
          (branch l).transport y hl = ((branch k).transport y hk).trans
            (T (isotropyArrow b γ) ((branch k).psi y) ((branch k).target_mem y hk))

open scoped ContDiff

open Branch
private theorem component_countable (i : Fin (H.atlas U).componentCount) :
    Countable (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  infer_instance
private theorem la (x : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) x) = x := by
  funext k
  simp [labeledA, labeledAInv]
private theorem al (x : M F) :
    labeledAInv (placeEquiv F ζ hζ) (labeledA (placeEquiv F ζ hζ) x) = x := by
  simp [labeledA, labeledAInv]
 def coord (g : KPCuspArithmetic.PGL2 F) (x : M F) :=
  labeledAInv (placeEquiv F ζ hζ) (g • labeledA (placeEquiv F ζ hζ) x)
local notation "cmap" => coord (ζ:=ζ) (hζ:=hζ)
 theorem coord_mul (g h : KPCuspArithmetic.PGL2 F) (x : M F) :
    cmap (g*h) x = cmap g (cmap h x) := by
  simp [coord, la, mul_smul]
 theorem coord_one (x : M F) : cmap (1 : KPCuspArithmetic.PGL2 F) x = x := by
  simp [coord, al]
 theorem coord_continuous (g : KPCuspArithmetic.PGL2 F) : Continuous (coord (ζ:=ζ) (hζ:=hζ) g) := by
  apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp ((KPCuspSiegel.continuous_action F g).comp (by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous))
 theorem chart_coord (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    coordinateMap (isotropyChart a) (targetChart a b h) g = cmap g.val := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  funext x
  simp [coordinateMap, isotropyChart, targetChart, ChartKind.representative, coord]
 theorem chart_omega (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    (targetChart a b h).omega = (isotropyChart b).omega := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  rfl
 theorem omega_open (a : ShrunkChart F ζ hζ U R P H) : IsOpen (omega a) := by
  apply a.domain_open.preimage
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
 theorem omega_subset (a : ShrunkChart F ζ hζ U R P H) :
    omega a ⊆ (isotropyChart a).omega := by
  intro x hx
  exact a.closure_subset (subset_closure hx)
 def make (a b : ShrunkChart F ζ hζ U R P H) (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    ActualBranch a b := by
  let he := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U _ g
  let r := he.choose
  let u := he.choose_spec.choose
  have hu := he.choose_spec.choose_spec
  have ht : Set.MapsTo (coordinateMap (isotropyChart a) (targetChart a b h) g)
      (omega a ∩ cmap g.val ⁻¹' omega b) (isotropyChart b).omega := by
    rw [chart_coord a b h g]
    exact fun _ hx => omega_subset b hx.2
  exact {
    component_eq := h
    arrow := {
      gamma := g, root := r⁻¹, levelLift := u,
      finite_comparison := by simpa only [inv_inv] using hu
      domain := omega a ∩ cmap g.val ⁻¹' omega b
      isOpen_domain := (omega_open a).inter ((omega_open b).preimage (coord_continuous g.val))
      source := fun _ hx => omega_subset a hx.1
      target := by rw [chart_omega a b h]; exact ht }
    source_shrinking := fun _ hx => hx.1
    target_shrinking := by
      change Set.MapsTo (coordinateMap (isotropyChart a) (targetChart a b h) g)
        (omega a ∩ cmap g.val ⁻¹' omega b) (omega b)
      rw [chart_coord a b h g]
      exact fun _ hx => hx.2
    target_larger := ht }
private theorem coord_smooth (g : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (cmap g) := by
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  let G : Fin (d F) → Matrix.GeneralLinearGroup (Fin 2) ℂ := fun k =>
    Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F ((placeEquiv F ζ hζ) k)).embedding B
  have he : cmap (Matrix.ProjGenLinGroup.mk B) =
      fun x => (CotangentLogCoframe.A (d F)).symm
        (KPArch.productAction (d F) G (CotangentLogCoframe.A (d F) x)) := by
    funext x
    simp only [coord, labeledAInv]
    congr 1
    funext k
    change KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk B) (labeledA (placeEquiv F ζ hζ) x) ((placeEquiv F ζ hζ) k) = _
    rw [KPCuspSiegel.action_mk]
    simp [labeledA, KPCuspSiegel.glAction, KPArch.productAction, G]
  rw [he]
  exact (CotangentLogCoframe.A (d F)).symm.contDiff.comp
    (((KPArch.productAction_contDiff (d F) G).of_le
      (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top)).comp (CotangentLogCoframe.A (d F)).contDiff)
 def coordHomeo (g : KPCuspArithmetic.PGL2 F) : M F ≃ₜ M F where
  toFun := cmap g
  invFun := cmap g⁻¹
  left_inv := by intro x; rw [← coord_mul, inv_mul_cancel, coord_one]
  right_inv := by intro x; rw [← coord_mul, mul_inv_cancel, coord_one]
  continuous_toFun := coord_continuous g
  continuous_invFun := coord_continuous g⁻¹
private theorem q_coord (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component))
    (x : M F) : q b (cmap g.val x) = q a x := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i))
  simp only [coord, la]
  apply Quotient.sound
  exact ⟨g, rfl⟩
private theorem make_psi (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    (make a b h g).arrow.psi = cmap g.val := chart_coord a b h g
private theorem make_inverse (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    Branch.inverse (some (make a b h g)) = cmap g.val⁻¹ := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  funext x
  simp [Branch.inverse, coordinateMap, isotropyChart, targetChart, ChartKind.representative, coord, make]
private theorem make_properties (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    Branch.Properties (some (make a b h g)) := by
  have hp : Branch.psi (some (make a b h g)) = cmap g.val := make_psi a b h g
  have hd : Branch.domain (some (make a b h g)) = omega a ∩ cmap g.val ⁻¹' omega b := rfl
  have hi := make_inverse a b h g
  have ht : Branch.targetDomain (some (make a b h g)) =
      cmap g.val '' (omega a ∩ cmap g.val ⁻¹' omega b) := by rw [Branch.targetDomain, hp, hd]
  have hl (x : M F) : cmap g.val⁻¹ (cmap g.val x) = x := (coordHomeo g.val).left_inv x
  have hr (x : M F) : cmap g.val (cmap g.val⁻¹ x) = x := (coordHomeo g.val).right_inv x
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (make a b h g).arrow.isOpen_domain
  · rw [ht]; exact (coordHomeo g.val).isOpenMap _ (make a b h g).arrow.isOpen_domain
  · exact (make a b h g).source_shrinking
  · rintro _ ⟨x,hx,rfl⟩; exact (make a b h g).target_shrinking hx
  · rw [hi, ht, hd]; rintro _ ⟨x,hx,rfl⟩; rwa [hl]
  · rw [hi, hp]; exact fun x _ => hl x
  · rw [hi, hp]; exact fun x _ => hr x
  · rw [hp]; exact (coord_smooth g.val).contDiffOn
  · rw [hi]; exact (coord_smooth g.val⁻¹).contDiffOn
  · rw [hp]; exact fun x _ => q_coord a b h g x
private theorem overlap_component (a b : ShrunkChart F ζ hζ U R P H)
    (x : M F) (hx : q a x ∈ b.baseDomain) : a.component = b.component := by
  obtain ⟨y, hy⟩ := hx
  have hh : (H.atlas U).components
      ⟨b.component, KPCuspSiegel.projection F
        (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H b.component) y.val⟩ =
    (H.atlas U).components
      ⟨a.component, KPCuspSiegel.projection F
        (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
          (labeledA (placeEquiv F ζ hζ) x)⟩ := by
    simpa only [(H.atlas U).components_formula, ShrunkChart.toBase, q] using hy
  exact (congrArg Sigma.fst ((H.atlas U).components.injective hh)).symm
private theorem overlap_iff (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) (x : M F) :
    (x ∈ omega a ∧ q a x ∈ b.baseDomain) ↔
      ∃ g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component),
        x ∈ (make a b h g).arrow.domain := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  constructor
  · rintro ⟨hx, y, hy⟩
    have hi : Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U
        ((H.atlas U).representative i)) := by
      intro u v huv
      have he : (H.atlas U).components ⟨i,u⟩ = (H.atlas U).components ⟨i,v⟩ := by
        simpa only [(H.atlas U).components_formula] using huv
      exact eq_of_heq (Sigma.mk.inj ((H.atlas U).components.injective he)).2
    obtain ⟨g,hg⟩ := Quotient.exact (hi hy)
    change g • labeledA (placeEquiv F ζ hζ) x = y.val at hg
    refine ⟨g, hx, ?_⟩
    change labeledA (placeEquiv F ζ hζ) (cmap g.val x) ∈ db
    rw [coord, la]
    change g • labeledA (placeEquiv F ζ hζ) x ∈ db
    rw [hg]
    exact y.property
  · rintro ⟨g,hx,hg⟩
    refine ⟨hx, ⟨⟨labeledA (placeEquiv F ζ hζ) (cmap g.val x), hg⟩, ?_⟩⟩
    exact q_coord _ _ rfl g x
private theorem none_properties (a b : ShrunkChart F ζ hζ U R P H) :
    Branch.Properties (none : Branch a b) := by
  refine ⟨isOpen_empty, ?_, Set.empty_subset _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [Branch.targetDomain, Branch.psi, Branch.inverse, Branch.domain, Set.MapsTo,
    contDiffOn_empty]
private theorem central_comm (r : rootsOfUnity 3 F)
    (c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ r * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ r := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨r,rfl⟩) c).symm
private theorem comparison_delta {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F:=F) (ζ:=ζ) (hζ:=hζ) (U:=U) (R:=R) (P:=P) (H:=H) i}
    (k l : Arrow a b) :
    ∃ u : U.toOpenSubgroup,
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (l.gamma * k.gamma⁻¹) *
          (H.atlas U).representative i =
        KPCuspGenuineMonodromy.central F ζ hζ (l.root * k.root⁻¹)⁻¹ *
          (H.atlas U).representative i * u.val := by
  refine ⟨l.levelLift * k.levelLift⁻¹, ?_⟩
  let f := KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
  let c := KPCuspGenuineMonodromy.central F ζ hζ
  let t := (H.atlas U).representative i
  have hk : f k.gamma = c k.root⁻¹ * t * k.levelLift.val * t⁻¹ := by
    have hh := congrArg (fun z => z * t⁻¹) k.finite_comparison
    simpa [t, mul_assoc] using hh
  have hl : f l.gamma = c l.root⁻¹ * t * l.levelLift.val * t⁻¹ := by
    have hh := congrArg (fun z => z * t⁻¹) l.finite_comparison
    simpa [t, mul_assoc] using hh
  change f (l.gamma * k.gamma⁻¹) * t = c (l.root * k.root⁻¹)⁻¹ * t * _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  rw [hk, hl]
  simp only [mul_inv_rev, inv_inv, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hc (z : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) : c k.root * z = z * c k.root := central_comm k.root z
  have hc2 : c k.root * (c l.root)⁻¹ = (c l.root)⁻¹ * c k.root := hc _
  change _ = c k.root * (c l.root)⁻¹ * t * (l.levelLift.val * k.levelLift.val⁻¹)
  calc
    _ = (c l.root)⁻¹ * (t * l.levelLift.val * k.levelLift.val⁻¹ * t⁻¹) * c k.root * t := by group
    _ = (c l.root)⁻¹ * c k.root * (t * l.levelLift.val * k.levelLift.val⁻¹ * t⁻¹) * t := by simpa only [mul_assoc] using congrArg (fun z => (c l.root)⁻¹ * z * t) (hc (t * l.levelLift.val * k.levelLift.val⁻¹ * t⁻¹)).symm
    _ = _ := by rw [← hc2]; group
private theorem separated (b : ShrunkChart F ζ hζ U R P H)
    (g : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H b.component)
    (x : KPCuspGenuineMonodromy.SymmetricSpace F)
    (hx : x ∈ b.domain) (hg : g • x ∈ b.domain) : g ∈ b.Isotropy := by
  open KPContSectorPhaseComponentCharts in
    let g' : ArchComponent F ζ hζ U R P H b.component :=
      ⟨complexProjectiveEmbedding F g.val, Subgroup.mem_map.mpr ⟨g.val,g.property,rfl⟩⟩
    have hh : g' ∈ MulAction.stabilizer _ b.center :=
      b.larger.separated g' ⟨g • x,
        ⟨x,b.closure_subset (subset_closure hx),complexProjectiveEmbedding_smul F g.val x⟩,
        b.closure_subset (subset_closure hg)⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have ht := MulAction.mem_stabilizer_iff.mp hh
    change complexProjectiveEmbedding F g.val • b.center = b.center at ht
    rwa [complexProjectiveEmbedding_smul] at ht
private theorem T_labels {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F:=F) (ζ:=ζ) (hζ:=hζ) (U:=U) (R:=R) (P:=P) (H:=H) i}
    (k l : Arrow a b) (hg : k.gamma = l.gamma) (hr : k.root = l.root)
    (x : M F) (hk : x ∈ k.domain) (hl : x ∈ l.domain) : T k x hk = T l x hl := by
  apply LinearIsometryEquiv.ext
  intro v
  change twistedOperator k x v = twistedOperator l x v
  simp only [twistedOperator, Q, Arrow.phase, Arrow.psi, hg, hr]
private theorem make_comparison (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g f : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component))
    (x : M F) (hx : x ∈ (make a b h g).arrow.domain ∩ (make a b h f).arrow.domain) :
    ∃ (γ : Gamma b) (V : Set (M F)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ (make a b h g).arrow.domain ∩ (make a b h f).arrow.domain ∧
      ∀ (y : M F) (hy : y ∈ V),
        ∃ (hk : y ∈ (make a b h g).arrow.domain) (hl : y ∈ (make a b h f).arrow.domain),
          (make a b h f).arrow.psi y = (isotropyArrow b γ).psi ((make a b h g).arrow.psi y) ∧
          T (make a b h f).arrow y hl = (T (make a b h g).arrow y hk).trans
            (T (isotropyArrow b γ) ((make a b h g).arrow.psi y)
              ((make a b h g).target_larger hk)) := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  let a : ShrunkChart F ζ hζ U R P H := ⟨i,ca,oa,da,dao,dac,das,dai⟩
  let b : ShrunkChart F ζ hζ U R P H := ⟨i,cb,ob,db,dbo,dbc,dbs,dbi⟩
  let k := (make a b rfl g).arrow
  let l := (make a b rfl f).arrow
  let δ := f * g⁻¹
  have hδ (y : M F) : cmap δ.val (cmap g.val y) = cmap f.val y := by
    rw [← coord_mul]
    congr 1
    simp [δ, mul_assoc]
  have hs : δ ∈ b.Isotropy := separated b δ
    (labeledA (placeEquiv F ζ hζ) (cmap g.val x)) hx.1.2 (by
      change δ.val • labeledA (placeEquiv F ζ hζ) (cmap g.val x) ∈ b.domain
      rw [← la (δ.val • labeledA (placeEquiv F ζ hζ) (cmap g.val x))]
      change labeledA (placeEquiv F ζ hζ) (cmap δ.val (cmap g.val x)) ∈ b.domain
      rw [hδ]
      exact hx.2.2)
  let γ : Gamma b := ⟨(⟨δ,hs⟩, l.root * k.root⁻¹), comparison_delta k l⟩
  refine ⟨γ, k.domain ∩ l.domain, k.isOpen_domain.inter l.isOpen_domain, hx,
    Set.Subset.refl _, ?_⟩
  intro y hy
  refine ⟨hy.1, hy.2, ?_, ?_⟩
  · have ht : (isotropyArrow b γ).psi = cmap δ.val := chart_coord b b rfl δ
    rw [make_psi a b rfl f, make_psi a b rfl g, ht]
    exact (hδ y).symm
  · have hc := T_comp (isotropyArrow b γ) k y hy.1 ((make a b rfl g).target_larger hy.1)
    refine Eq.trans ?_ hc
    apply T_labels
    · change f = (f * g⁻¹) * g
      group
    · change l.root = (l.root * k.root⁻¹) * k.root
      group
private theorem build (a b : ShrunkChart F ζ hζ U R P H) : Nonempty (Enumeration a b) := by
  by_cases h : a.component = b.component
  · let G := KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)
    letI : Countable G := component_countable a.component
    obtain ⟨enum, henum⟩ := exists_surjective_nat G
    refine ⟨{
      branch := fun k => some (make a b h (enum k))
      properties := fun k => make_properties a b h (enum k)
      covers := ?_
      local_comparison := ?_ }⟩
    · ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨k,hk⟩
        exact (overlap_iff a b h x).mpr ⟨enum k,hk⟩
      · intro hx
        obtain ⟨g,hg⟩ := (overlap_iff a b h x).mp hx
        obtain ⟨k,rfl⟩ := henum g
        exact ⟨k,hg⟩
    · intro k l x hx
      exact make_comparison a b h (enum k) (enum l) x hx
  · refine ⟨{
      branch := fun _ => none
      properties := fun _ => none_properties a b
      covers := ?_
      local_comparison := ?_ }⟩
    · ext x
      simp only [Branch.domain, Set.iUnion_empty, Set.mem_empty_iff_false, Set.mem_setOf_eq,
        false_iff, not_and]
      intro _ hb
      exact h (overlap_component a b x hb)
    · intro k l x hx
      exact False.elim hx.1

theorem enumeration_exists (a b : ShrunkChart F ζ hζ U R P H) :
    Nonempty (Enumeration a b) :=
  build a b

end DedekindZetaZeroFree.KPContCotangentOverlapRationalBranches

namespace DedekindZetaZeroFree

theorem kp_cont_cotangent_overlap_rational_branches
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (cover : KPContActualCotangentCountableShrinking.CountableCover F ζ hζ U R P H)
    (a : KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H)
    (ha : a.Properties) (n : ℕ) :
    Nonempty (KPContCotangentOverlapRationalBranches.Enumeration a (cover.chart n)) := by
  exact KPContCotangentOverlapRationalBranches.build a (cover.chart n)

end DedekindZetaZeroFree

end
