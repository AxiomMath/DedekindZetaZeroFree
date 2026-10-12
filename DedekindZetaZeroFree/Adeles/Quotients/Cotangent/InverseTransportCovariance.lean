module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.BorelOverlapDescent
public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.BorelCoverRefinement

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentTransportChoiceAlgebra

open KPContActualCotangentCountableShrinking
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem eqRec_places {i j : Fin (H.atlas U).componentCount} (h : i = j)
    (s : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i) :
    (h ▸ s).places = s.places := by
  cases h; rfl

private theorem eqRec_rep {i j : Fin (H.atlas U).componentCount} (h : i = j)
    (s : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i) :
    (h ▸ s).kind.representative = s.kind.representative := by
  cases h; rfl

private theorem eqRec_splitting {i j : Fin (H.atlas U).componentCount} (h : i = j)
    (s : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i) :
    (h ▸ s).splitting = s.splitting := by
  cases h; rfl

private theorem eqRec_cast_symm {i j : Fin (H.atlas U).componentCount} (h : i = j)
    (y : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) j) :
    h ▸ (h.symm ▸ y) = y := by
  cases h; rfl

private theorem eqRec_trans_symm {i j k : Fin (H.atlas U).componentCount}
    (h₁ : i = j) (h₂ : j = k)
    (X : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) k) :
    h₁.symm ▸ (h₂.symm ▸ X) = (h₁.trans h₂).symm ▸ X := by
  cases h₁; cases h₂; rfl

private theorem targetChart_places (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    (targetChart a b h).places = placeEquiv F ζ hζ := by
  unfold targetChart
  rw [eqRec_places]
  rfl

private theorem targetChart_rep (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    (targetChart a b h).kind.representative = 1 := by
  unfold targetChart
  rw [eqRec_rep]
  rfl

private theorem targetChart_splitting (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    (targetChart a b h).splitting = fun _ => 1 := by
  unfold targetChart
  rw [eqRec_splitting]
  rfl

private theorem targetChart_cast (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    h ▸ targetChart a b h = isotropyChart b := by
  unfold targetChart
  exact eqRec_cast_symm h (isotropyChart b)

private theorem shrunkChart_separated (C : ShrunkChart F ζ hζ U R P H)
    (g : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H C.component)
    (x : KPCuspGenuineMonodromy.SymmetricSpace F)
    (hx : x ∈ C.domain) (hg : g • x ∈ C.domain) : g ∈ C.Isotropy := by
  let g' : KPContSectorPhaseComponentCharts.ArchComponent F ζ hζ U R P H C.component :=
    ⟨KPContSectorPhaseComponentCharts.complexProjectiveEmbedding F g.val,
      Subgroup.mem_map.mpr ⟨g.val, g.property, rfl⟩⟩
  have hh : g' ∈ MulAction.stabilizer _ C.center :=
    C.larger.separated g' ⟨g • x,
      ⟨x, C.closure_subset (subset_closure hx),
        KPContSectorPhaseComponentCharts.complexProjectiveEmbedding_smul F g.val x⟩,
      C.closure_subset (subset_closure hg)⟩
  apply MulAction.mem_stabilizer_iff.mpr
  have ht := MulAction.mem_stabilizer_iff.mp hh
  change KPContSectorPhaseComponentCharts.complexProjectiveEmbedding F g.val • C.center =
    C.center at ht
  rwa [KPContSectorPhaseComponentCharts.complexProjectiveEmbedding_smul] at ht

private theorem labeledA_labeledAInv' (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA p (labeledAInv p y) = y := by
  funext k
  simp [labeledAInv, labeledA]

 def Phi (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (γ : KPCuspArithmetic.PGL2 F) (x : M F) : M F :=
  labeledAInv (placeEquiv F ζ hζ) (γ • labeledA (placeEquiv F ζ hζ) x)

private theorem Phi_mul (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (γ δ : KPCuspArithmetic.PGL2 F) (x : M F) :
    Phi ζ hζ (γ * δ) x = Phi ζ hζ γ (Phi ζ hζ δ x) := by
  simp only [Phi, mul_smul, labeledA_labeledAInv']

private theorem arrow_psi_eq_Phi {i : Fin (H.atlas U).componentCount}
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (hA : A.places = placeEquiv F ζ hζ) (hAr : A.kind.representative = 1)
    (hB : B.places = placeEquiv F ζ hζ) (hBr : B.kind.representative = 1)
    (e : Arrow A B) : e.psi = Phi ζ hζ (e.gamma : KPCuspArithmetic.PGL2 F) := by
  funext x
  simp only [Arrow.psi, coordinateMap, Phi, hA, hAr, hB, hBr]
  simp

 def Op (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (γ : KPCuspArithmetic.PGL2 F) (r : rootsOfUnity 3 F) (x : M F) :
    E F →L[ℂ] E F :=
  (KPCuspGenuineMonodromy.chi F ζ hζ r : ℂ) •
    KPContCotangentRealOrthogonalComplexification.operatorComplexification
      (Fin (d F) × Fin 3)
      ((CotangentLogCoframe.C (d F) (Phi ζ hζ γ x)).toContinuousLinearMap.comp
        ((fderiv ℝ (Phi ζ hζ γ) x).comp
          (CotangentLogCoframe.H (d F) x).toContinuousLinearMap))

private theorem twistedOperator_eq_Op {i : Fin (H.atlas U).componentCount}
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (hA : A.places = placeEquiv F ζ hζ) (hAr : A.kind.representative = 1)
    (hAs : A.splitting = fun _ => 1)
    (hB : B.places = placeEquiv F ζ hζ) (hBr : B.kind.representative = 1)
    (hBs : B.splitting = fun _ => 1)
    (e : Arrow A B) (x : M F) :
    twistedOperator e x = Op ζ hζ (e.gamma : KPCuspArithmetic.PGL2 F) e.root x := by
  have hpsi := arrow_psi_eq_Phi hA hAr hB hBr e
  have hph : e.phase x = (KPCuspGenuineMonodromy.chi F ζ hζ e.root : ℂ) := by
    simp only [Arrow.phase, hBs, hAs]
    congr 1
    simp
  rw [twistedOperator, Op, hph]
  congr 1
  simp only [Q, hpsi]

 def castArrow {i j : Fin (H.atlas U).componentCount} (h : i = j)
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (e : Arrow A B) : Arrow (h ▸ A) (h ▸ B) :=
  cast (by cases h; rfl) e

private theorem arrow_gamma_index_cast {i j : Fin (H.atlas U).componentCount} (h : i = j)
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (e : Arrow A B) :
    ((castArrow h e).gamma : KPCuspArithmetic.PGL2 F) = (e.gamma : KPCuspArithmetic.PGL2 F) := by
  cases h; rfl

private theorem arrow_gamma_chart_cast {i : Fin (H.atlas U).componentCount}
    {A B B' : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (h : B = B') (e : Arrow A B) : (h ▸ e).gamma = e.gamma := by
  cases h; rfl

private theorem arrow_root_index_cast {i j : Fin (H.atlas U).componentCount} (h : i = j)
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (e : Arrow A B) : (castArrow h e).root = e.root := by
  cases h; rfl

private theorem arrow_root_chart_cast {i : Fin (H.atlas U).componentCount}
    {A B B' : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (h : B = B') (e : Arrow A B) : (h ▸ e).root = e.root := by
  cases h; rfl

private theorem arrow_psi_index_cast {i j : Fin (H.atlas U).componentCount} (h : i = j)
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (e : Arrow A B) : (castArrow h e).psi = e.psi := by
  cases h; rfl

private theorem arrow_psi_chart_cast {i : Fin (H.atlas U).componentCount}
    {A B B' : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (h : B = B') (e : Arrow A B) : (h ▸ e).psi = e.psi := by
  cases h; rfl

private theorem arrow_domain_index_cast {i j : Fin (H.atlas U).componentCount} (h : i = j)
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (e : Arrow A B) : (castArrow h e).domain = e.domain := by
  cases h; rfl

private theorem arrow_domain_chart_cast {i : Fin (H.atlas U).componentCount}
    {A B B' : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (h : B = B') (e : Arrow A B) : (h ▸ e).domain = e.domain := by
  cases h; rfl

private theorem arrow_finite_comparison_index_cast {i j : Fin (H.atlas U).componentCount}
    (h : i = j)
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (e : Arrow A B) :
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ ((castArrow h e).gamma) *
        (H.atlas U).representative j =
      KPCuspGenuineMonodromy.central F ζ hζ ((castArrow h e).root)⁻¹ *
        (H.atlas U).representative j * (castArrow h e).levelLift.val := by
  cases h; exact e.finite_comparison

private theorem T_eq_of_twistedOperator {i j : Fin (H.atlas U).componentCount}
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    {A' B' : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) j}
    (e : Arrow A B) (e' : Arrow A' B') (x x' : M F)
    (hx : x ∈ e.domain) (hx' : x' ∈ e'.domain)
    (h : twistedOperator e x = twistedOperator e' x') : T e x hx = T e' x' hx' := by
  apply LinearIsometryEquiv.ext
  intro v
  change twistedOperator e x v = twistedOperator e' x' v
  rw [h]

private theorem T_domain_irrel {i : Fin (H.atlas U).componentCount}
    {A B : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (e : Arrow A B) (x : M F) (h1 h2 : x ∈ e.domain) : T e x h1 = T e x h2 := by
  apply LinearIsometryEquiv.ext
  intro v
  rfl

private theorem central_comm' (ε : rootsOfUnity 3 F)
    (c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) c).symm

private theorem comparison_mul {i : Fin (H.atlas U).componentCount}
    (R₀ : KPCuspGenuineMonodromy.FiniteCover F ζ hζ)
    (γ δ : KPCuspGenuineMonodromy.Component F ζ hζ U R₀)
    (c d : rootsOfUnity 3 F) (u v : U.toOpenSubgroup)
    (hγ : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * R₀ =
      KPCuspGenuineMonodromy.central F ζ hζ c * R₀ * u.val)
    (hδ : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ * R₀ =
      KPCuspGenuineMonodromy.central F ζ hζ d * R₀ * v.val) :
    ∃ w : U.toOpenSubgroup,
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (γ * δ) * R₀ =
        KPCuspGenuineMonodromy.central F ζ hζ (c * d) * R₀ * w.val := by
  refine ⟨u * v, ?_⟩
  change KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (γ * δ) * R₀ =
    KPCuspGenuineMonodromy.central F ζ hζ (c * d) * R₀ *
      ((u : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) * v)
  calc KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (γ * δ) * R₀
      = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
          (KPCuspGenuineMonodromy.central F ζ hζ d * R₀ * v.val) := by
        rw [map_mul, mul_assoc, hδ]
    _ = KPCuspGenuineMonodromy.central F ζ hζ d *
          (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * R₀) * v.val := by
        rw [← mul_assoc, ← mul_assoc, ← central_comm' (F := F) (ζ := ζ) (hζ := hζ) d]
        group
    _ = KPCuspGenuineMonodromy.central F ζ hζ d *
          (KPCuspGenuineMonodromy.central F ζ hζ c * R₀ * u.val) * v.val := by rw [hγ]
    _ = KPCuspGenuineMonodromy.central F ζ hζ (c * d) * R₀ * (u.val * v.val) := by
        have hcd : KPCuspGenuineMonodromy.central F ζ hζ (c * d) =
            KPCuspGenuineMonodromy.central F ζ hζ d *
              KPCuspGenuineMonodromy.central F ζ hζ c := by
          rw [map_mul]
          exact (central_comm' (F := F) (ζ := ζ) (hζ := hζ) d
            (KPCuspGenuineMonodromy.central F ζ hζ c)).symm
        rw [hcd]
        group

private theorem comparison_inv {i : Fin (H.atlas U).componentCount}
    (R₀ : KPCuspGenuineMonodromy.FiniteCover F ζ hζ)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U R₀)
    (c : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hγ : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * R₀ =
      KPCuspGenuineMonodromy.central F ζ hζ c * R₀ * u.val) :
    ∃ w : U.toOpenSubgroup,
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ⁻¹ * R₀ =
        KPCuspGenuineMonodromy.central F ζ hζ c⁻¹ * R₀ * w.val := by
  refine ⟨u⁻¹, ?_⟩
  have hγ' : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ =
      KPCuspGenuineMonodromy.central F ζ hζ c * R₀ * u.val * R₀⁻¹ := by
    rw [← hγ]; group
  have hcinv : ((KPCuspGenuineMonodromy.central F ζ hζ) c)⁻¹ =
      KPCuspGenuineMonodromy.central F ζ hζ c⁻¹ :=
    (map_inv (KPCuspGenuineMonodromy.central F ζ hζ) c).symm
  rw [Subgroup.coe_inv, map_inv, hγ']
  simp only [mul_inv_rev, inv_inv]
  rw [hcinv]
  rw [central_comm' (F := F) (ζ := ζ) (hζ := hζ) c⁻¹ R₀]
  calc R₀ * ((↑u)⁻¹ * (R₀⁻¹ * KPCuspGenuineMonodromy.central F ζ hζ c⁻¹)) * R₀
      = R₀ * (↑u)⁻¹ * R₀⁻¹ * KPCuspGenuineMonodromy.central F ζ hζ c⁻¹ * R₀ := by group
    _ = R₀ * (↑u)⁻¹ * R₀⁻¹ * (KPCuspGenuineMonodromy.central F ζ hζ c⁻¹ * R₀) := by group
    _ = R₀ * (↑u)⁻¹ * R₀⁻¹ * (R₀ * KPCuspGenuineMonodromy.central F ζ hζ c⁻¹) := by
          rw [central_comm' (F := F) (ζ := ζ) (hζ := hζ) c⁻¹ R₀]
    _ = R₀ * (↑u)⁻¹ * KPCuspGenuineMonodromy.central F ζ hζ c⁻¹ := by group
    _ = R₀ * (KPCuspGenuineMonodromy.central F ζ hζ c⁻¹ * (↑u)⁻¹) := by
          rw [mul_assoc R₀ (↑u)⁻¹ (KPCuspGenuineMonodromy.central F ζ hζ c⁻¹)]
          rw [← central_comm' (F := F) (ζ := ζ) (hζ := hζ) c⁻¹
            ((u : KPCuspGenuineMonodromy.FiniteCover F ζ hζ)⁻¹)]
    _ = R₀ * KPCuspGenuineMonodromy.central F ζ hζ c⁻¹ * (↑u)⁻¹ := by group

private theorem cast_lifted_places {i j : Fin (H.atlas U).componentCount} (h : i = j)
    (s : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i)
    (hs : s.places = placeEquiv F ζ hζ) :
    (h ▸ s).places = placeEquiv F ζ hζ := by
  rw [eqRec_places, hs]

private theorem cast_lifted_rep {i j : Fin (H.atlas U).componentCount} (h : i = j)
    (s : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i)
    (hs : s.kind.representative = 1) :
    (h ▸ s).kind.representative = 1 := by
  rw [eqRec_rep, hs]

private theorem cast_lifted_splitting {i j : Fin (H.atlas U).componentCount} (h : i = j)
    (s : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i)
    (hs : s.splitting = fun _ => 1) :
    (h ▸ s).splitting = fun _ => 1 := by
  rw [eqRec_splitting, hs]

theorem omega_subset_larger (a : ShrunkChart F ζ hζ U R P H) :
    omega a ⊆ (isotropyChart a).omega := by
  intro x hx
  exact a.closure_subset (subset_closure hx)

def EquivariantSequence (cover : CountableCover F ζ hζ U R P H)
    (f : ℕ → M F → E F) : Prop :=
  ∀ (n : ℕ) (γ : Gamma (cover.chart n)) (y : M F)
    (hy : y ∈ omega (cover.chart n)),
    f n ((isotropyArrow (cover.chart n) γ).psi y) =
      T (isotropyArrow (cover.chart n) γ) y
        (omega_subset_larger (cover.chart n) hy) (f n y)

def inverseTransport {a b : ShrunkChart F ζ hζ U R P H}
    (ψ : Branch a b) (f : M F → E F) (x : M F) (hx : x ∈ ψ.domain) : E F :=
  (ψ.transport x hx).symm (f (ψ.psi x))

structure Properties (cover : CountableCover F ζ hζ U R P H)
    (f : ℕ → M F → E F) : Prop where
  choice_independent : ∀ (a : ShrunkChart F ζ hζ U R P H) (n : ℕ)
    (ψ φ : Branch a (cover.chart n)) (x : M F)
    (hψ : x ∈ ψ.domain) (hφ : x ∈ φ.domain),
    inverseTransport ψ (f n) x hψ = inverseTransport φ (f n) x hφ
  composition : ∀ (n : ℕ)
    (a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) (cover.chart n).component)
    (θ : Arrow a b) (ψ : Arrow b (isotropyChart (cover.chart n)))
    (x : M F) (hθ : x ∈ θ.domain) (hψ : θ.psi x ∈ ψ.domain),
    (T (comp ψ θ) x ⟨hθ, hψ⟩).symm (f n (ψ.psi (θ.psi x))) =
      (T θ x hθ).symm ((T ψ (θ.psi x) hψ).symm (f n (ψ.psi (θ.psi x))))
  mixed_charts : ∀ (a b : ShrunkChart F ζ hζ U R P H) (n : ℕ)
    (θ : Branch a b) (φ : Branch a (cover.chart n))
    (ψ : Branch b (cover.chart n)) (x : M F)
    (hθ : x ∈ θ.domain) (hφ : x ∈ φ.domain) (hψ : θ.psi x ∈ ψ.domain),
    inverseTransport ψ (f n) (θ.psi x) hψ =
      θ.transport x hθ (inverseTransport φ (f n) x hφ)
  identity : ∀ (n : ℕ) (y : M F) (hy : y ∈ omega (cover.chart n)),
    (T (KPContCotangentActualOverlap.identity (isotropyChart (cover.chart n)))
      y (omega_subset_larger (cover.chart n) hy)).symm
        (f n ((KPContCotangentActualOverlap.identity (isotropyChart (cover.chart n))).psi y)) =
      f n y
  fixed_fiber : ∀ (n : ℕ) (y : M F) (hy : y ∈ omega (cover.chart n)),
    f n y ∈ Fixed (cover.chart n) y (omega_subset_larger (cover.chart n) hy)
  zero_fixed_fiber : ∀ (n : ℕ) (y : M F) (hy : y ∈ omega (cover.chart n)),
    Fixed (cover.chart n) y (omega_subset_larger (cover.chart n) hy) = ⊥ → f n y = 0

end DedekindZetaZeroFree.KPContActualCotangentTransportChoiceAlgebra

namespace DedekindZetaZeroFree

open KPContActualCotangentCountableShrinking
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentOverlapRationalBranches
open KPContActualCotangentTransportChoiceAlgebra

theorem kp_cont_actual_cotangent_transport_choice_algebra
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : CountableCover F ζ hζ U R P H)
    (f : ℕ → M F → E F) (hf : EquivariantSequence cover f) :
    KPContActualCotangentTransportChoiceAlgebra.Properties cover f := by
  have hCI : ∀ (a : ShrunkChart F ζ hζ U R P H) (n : ℕ)
      (ψ φ : Branch a (cover.chart n)) (x : M F)
      (hψ : x ∈ ψ.domain) (hφ : x ∈ φ.domain),
      inverseTransport ψ (f n) x hψ = inverseTransport φ (f n) x hφ := by
    intro a n ψ φ x hψ hφ
    cases ψ with
    | none => exact hψ.elim
    | some e₁ =>
      cases φ with
      | none => exact hφ.elim
      | some e₂ =>
        dsimp only [inverseTransport, Branch.transport, Branch.psi, Branch.domain] at *
        have h₁ := e₁.component_eq
        have h₂ := e₂.component_eq
        have hpsi₁ : e₁.arrow.psi = Phi ζ hζ (e₁.arrow.gamma : KPCuspArithmetic.PGL2 F) :=
          arrow_psi_eq_Phi rfl rfl
            (targetChart_places a (cover.chart n) h₁)
            (targetChart_rep a (cover.chart n) h₁) e₁.arrow
        have hpsi₂ : e₂.arrow.psi = Phi ζ hζ (e₂.arrow.gamma : KPCuspArithmetic.PGL2 F) :=
          arrow_psi_eq_Phi rfl rfl
            (targetChart_places a (cover.chart n) h₂)
            (targetChart_rep a (cover.chart n) h₂) e₂.arrow
        set γ₁ : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H
            (cover.chart n).component := (castArrow h₁ e₁.arrow).gamma with hγ₁def
        set γ₂ : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H
            (cover.chart n).component := (castArrow h₂ e₂.arrow).gamma with hγ₂def
        set r₁ : rootsOfUnity 3 F := (castArrow h₁ e₁.arrow).root with hr₁def
        set r₂ : rootsOfUnity 3 F := (castArrow h₂ e₂.arrow).root with hr₂def
        have hγ₁coe : (γ₁ : KPCuspArithmetic.PGL2 F) =
            (e₁.arrow.gamma : KPCuspArithmetic.PGL2 F) := by
          rw [hγ₁def]; exact arrow_gamma_index_cast h₁ e₁.arrow
        have hγ₂coe : (γ₂ : KPCuspArithmetic.PGL2 F) =
            (e₂.arrow.gamma : KPCuspArithmetic.PGL2 F) := by
          rw [hγ₂def]; exact arrow_gamma_index_cast h₂ e₂.arrow
        have hr₁ : r₁ = e₁.arrow.root := by rw [hr₁def]; exact arrow_root_index_cast h₁ e₁.arrow
        have hr₂ : r₂ = e₂.arrow.root := by rw [hr₂def]; exact arrow_root_index_cast h₂ e₂.arrow
        have hx₁ : labeledA (placeEquiv F ζ hζ) (e₁.arrow.psi x) =
            (e₁.arrow.gamma : KPCuspArithmetic.PGL2 F) • labeledA (placeEquiv F ζ hζ) x := by
          rw [hpsi₁]; simp only [Phi, labeledA_labeledAInv']
        have hx₂ : labeledA (placeEquiv F ζ hζ) (e₂.arrow.psi x) =
            (e₂.arrow.gamma : KPCuspArithmetic.PGL2 F) • labeledA (placeEquiv F ζ hζ) x := by
          rw [hpsi₂]; simp only [Phi, labeledA_labeledAInv']
        have hgc : ((γ₂ * γ₁⁻¹ : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H
            (cover.chart n).component) : KPCuspArithmetic.PGL2 F) *
            (e₁.arrow.gamma : KPCuspArithmetic.PGL2 F) =
            (e₂.arrow.gamma : KPCuspArithmetic.PGL2 F) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hγ₂coe, hγ₁coe]
          group
        have hstab : γ₂ * γ₁⁻¹ ∈ (cover.chart n).Isotropy := by
          apply shrunkChart_separated (cover.chart n) (γ₂ * γ₁⁻¹)
          · exact e₁.target_shrinking hψ
          · have hstep : ((γ₂ * γ₁⁻¹ : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H
                (cover.chart n).component) : KPCuspArithmetic.PGL2 F) •
                labeledA (placeEquiv F ζ hζ) (e₁.arrow.psi x) ∈ (cover.chart n).domain := by
              rw [hx₁, ← mul_smul, hgc, ← hx₂]
              exact e₂.target_shrinking hφ
            rw [show (γ₂ * γ₁⁻¹) • labeledA (placeEquiv F ζ hζ) (e₁.arrow.psi x) =
                ((γ₂ * γ₁⁻¹ : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H
                  (cover.chart n).component) : KPCuspArithmetic.PGL2 F) •
                  labeledA (placeEquiv F ζ hζ) (e₁.arrow.psi x) from rfl]
            exact hstep
        have hcmp₁ : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ₁ *
            (H.atlas U).representative (cover.chart n).component =
          KPCuspGenuineMonodromy.central F ζ hζ r₁⁻¹ *
            (H.atlas U).representative (cover.chart n).component *
            ((castArrow h₁ e₁.arrow).levelLift).val := by
          rw [hγ₁def, hr₁def]
          exact arrow_finite_comparison_index_cast h₁ e₁.arrow
        have hcmp₂ : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ₂ *
            (H.atlas U).representative (cover.chart n).component =
          KPCuspGenuineMonodromy.central F ζ hζ r₂⁻¹ *
            (H.atlas U).representative (cover.chart n).component *
            ((castArrow h₂ e₂.arrow).levelLift).val := by
          rw [hγ₂def, hr₂def]
          exact arrow_finite_comparison_index_cast h₂ e₂.arrow
        have hfin : ∃ u : U.toOpenSubgroup,
            KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (γ₂ * γ₁⁻¹) *
              (H.atlas U).representative (cover.chart n).component =
            KPCuspGenuineMonodromy.central F ζ hζ (r₂ * r₁⁻¹)⁻¹ *
              (H.atlas U).representative (cover.chart n).component * u.val := by
          obtain ⟨w₁, hw₁⟩ := comparison_inv (R := R) (P := P) (H := H)
            (i := (cover.chart n).component)
            ((H.atlas U).representative (cover.chart n).component) γ₁ r₁⁻¹
            ((castArrow h₁ e₁.arrow).levelLift) hcmp₁
          obtain ⟨w, hw⟩ := comparison_mul (R := R) (P := P) (H := H)
            (i := (cover.chart n).component)
            ((H.atlas U).representative (cover.chart n).component) γ₂ γ₁⁻¹ r₂⁻¹ r₁
            ((castArrow h₂ e₂.arrow).levelLift) w₁ hcmp₂ hw₁
          refine ⟨w, ?_⟩
          rw [hw]
          rw [show (r₂ * r₁⁻¹)⁻¹ = r₂⁻¹ * r₁ from by rw [mul_inv_rev, inv_inv]; exact mul_comm _ _]
        let δ : Gamma (cover.chart n) := ⟨(⟨γ₂ * γ₁⁻¹, hstab⟩, r₂ * r₁⁻¹), hfin⟩
        have hδval : ((δ.val.1.val : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H
            (cover.chart n).component) : KPCuspArithmetic.PGL2 F) =
            (γ₂ : KPCuspArithmetic.PGL2 F) * (γ₁ : KPCuspArithmetic.PGL2 F)⁻¹ := rfl
        set E₁ : Arrow (h₁ ▸ isotropyChart a) (isotropyChart (cover.chart n)) :=
          (targetChart_cast a (cover.chart n) h₁) ▸ (castArrow h₁ e₁.arrow) with hE₁def
        have hE₁γ : E₁.gamma = γ₁ := by
          rw [hE₁def, hγ₁def]
          exact arrow_gamma_chart_cast (targetChart_cast a (cover.chart n) h₁)
            (castArrow h₁ e₁.arrow)
        have hE₁root : E₁.root = r₁ := by
          rw [hE₁def, hr₁def]
          exact arrow_root_chart_cast (targetChart_cast a (cover.chart n) h₁)
            (castArrow h₁ e₁.arrow)
        have hE₁psi : E₁.psi = e₁.arrow.psi := by
          rw [hE₁def, arrow_psi_chart_cast, arrow_psi_index_cast]
        have hxE₁ : x ∈ E₁.domain := by
          rw [hE₁def, arrow_domain_chart_cast, arrow_domain_index_cast]
          exact hψ
        have htarget : E₁.psi x ∈ (isotropyArrow (cover.chart n) δ).domain := by
          rw [hE₁psi]
          exact omega_subset_larger (cover.chart n) (e₁.target_shrinking hψ)
        have hy : e₁.arrow.psi x ∈ omega (cover.chart n) := e₁.target_shrinking hψ
        have hTE₁ : T E₁ x hxE₁ = T e₁.arrow x hψ := by
          apply T_eq_of_twistedOperator
          rw [twistedOperator_eq_Op (cast_lifted_places h₁ (isotropyChart a) rfl)
                (cast_lifted_rep h₁ (isotropyChart a) rfl)
                (cast_lifted_splitting h₁ (isotropyChart a) rfl) rfl rfl rfl E₁ x,
              twistedOperator_eq_Op rfl rfl rfl
                (targetChart_places a (cover.chart n) h₁)
                (targetChart_rep a (cover.chart n) h₁)
                (targetChart_splitting a (cover.chart n) h₁) e₁.arrow x,
              hE₁γ, hE₁root, hγ₁coe, hr₁]
        have hcompγ : ((comp (isotropyArrow (cover.chart n) δ) E₁).gamma :
            KPCuspArithmetic.PGL2 F) = (e₂.arrow.gamma : KPCuspArithmetic.PGL2 F) := by
          show ((isotropyArrow (cover.chart n) δ).gamma : KPCuspArithmetic.PGL2 F) *
            (E₁.gamma : KPCuspArithmetic.PGL2 F) = _
          rw [hE₁γ, hγ₁coe]
          change ((δ.val.1.val : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H
            (cover.chart n).component) : KPCuspArithmetic.PGL2 F) *
            (e₁.arrow.gamma : KPCuspArithmetic.PGL2 F) = (e₂.arrow.gamma : KPCuspArithmetic.PGL2 F)
          rw [hδval, hγ₁coe, hγ₂coe]
          group
        have hcomp_root : (comp (isotropyArrow (cover.chart n) δ) E₁).root =
            e₂.arrow.root := by
          show (r₂ * r₁⁻¹) * E₁.root = e₂.arrow.root
          rw [hE₁root, hr₂, hr₁]
          group
        have hT₂ : T e₂.arrow x hφ =
            T (comp (isotropyArrow (cover.chart n) δ) E₁) x ⟨hxE₁, htarget⟩ := by
          apply T_eq_of_twistedOperator
          rw [twistedOperator_eq_Op rfl rfl rfl
                (targetChart_places a (cover.chart n) h₂)
                (targetChart_rep a (cover.chart n) h₂)
                (targetChart_splitting a (cover.chart n) h₂) e₂.arrow x,
              twistedOperator_eq_Op (cast_lifted_places h₁ (isotropyChart a) rfl)
                (cast_lifted_rep h₁ (isotropyChart a) rfl)
                (cast_lifted_splitting h₁ (isotropyChart a) rfl) rfl rfl rfl
                (comp (isotropyArrow (cover.chart n) δ) E₁) x,
              hcompγ, hcomp_root]
        have hδpsi : (isotropyArrow (cover.chart n) δ).psi (e₁.arrow.psi x) =
            e₂.arrow.psi x := by
          have h1 : (isotropyArrow (cover.chart n) δ).psi =
              Phi ζ hζ (δ.val.1.val : KPCuspArithmetic.PGL2 F) :=
            arrow_psi_eq_Phi rfl rfl rfl rfl (isotropyArrow (cover.chart n) δ)
          rw [h1, hδval, hγ₁coe, hγ₂coe, congrFun hpsi₁ x]
          rw [← Phi_mul ζ hζ
            ((e₂.arrow.gamma : KPCuspArithmetic.PGL2 F) *
              (e₁.arrow.gamma : KPCuspArithmetic.PGL2 F)⁻¹)
            (e₁.arrow.gamma : KPCuspArithmetic.PGL2 F) x]
          rw [show (e₂.arrow.gamma : KPCuspArithmetic.PGL2 F) *
              (e₁.arrow.gamma : KPCuspArithmetic.PGL2 F)⁻¹ *
              (e₁.arrow.gamma : KPCuspArithmetic.PGL2 F) =
              (e₂.arrow.gamma : KPCuspArithmetic.PGL2 F) from by group]
          rw [← congrFun hpsi₂ x]
        have hequiv := hf n δ (e₁.arrow.psi x) hy
        rw [hδpsi] at hequiv
        have hcomp := T_comp (isotropyArrow (cover.chart n) δ) E₁ x hxE₁ htarget
        have hTδ : T (isotropyArrow (cover.chart n) δ) (E₁.psi x) htarget =
            T (isotropyArrow (cover.chart n) δ) (e₁.arrow.psi x)
              (omega_subset_larger (cover.chart n) hy) := by
          have hxeq : E₁.psi x = e₁.arrow.psi x := congrFun hE₁psi x
          apply LinearIsometryEquiv.ext
          intro v
          change twistedOperator (isotropyArrow (cover.chart n) δ) (E₁.psi x) v =
            twistedOperator (isotropyArrow (cover.chart n) δ) (e₁.arrow.psi x) v
          rw [hxeq]
        rw [hT₂, hcomp, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
          hTδ, hequiv, LinearIsometryEquiv.symm_apply_apply, hTE₁]

  refine ⟨hCI, ?_, ?_, ?_, ?_, ?_⟩

  ·
    intro n a b θ ψ x hθ hψ
    rw [T_comp ψ θ x hθ hψ, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply]
  ·
    intro a b n θ φ ψ x hθ hφ hψ
    cases θ with
    | none => exact hθ.elim
    | some eθ =>
      cases φ with
      | none => exact hφ.elim
      | some eφ =>
        cases ψ with
        | none => exact hψ.elim
        | some eψ =>
          dsimp only [inverseTransport, Branch.transport, Branch.psi, Branch.domain] at *
          have hθc : a.component = b.component := eθ.component_eq
          have hψc : b.component = (cover.chart n).component := eψ.component_eq
          have hGc : a.component = (cover.chart n).component := hθc.trans hψc
          have hGt : hθc.symm ▸ targetChart b (cover.chart n) hψc =
              targetChart a (cover.chart n) hGc := by
            unfold targetChart
            exact eqRec_trans_symm hθc hψc (isotropyChart (cover.chart n))
          let Eψ' : Arrow (targetChart a b hθc)
              (hθc.symm ▸ targetChart b (cover.chart n) hψc) :=
            (show targetChart a b hθc = hθc.symm ▸ isotropyChart b from rfl) ▸
              (castArrow hθc.symm eψ.arrow)
          let C : Arrow (isotropyChart a)
              (hθc.symm ▸ targetChart b (cover.chart n) hψc) :=
            comp Eψ' eθ.arrow
          let Garrow : Arrow (isotropyChart a) (targetChart a (cover.chart n) hGc) :=
            hGt ▸ C
          have hψ' : eθ.arrow.psi x ∈ Eψ'.domain := by
            show eθ.arrow.psi x ∈ (castArrow hθc.symm eψ.arrow).domain
            rw [arrow_domain_index_cast]
            exact hψ
          have hxC : x ∈ C.domain := by
            show x ∈ eθ.arrow.domain ∩ eθ.arrow.psi ⁻¹' Eψ'.domain
            exact ⟨hθ, hψ'⟩
          have hxG : x ∈ Garrow.domain := by
            rw [arrow_domain_chart_cast hGt C]
            exact hxC
          have Gdom : Garrow.domain =
              eθ.arrow.domain ∩ eθ.arrow.psi ⁻¹' eψ.arrow.domain := by
            rw [arrow_domain_chart_cast hGt C]
            show eθ.arrow.domain ∩ eθ.arrow.psi ⁻¹' Eψ'.domain = _
            rw [show Eψ'.domain = (castArrow hθc.symm eψ.arrow).domain from rfl,
              arrow_domain_index_cast hθc.symm eψ.arrow]
          have Gpsi : Garrow.psi = eψ.arrow.psi ∘ eθ.arrow.psi := by
            rw [arrow_psi_chart_cast hGt C]
            show (comp Eψ' eθ.arrow).psi = _
            rw [KPContCotangentActualGroupoidIdentities.comp_psi,
              show Eψ'.psi = (castArrow hθc.symm eψ.arrow).psi from rfl,
              arrow_psi_index_cast hθc.symm eψ.arrow]
          have Ggamma : (Garrow.gamma : KPCuspArithmetic.PGL2 F) =
              (eψ.arrow.gamma : KPCuspArithmetic.PGL2 F) *
                (eθ.arrow.gamma : KPCuspArithmetic.PGL2 F) := by
            rw [arrow_gamma_chart_cast hGt C]
            show (Eψ'.gamma : KPCuspArithmetic.PGL2 F) *
              (eθ.arrow.gamma : KPCuspArithmetic.PGL2 F) = _
            rw [show (Eψ'.gamma : KPCuspArithmetic.PGL2 F) =
                  ((castArrow hθc.symm eψ.arrow).gamma : KPCuspArithmetic.PGL2 F)
                  from rfl,
              arrow_gamma_index_cast hθc.symm eψ.arrow]
          have Groot : Garrow.root = eψ.arrow.root * eθ.arrow.root := by
            rw [arrow_root_chart_cast hGt C]
            show Eψ'.root * eθ.arrow.root = _
            rw [show Eψ'.root = (castArrow hθc.symm eψ.arrow).root from rfl,
              arrow_root_index_cast hθc.symm eψ.arrow]
          have hTψ' : T Eψ' (eθ.arrow.psi x) hψ' =
              T eψ.arrow (eθ.arrow.psi x) hψ := by
            apply T_eq_of_twistedOperator
            rw [twistedOperator_eq_Op (targetChart_places a b hθc) (targetChart_rep a b hθc)
                  (targetChart_splitting a b hθc)
                  (cast_lifted_places hθc.symm (targetChart b (cover.chart n) hψc)
                    (targetChart_places b (cover.chart n) hψc))
                  (cast_lifted_rep hθc.symm (targetChart b (cover.chart n) hψc)
                    (targetChart_rep b (cover.chart n) hψc))
                  (cast_lifted_splitting hθc.symm (targetChart b (cover.chart n) hψc)
                    (targetChart_splitting b (cover.chart n) hψc)) Eψ' (eθ.arrow.psi x),
                twistedOperator_eq_Op rfl rfl rfl
                  (targetChart_places b (cover.chart n) hψc)
                  (targetChart_rep b (cover.chart n) hψc)
                  (targetChart_splitting b (cover.chart n) hψc) eψ.arrow (eθ.arrow.psi x),
                show (Eψ'.gamma : KPCuspArithmetic.PGL2 F) =
                  ((castArrow hθc.symm eψ.arrow).gamma : KPCuspArithmetic.PGL2 F) from rfl,
                arrow_gamma_index_cast hθc.symm eψ.arrow,
                show Eψ'.root = (castArrow hθc.symm eψ.arrow).root from rfl,
                arrow_root_index_cast hθc.symm eψ.arrow]
          have hTcomp : T C x hxC =
              (T eθ.arrow x hθ).trans (T Eψ' (eθ.arrow.psi x) hψ') := by
            rw [T_domain_irrel C x hxC ⟨hθ, hψ'⟩]
            exact T_comp Eψ' eθ.arrow x hθ hψ'
          have hTC : T Garrow x hxG = T C x hxC := by
            apply T_eq_of_twistedOperator
            rw [twistedOperator_eq_Op rfl rfl rfl
                  (targetChart_places a (cover.chart n) hGc)
                  (targetChart_rep a (cover.chart n) hGc)
                  (targetChart_splitting a (cover.chart n) hGc) Garrow x,
                twistedOperator_eq_Op rfl rfl rfl
                  (cast_lifted_places hθc.symm (targetChart b (cover.chart n) hψc)
                    (targetChart_places b (cover.chart n) hψc))
                  (cast_lifted_rep hθc.symm (targetChart b (cover.chart n) hψc)
                    (targetChart_rep b (cover.chart n) hψc))
                  (cast_lifted_splitting hθc.symm (targetChart b (cover.chart n) hψc)
                    (targetChart_splitting b (cover.chart n) hψc)) C x,
                arrow_gamma_chart_cast hGt C, arrow_root_chart_cast hGt C]
          have hTG : T Garrow x hxG =
              (T eθ.arrow x hθ).trans (T eψ.arrow (eθ.arrow.psi x) hψ) := by
            rw [hTC, hTcomp, hTψ']
          let G : ActualBranch a (cover.chart n) :=
            { component_eq := hGc
              arrow := hGt ▸ C
              source_shrinking := by
                intro y hy
                rw [Gdom] at hy
                exact eθ.source_shrinking hy.1
              target_shrinking := by
                intro y hy
                rw [Gdom] at hy
                rw [Gpsi, Function.comp_apply]
                exact eψ.target_shrinking hy.2
              target_larger := by
                intro y hy
                rw [Gdom] at hy
                rw [Gpsi, Function.comp_apply]
                exact eψ.target_larger hy.2 }
          have key := hCI a n (some G) (some eφ) x hxG hφ
          dsimp only [inverseTransport, Branch.transport, Branch.psi, Branch.domain] at key
          rw [show Garrow.psi x = eψ.arrow.psi (eθ.arrow.psi x) from congrFun Gpsi x,
            hTG] at key
          have hkey := congrArg (T eθ.arrow x hθ) key
          rw [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
            LinearIsometryEquiv.apply_symm_apply] at hkey
          exact hkey

  ·
    intro n y hy
    rw [KPContCotangentActualGroupoidIdentities.identity_psi, T_identity]
    rfl
  ·
    intro n y hy
    rw [mem_Fixed_iff]
    intro γ hγ
    have h := hf n γ y hy
    rw [show (isotropyArrow (cover.chart n) γ).psi y = y from hγ] at h
    exact h.symm
  ·
    intro n y hy hzero
    have hmem : f n y ∈ Fixed (cover.chart n) y (omega_subset_larger (cover.chart n) hy) := by
      rw [mem_Fixed_iff]
      intro γ hγ
      have h := hf n γ y hy
      rw [show (isotropyArrow (cover.chart n) γ).psi y = y from hγ] at h
      exact h.symm
    rw [hzero] at hmem
    simpa using hmem

end DedekindZetaZeroFree

end
