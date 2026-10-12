module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.OpenCellKernelAndActions
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TestFunctionCoinvariantsAndIntegration
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.InductionReciprocity

@[expose] public section

noncomputable section

set_option maxHeartbeats 4000000

namespace DedekindZetaZeroFree.KPJacquetTwistedCell

open scoped NumberField NNReal Classical
open NumberField IsDedekindDomain MeasureTheory
open KPLocalSmoothRepresentation KPJacquetClosedCellBump

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
  (τ : Representation ℂ (Torus F ζ hζ w) E)

abbrev coefficientRepresentation :=
  inflatedRepresentation F ζ hζ w
    (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w) τ

def rootToBorel : Multiplicative (KPRankOneInduction.LocalField F w) →*
    Borel F ζ hζ w where
  toFun := rootInBorel F ζ hζ w
  map_one' := by apply Subtype.ext; exact map_one (upperRoot F ζ hζ w)
  map_mul' := by intro x y; apply Subtype.ext; exact map_mul (upperRoot F ζ hζ w) x y

abbrev ClosedCoinvariants
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ) :=
  RootCoinvariants
    (inducingRepresentation F ζ hζ w (coefficientRepresentation F ζ hζ w τ))
    (rootToBorel F ζ hζ w) ψ

abbrev InducedCoinvariants
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ) :=
  TwistedCoinvariants F ζ hζ w
    (V := PrincipalSeries F ζ hζ w m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w) τ)
    (inducedRepresentation F ζ hζ w m hm
      (coefficientRepresentation F ζ hζ w τ)) ψ

theorem closed_root_trivial
    (y : Multiplicative (KPRankOneInduction.LocalField F w)) (e : E) :
    inducingRepresentation F ζ hζ w (coefficientRepresentation F ζ hζ w τ)
      (rootToBorel F ζ hζ w y) e = e := by
  letI : TopologicalSpace (FiniteCover F ζ hζ w) := ⊥
  letI : DiscreteTopology (FiniteCover F ζ hζ w) := ⟨rfl⟩
  have hn : projection F ζ hζ w (upperRoot F ζ hζ w y) =
      KPRankOneInduction.upperRootElement F w (Multiplicative.toAdd y) := rfl
  have hd := KPRankOneInduction.deltaB_upperRoot F w (projection F ζ hζ w)
    (Multiplicative.toAdd y) (rootToBorel F ζ hζ w y) hn
  change (((dB F ζ hζ w (rootToBorel F ζ hζ w y) : ℝ≥0) : ℝ) : ℂ) •
    τ (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
      (rootToBorel F ζ hζ w y)) e = e
  rw [show KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
    (rootToBorel F ζ hζ w y) = 1 from
    KPLocalInductionJacquetReciprocity.borelRetraction_upperRoot F ζ hζ w y]
  unfold KPLocalSmoothRepresentation.dB KPRankOneInduction.dB
  rw [KPRankOneInduction.halfModulus_eq, hd]
  simp

theorem closed_relations_eq_top
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ)
    (hψne : ψ ≠ 1) :
    rootRelationSpan
      (inducingRepresentation F ζ hζ w (coefficientRepresentation F ζ hζ w τ))
      (rootToBorel F ζ hζ w) ψ = ⊤ := by
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    apply hψne
    apply MonoidHom.ext
    intro y
    exact not_exists_not.mp h y
  have hc : (1 - (ψ y : ℂ)) ≠ 0 := by
    intro h
    apply hy
    apply Units.ext
    simpa using (sub_eq_zero.mp h).symm
  apply top_unique
  intro e _
  have hmem :
      inducingRepresentation F ζ hζ w (coefficientRepresentation F ζ hζ w τ)
        (rootToBorel F ζ hζ w y) ((1 - (ψ y : ℂ))⁻¹ • e) -
      (ψ y : ℂ) • ((1 - (ψ y : ℂ))⁻¹ • e) ∈
      rootRelationSpan (inducingRepresentation F ζ hζ w
        (coefficientRepresentation F ζ hζ w τ)) (rootToBorel F ζ hζ w) ψ :=
    Submodule.subset_span (Set.mem_range_self (y, (1 - (ψ y : ℂ))⁻¹ • e))
  change _ ∈ rootRelationSpan _ _ ψ at hmem
  rw [closed_root_trivial] at hmem
  have he : ((1 - (ψ y : ℂ))⁻¹ • e) -
      (ψ y : ℂ) • ((1 - (ψ y : ℂ))⁻¹ • e) = e := by
    calc
      _ = (1 - (ψ y : ℂ)) • ((1 - (ψ y : ℂ))⁻¹ • e) := by
        rw [sub_smul, one_smul]
      _ = e := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [he] at hmem
  exact hmem

theorem closed_coinvariants_subsingleton
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ)
    (hψne : ψ ≠ 1) :
    Subsingleton (ClosedCoinvariants F ζ hζ w τ ψ) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  rw [rootTwistedRepresentation_ker]
  exact closed_relations_eq_top F ζ hζ w τ ψ hψne

local instance : ValuativeRel (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F w
local instance : IsNonarchimedeanLocalField (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F w

variable [hE : FiniteDimensional ℂ E]
  (hτ : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τ)

include hτ hE

include hm in

theorem coefficient_smooth :
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation (coefficientRepresentation F ζ hζ w τ) := by
  exact inflatedRepresentation_smooth F ζ hζ w m hm
    (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w) τ hm
    (KPLocalInductionJacquetReciprocity.borelRetraction_continuous F ζ hζ w m hm) hτ

omit hE in
include hm in
 theorem coefficient_smooth_without_dimension :
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation (coefficientRepresentation F ζ hζ w τ) := by
  exact inflatedRepresentation_smooth F ζ hζ w m hm
    (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w) τ hm
    (KPLocalInductionJacquetReciprocity.borelRetraction_continuous F ζ hζ w m hm) hτ

omit hE in
private theorem coefficient_root_one
    (y : Multiplicative (KPRankOneInduction.LocalField F w)) :
    coefficientRepresentation F ζ hζ w τ (rootInBorel F ζ hζ w y) = 1 := by
  change τ (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
    (rootInBorel F ζ hζ w y)) = 1
  rw [show KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
    (rootInBorel F ζ hζ w y) = 1 from
    KPLocalInductionJacquetReciprocity.borelRetraction_upperRoot F ζ hζ w y]
  exact map_one τ

private theorem open_root_translation
    (y : Multiplicative (KPRankOneInduction.LocalField F w))
    (φ : KPJacquetOpenCell.TestFunctions F w (E := E)) :
    KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm
      (coefficientRepresentation F ζ hζ w τ)
      (coefficient_smooth_without_dimension F ζ hζ w m hm τ hτ) (rootToBorel F ζ hζ w y) φ =
    KPJacquetOpenTestFunction.translationRepresentation y φ := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  exact KPJacquetOpenCell.upperRoot_action F ζ hζ w m hm
    (coefficientRepresentation F ζ hζ w τ)
    (coefficient_smooth_without_dimension F ζ hζ w m hm τ hτ)
    (coefficient_root_one F ζ hζ w m τ hτ) (Multiplicative.toAdd y) x φ

omit hE in
private theorem omega_shift (b : Borel F ζ hζ w)
    (x y : KPRankOneInduction.LocalField F w) :
    (KPJacquetBruhatCharts.omegaMap F ζ hζ w (b, x)).val *
      upperRoot F ζ hζ w (Multiplicative.ofAdd y) =
    (KPJacquetBruhatCharts.omegaMap F ζ hζ w (b, x + y)).val := by
  change (b.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
    upperRoot F ζ hζ w (Multiplicative.ofAdd x)) * _ = _
  rw [mul_assoc, ← map_mul, ← ofAdd_add]
  rfl

omit hE in
include hm in
private theorem extension_on (b : Borel F ζ hζ w)
    (x : KPRankOneInduction.LocalField F w)
    (φ : KPJacquetOpenCell.TestFunctions F w (E := E)) :
    KPJacquetOpenCell.extensionFunction F ζ hζ w
      (coefficientRepresentation F ζ hζ w τ) φ
      (KPJacquetBruhatCharts.omegaMap F ζ hζ w (b, x)).val =
    inducingRepresentation F ζ hζ w (coefficientRepresentation F ζ hζ w τ) b
      (KPJacquetStepFunction.value φ x) := by
  letI := finiteCoverTopology F ζ hζ w m
  have h := (KPJacquetBruhatCharts.omegaHomeomorph F ζ hζ w m hm).left_inv (b, x)
  unfold KPJacquetOpenCell.extensionFunction
  rw [dif_pos (KPJacquetBruhatCharts.omegaMap F ζ hζ w (b, x)).property]
  change inducingRepresentation F ζ hζ w _
    (KPJacquetBruhatCharts.omegaInverse F ζ hζ w
      (KPJacquetBruhatCharts.omegaMap F ζ hζ w (b, x))).1
    (KPJacquetStepFunction.value φ
      (KPJacquetBruhatCharts.omegaInverse F ζ hζ w
        (KPJacquetBruhatCharts.omegaMap F ζ hζ w (b, x))).2) = _
  change KPJacquetBruhatCharts.omegaInverse F ζ hζ w
    (KPJacquetBruhatCharts.omegaMap F ζ hζ w (b, x)) = (b, x) at h
  rw [h]

omit hE in
include hm in
 theorem extension_translation
    (y : KPRankOneInduction.LocalField F w)
    (φ : KPJacquetOpenCell.TestFunctions F w (E := E))
    (g : FiniteCover F ζ hζ w) :
    KPJacquetOpenCell.extensionFunction F ζ hζ w
      (coefficientRepresentation F ζ hζ w τ)
      (KPJacquetOpenTestFunction.translation y φ) g =
    KPJacquetOpenCell.extensionFunction F ζ hζ w
      (coefficientRepresentation F ζ hζ w τ) φ
      (g * upperRoot F ζ hζ w (Multiplicative.ofAdd y)) := by
  letI := finiteCoverTopology F ζ hζ w m
  let H := KPJacquetBruhatCharts.omegaHomeomorph F ζ hζ w m hm
  by_cases hg : g ∈ KPJacquetBruhatCharts.omega F ζ hζ w
  · let p := H.symm ⟨g, hg⟩
    have he : (KPJacquetBruhatCharts.omegaMap F ζ hζ w p).val = g :=
      congrArg Subtype.val (H.apply_symm_apply ⟨g, hg⟩)
    rw [← he, omega_shift F ζ hζ w m τ hτ p.1 p.2 y]
    rw [extension_on F ζ hζ w m hm τ hτ, extension_on F ζ hζ w m hm τ hτ]
    rfl
  · have hgn : g * upperRoot F ζ hζ w (Multiplicative.ofAdd y) ∉
        KPJacquetBruhatCharts.omega F ζ hζ w := by
      intro hn
      let p := H.symm ⟨_, hn⟩
      have he : (KPJacquetBruhatCharts.omegaMap F ζ hζ w p).val =
          g * upperRoot F ζ hζ w (Multiplicative.ofAdd y) :=
        congrArg Subtype.val (H.apply_symm_apply ⟨_, hn⟩)
      have hh := omega_shift F ζ hζ w m τ hτ p.1 p.2 (-y)
      rw [he, mul_assoc, ← map_mul, ← ofAdd_add] at hh
      simp only [add_neg_cancel, ofAdd_zero, map_one, mul_one] at hh
      exact hg (hh ▸ (KPJacquetBruhatCharts.omegaMap F ζ hζ w (p.1, p.2 + -y)).property)
    simp [KPJacquetOpenCell.extensionFunction, hg, hgn]

omit hE in
 def openIntertwiner :
    Representation.IntertwiningMap
      (KPJacquetOpenTestFunction.translationRepresentation
        (K := KPRankOneInduction.LocalField F w) (E := E))
      ((inducedRepresentation F ζ hζ w m hm
        (coefficientRepresentation F ζ hζ w τ)).comp (upperRoot F ζ hζ w)) where
  toLinearMap := KPJacquetOpenCell.ext_w F ζ hζ w m hm
    (coefficientRepresentation F ζ hζ w τ)
    (coefficient_smooth_without_dimension F ζ hζ w m hm τ hτ)
  isIntertwining' y := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact extension_translation F ζ hζ w m hm τ hτ
      (Multiplicative.toAdd y) φ g

omit hE in

def openCellMap
    (hτ : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τ)
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ) :
    KPJacquetOpenTestFunction.TranslationCoinvariants (E := E) ψ →ₗ[ℂ]
      InducedCoinvariants F ζ hζ w m hm τ ψ := by
  exact Representation.Coinvariants.map _ _ {
    toLinearMap := (openIntertwiner F ζ hζ w m hm τ hτ).toLinearMap
    isIntertwining' y := by
      apply LinearMap.ext
      intro φ
      simp only [LinearMap.comp_apply, rootTwistedRepresentation_apply,
        MonoidHom.id_apply, map_smul]
      congr 1
      exact LinearMap.congr_fun
        ((openIntertwiner F ζ hζ w m hm τ hτ).isIntertwining' y) φ }

theorem openCellMap_mk
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ)
    (φ : KPJacquetOpenCell.TestFunctions F w (E := E)) :
    openCellMap F ζ hζ w m hm τ hτ ψ
      (KPJacquetOpenTestFunction.coinvariantsMk ψ φ) =
    rootCoinvariantsMk
      (inducedRepresentation F ζ hζ w m hm
        (coefficientRepresentation F ζ hζ w τ))
      (upperRoot F ζ hζ w) ψ
      (KPJacquetOpenCell.ext_w F ζ hζ w m hm
        (coefficientRepresentation F ζ hζ w τ)
        (coefficient_smooth F ζ hζ w m hm τ hτ) φ) := by
  rfl

omit hτ hE in
private theorem smooth_restrict {G U : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G U) (hs : SmoothRepresentation ρ)
    (n : Multiplicative (KPRankOneInduction.LocalField F w) →* G)
    (hn : Continuous n) : KPCoinvariants.IsSmooth (ρ.comp n) := by
  apply KPCoinvariants.restrict_smooth ρ _ n hn
  intro v
  obtain ⟨J, hJ⟩ := hs v
  exact Subgroup.isOpen_mono (H₂ := ρ.stabilizer v) hJ J.isOpen

 def closedIntertwiner :
    Representation.IntertwiningMap
      ((inducedRepresentation F ζ hζ w m hm
        (coefficientRepresentation F ζ hζ w τ)).comp (upperRoot F ζ hζ w))
      ((inducingRepresentation F ζ hζ w
        (coefficientRepresentation F ζ hζ w τ)).comp (rootToBorel F ζ hζ w)) where
  toLinearMap := ev1 F ζ hζ w m (coefficientRepresentation F ζ hζ w τ)
  isIntertwining' y := by
    apply LinearMap.ext
    intro f
    exact ev1_borel F ζ hζ w m hm (coefficientRepresentation F ζ hζ w τ)
      (rootToBorel F ζ hζ w y) f

omit hτ hE in
 theorem twist_eq {G U : Type*} [Group G] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G U)
    (n : Multiplicative (KPRankOneInduction.LocalField F w) →* G)
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ) :
    rootTwistedRepresentation ρ n ψ = KPCoinvariants.twistedRepresentation (ρ.comp n) ψ := by
  apply MonoidHom.ext
  intro y
  apply LinearMap.ext
  intro u
  simp [rootTwistedRepresentation, KPCoinvariants.twistedRepresentation]

omit hτ hE in
 def twistEquiv {G U : Type*} [Group G] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G U)
    (n : Multiplicative (KPRankOneInduction.LocalField F w) →* G)
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ) :
    RootCoinvariants ρ n ψ ≃ₗ[ℂ] KPCoinvariants.Coinvariants (ρ.comp n) ψ :=
  Submodule.quotEquivOfEq _ _ (congrArg Representation.Coinvariants.ker
    (twist_eq F w ρ n ψ))

theorem openCellMap_bijective
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ)
    (hψ : Continuous ψ) (hψne : ψ ≠ 1) :
    Function.Bijective (openCellMap F ζ hζ w m hm τ hτ ψ) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  let ρB := coefficientRepresentation F ζ hζ w τ
  let hs := coefficient_smooth F ζ hζ w m hm τ hτ
  obtain ⟨hU, hV, hW, hiB, hpB, hi, hex, hp⟩ :=
    KPJacquetOpenCell.smooth_borel_short_exact F ζ hζ w m hm ρB hs
  have hn : Continuous (rootToBorel F ζ hζ w) :=
    ((continuousUpperRoot F ζ hζ w m hm).continuous).subtype_mk _
  have hUs : KPCoinvariants.IsSmooth
      (KPJacquetOpenTestFunction.translationRepresentation
        (K := KPRankOneInduction.LocalField F w) (E := E)) := by
    have h := smooth_restrict F w _ hU (rootToBorel F ζ hζ w) hn
    intro φ
    convert h φ using 1
    ext x
    change (KPJacquetOpenTestFunction.translationRepresentation (Multiplicative.ofAdd x) φ = φ) ↔
      (KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm
        (coefficientRepresentation F ζ hζ w τ)
        (coefficient_smooth_without_dimension F ζ hζ w m hm τ hτ)
        (rootToBorel F ζ hζ w (Multiplicative.ofAdd x)) φ = φ)
    rw [open_root_translation F ζ hζ w m hm τ hτ]
  have hVs : KPCoinvariants.IsSmooth (V := Induced F ζ hζ w m ρB)
      ((inducedRepresentation F ζ hζ w m hm ρB).comp (upperRoot F ζ hζ w)) :=
    smooth_restrict F w _ hV (rootToBorel F ζ hζ w) hn
  have hWs : KPCoinvariants.IsSmooth
      ((inducingRepresentation F ζ hζ w ρB).comp (rootToBorel F ζ hζ w)) :=
    smooth_restrict F w _ hW (rootToBorel F ζ hζ w) hn
  have hψs : IsLocallyConstant ψ := by
    have h := KPJacquetCharacter.character_locallyConstant F w
      (AddChar.toMonoidHomEquiv.symm ψ) (hψ.comp continuous_ofAdd)
    exact h.comp_continuous continuous_toAdd
  obtain ⟨hinj, hrange, hsurj⟩ := KPCoinvariants.exact _ _ _ hUs hVs hWs ψ hψ
    hψs
    (openIntertwiner F ζ hζ w m hm τ hτ)
    (closedIntertwiner F ζ hζ w m hm τ) hi hp hex
  letI : Subsingleton (ClosedCoinvariants F ζ hζ w τ ψ) :=
    closed_coinvariants_subsingleton F ζ hζ w τ ψ hψne
  let eU := twistEquiv F w (U := KPJacquetOpenCell.TestFunctions F w (E := E))
    (KPJacquetOpenTestFunction.translationRepresentation
      (K := KPRankOneInduction.LocalField F w) (E := E))
    (MonoidHom.id _) ψ
  let eV := twistEquiv F w (U := Induced F ζ hζ w m ρB) (inducedRepresentation F ζ hζ w m hm ρB)
    (upperRoot F ζ hζ w) ψ
  let eW := twistEquiv F w (inducingRepresentation F ζ hζ w ρB)
    (rootToBorel F ζ hζ w) ψ
  have hmU : (KPJacquetOpenTestFunction.translationRepresentation
      (K := KPRankOneInduction.LocalField F w) (E := E)).comp (MonoidHom.id _) =
      KPJacquetOpenTestFunction.translationRepresentation := by rfl
  have hmap : ∀ q, eV (openCellMap F ζ hζ w m hm τ hτ ψ q) =
      KPCoinvariants.map
        (V := KPJacquetOpenCell.TestFunctions F w (E := E))
        (W := Induced F ζ hζ w m ρB) _ _ ψ
        (openIntertwiner F ζ hζ w m hm τ hτ) (eU q) := by
    intro q
    obtain ⟨φ, rfl⟩ := rootCoinvariantsMk_surjective
      (KPJacquetOpenTestFunction.translationRepresentation
        (K := KPRankOneInduction.LocalField F w) (E := E)) (MonoidHom.id _) ψ q
    rfl
  have hWzero : Subsingleton (KPCoinvariants.Coinvariants
      ((inducingRepresentation F ζ hζ w ρB).comp (rootToBorel F ζ hζ w)) ψ) :=
    eW.surjective.subsingleton
  letI := hWzero
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply eU.injective
    apply hinj
    rw [← hmap, ← hmap, hab]
  · intro q
    have hq : eV q ∈ LinearMap.ker (KPCoinvariants.map
        (V := Induced F ζ hζ w m ρB) (W := E) _ _ ψ
        (closedIntertwiner F ζ hζ w m hm τ)) := by
      change _ = 0
      exact Subsingleton.elim _ _
    rw [← hrange] at hq
    obtain ⟨a, ha⟩ := hq
    refine ⟨eU.symm a, eV.injective ?_⟩
    rw [hmap, eU.apply_symm_apply]
    exact ha

def openCellEquiv
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ)
    (hψ : Continuous ψ) (hψne : ψ ≠ 1) :
    KPJacquetOpenTestFunction.TranslationCoinvariants (E := E) ψ ≃ₗ[ℂ]
      InducedCoinvariants F ζ hζ w m hm τ ψ :=
  LinearEquiv.ofBijective (openCellMap F ζ hζ w m hm τ hτ ψ)
    (openCellMap_bijective F ζ hζ w m hm τ hτ ψ hψ hψne)

theorem nonempty_coefficient_equiv
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ)
    (hψ : Continuous ψ) (hψne : ψ ≠ 1) :
    Nonempty (InducedCoinvariants F ζ hζ w m hm τ ψ ≃ₗ[ℂ] E) := by
  let e := (Module.finBasis ℂ E).equivFun
  letI : NormedAddCommGroup E := NormedAddCommGroup.induced E _ e e.injective
  letI : NormedSpace ℂ E := NormedSpace.induced ℂ E _ e
  letI : MeasurableSpace (KPRankOneInduction.LocalField F w) := borel _
  letI : BorelSpace (KPRankOneInduction.LocalField F w) := ⟨rfl⟩
  exact ⟨(openCellEquiv F ζ hζ w m hm τ hτ ψ hψ hψne).symm.trans
    (KPJacquetOpenTestFunction.coinvariantsEquiv ψ hψ Measure.addHaar)⟩

section Integral

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]
  (τV : Representation ℂ (Torus F ζ hζ w) V)
  (hτV : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τV)

local instance : MeasurableSpace (KPRankOneInduction.LocalField F w) :=
  borel (KPRankOneInduction.LocalField F w)
local instance : BorelSpace (KPRankOneInduction.LocalField F w) := ⟨rfl⟩

omit hτ hE in

def coefficientEquiv
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ)
    (hψ : Continuous ψ) (hψne : ψ ≠ 1)
    (μ : Measure (KPRankOneInduction.LocalField F w)) [μ.IsAddHaarMeasure] :
    InducedCoinvariants F ζ hζ w m hm τV ψ ≃ₗ[ℂ] V :=
  (openCellEquiv F ζ hζ w m hm τV hτV ψ hψ hψne).symm.trans
    (KPJacquetOpenTestFunction.coinvariantsEquiv ψ hψ μ)

omit hτ hE in

theorem coefficientEquiv_openCell_mk
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ)
    (hψ : Continuous ψ) (hψne : ψ ≠ 1)
    (μ : Measure (KPRankOneInduction.LocalField F w)) [μ.IsAddHaarMeasure]
    (φ : KPJacquetOpenCell.TestFunctions F w (E := V)) :
    coefficientEquiv F ζ hζ w m hm τV hτV ψ hψ hψne μ
      (openCellMap F ζ hζ w m hm τV hτV ψ
        (KPJacquetOpenTestFunction.coinvariantsMk ψ φ)) =
    ∫ x, ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹) •
      KPJacquetStepFunction.value φ x ∂μ := by
  change KPJacquetOpenTestFunction.coinvariantsEquiv ψ hψ μ
    ((openCellEquiv F ζ hζ w m hm τV hτV ψ hψ hψne).symm
      ((openCellEquiv F ζ hζ w m hm τV hτV ψ hψ hψne)
        (KPJacquetOpenTestFunction.coinvariantsMk ψ φ))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact KPJacquetOpenTestFunction.coinvariantsEquiv_mk ψ hψ μ φ

end Integral

end DedekindZetaZeroFree.KPJacquetTwistedCell

end
