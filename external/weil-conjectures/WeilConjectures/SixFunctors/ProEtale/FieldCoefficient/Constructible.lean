/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Module

/-!
# Lisse and constructible `Λ`-adic sheaves on the pro-étale site

This is the counterpart, for a coefficient field `Λ` with an ultrametric norm (the case of
interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Constructible`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

Let `X` be a scheme. Following Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8) and
the blueprint (`definition-constructible-sheaves`), a
sheaf `F` of `Λ`-modules on the small pro-étale site of `X` is

- *lisse* (`AlgebraicGeometry.ProEtale.IsFieldLisseSheaf`) if it is pro-étale locally a finite
  direct sum of copies of the constant sheaf `Λ`
  (`AlgebraicGeometry.ProEtale.fieldConstantSheaf`), that is, locally free of finite rank over
  `Λ_X`;
- *constructible* (`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf`) if, locally on `X`,
  `X` is the disjoint union of finitely many locally closed subschemes on each of which `F` is
  lisse (`AlgebraicGeometry.ProEtale.IsFieldStratifiedLisseSheaf`).

A lisse sheaf on a connected `X` is the same as a continuous finite-dimensional representation
of `π₁(X)` with coefficients in `Λ`: the trivialising pro-étale cover may be taken to be a
pro-finite étale Galois cover, whose group acts continuously on the fibre `Λⁿ`. For `Λ = E`
these are the lisse `E`-sheaves of the blueprint.

The strata are only required to be locally closed: on the noetherian schemes of the blueprint
every locally closed subset is constructible, and with this convention pullback along an
arbitrary morphism preserves constructibility. The stratification is only required locally on
`X`, so that constructibility is a local property; on the quasi-compact schemes of the blueprint
this is the same as a global finite stratification.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsFieldLisseSheaf` and
  `AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf`.
- `AlgebraicGeometry.ProEtale.fieldConstructibleSheaf`: constructibility as an object property.
- `AlgebraicGeometry.ProEtale.IsIrreducibleFieldLocalSystem`: irreducible lisse sheaves.

## Main results

- `AlgebraicGeometry.ProEtale.isFieldLisseSheaf_fieldConstantSheaf`: `Λ_X` is lisse.
- `AlgebraicGeometry.ProEtale.IsFieldLisseSheaf.upperStar`,
  `AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.upperStar`: pullback preserves lisse and
  constructible sheaves. Both rest on `g^* Λ ≅ Λ`
  (`AlgebraicGeometry.ProEtale.upperStarFieldConstantSheafIso`).
- `AlgebraicGeometry.ProEtale.IsFieldLisseSheaf.biprod`,
  `AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.biprod`: binary direct sums of lisse,
  resp. constructible, sheaves are lisse, resp. constructible.
- The constructible sheaves contain `0` and are closed under isomorphisms and finite products.
  On a locally Noetherian scheme they are also closed under kernels and cokernels
  (`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Abelian`), and they are closed under
  extensions (`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Extension`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ] {X : Scheme.{u}}

/-- A sheaf of `Λ`-modules on the small pro-étale site of `X` is *lisse* if it is pro-étale
locally isomorphic to a finite direct sum of copies of the constant sheaf `Λ`: there
is a pro-étale covering family of `X` over each member `f : V ⟶ X` of which `f^* F ≅ Λ_Vⁿ`. -/
def IsFieldLisseSheaf (F : FieldSheaf Λ X) : Prop :=
  ∃ R ∈ Scheme.proetalePrecoverage X, ∀ ⦃V : Scheme.{u}⦄ (f : V ⟶ X), R f →
    ∃ n : ℕ, Nonempty ((f)^*ᶠ[Λ].obj F ≅
      ⨁ fun _ : Fin n ↦ FieldSheaf.unit Λ V)

/-- Being lisse is invariant under isomorphism. -/
lemma IsFieldLisseSheaf.of_iso {F G : FieldSheaf Λ X}
    (e : F ≅ G) (hF : IsFieldLisseSheaf F) : IsFieldLisseSheaf G := by
  obtain ⟨R, hR, h⟩ := hF
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, ⟨e'⟩⟩ := h f hf
  exact ⟨n, ⟨((f)^*ᶠ[Λ].mapIso e).symm ≪≫ e'⟩⟩

/-- The constant sheaf is lisse, trivialised by the identity cover. -/
lemma isFieldLisseSheaf_fieldConstantSheaf (X : Scheme.{u}) :
    IsFieldLisseSheaf (FieldSheaf.unit Λ X) := by
  refine ⟨.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, fun V f hf ↦ ?_⟩
  obtain ⟨⟩ := hf
  exact ⟨1, ⟨(fieldUpperStarId Λ X).app _ ≪≫ (biproduct.isoProduct
    (fun _ : Fin 1 ↦ FieldSheaf.unit Λ X) ≪≫ productUniqueIso _).symm⟩⟩

/-- The zero sheaf is lisse: it is the empty direct sum of copies of `Λ`. -/
lemma IsFieldLisseSheaf.of_isZero {F : FieldSheaf Λ X}
    (hF : IsZero F) : IsFieldLisseSheaf F := by
  refine ⟨.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, fun V f hf ↦ ?_⟩
  obtain ⟨⟩ := hf
  refine ⟨0, ⟨IsZero.iso ?_ ?_⟩⟩
  · exact Functor.map_isZero _ hF
  · exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
      fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩

/-- A sheaf of `Λ`-modules on the small pro-étale site of `X` is *stratified lisse* if `X` is
the disjoint union of finitely many locally closed constructible subschemes `Z_k`, given by
immersions `i_k : Z_k ⟶ X` whose images are constructible subsets partitioning `X`, such that
each restriction `i_k^* F` is lisse (`definition-constructible-sheaves`). -/
def IsFieldStratifiedLisseSheaf (F : FieldSheaf Λ X) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (Z : ι → Scheme.{u}) (i : (k : ι) → Z k ⟶ X),
    (∀ k, IsImmersion (i k)) ∧ (∀ k, Topology.IsConstructible (Set.range (i k).base)) ∧
      (∀ x : X, ∃! k, x ∈ Set.range (i k).base) ∧
      ∀ k, IsFieldLisseSheaf ((i k)^*ᶠ[Λ].obj F)

/-- Being stratified lisse is invariant under isomorphism. -/
lemma IsFieldStratifiedLisseSheaf.of_iso
    {F G : FieldSheaf Λ X} (e : F ≅ G)
    (hF : IsFieldStratifiedLisseSheaf F) : IsFieldStratifiedLisseSheaf G := by
  obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hF
  exact ⟨ι, hι, Z, i, hi, hc, hcover, fun k ↦ (h k).of_iso ((_)^*ᶠ[Λ].mapIso e)⟩

/-- A lisse sheaf is stratified lisse, with the trivial stratification. -/
lemma IsFieldLisseSheaf.isFieldStratifiedLisseSheaf
    {F : FieldSheaf Λ X} (hF : IsFieldLisseSheaf F) :
    IsFieldStratifiedLisseSheaf F :=
  ⟨Unit, inferInstance, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ inferInstance,
    fun _ ↦ by simp, fun x ↦ ⟨(), ⟨x, rfl⟩, fun _ _ ↦ rfl⟩,
    fun _ ↦ hF.of_iso ((fieldUpperStarId Λ X).app F).symm⟩

/-- A sheaf of `Λ`-modules on the small pro-étale site of `X` is *constructible* if it is
stratified lisse locally on `X`: every point of `X` has an open neighbourhood `W`, given by an
open immersion `j : W ⟶ X`, such that `X ∩ W` is the disjoint union of finitely many locally
closed subschemes on each of which `j^* F` is lisse. On a quasi-compact `X` this is the same as
being stratified lisse. -/
def IsFieldConstructibleSheaf (F : FieldSheaf Λ X) :
    Prop :=
  ∀ x : X, ∃ (W : Scheme.{u}) (j : W ⟶ X), IsOpenImmersion j ∧ x ∈ Set.range j.base ∧
    IsFieldStratifiedLisseSheaf ((j)^*ᶠ[Λ].obj F)

/-- Being constructible is invariant under isomorphism. -/
lemma IsFieldConstructibleSheaf.of_iso
    {F G : FieldSheaf Λ X} (e : F ≅ G)
    (hF : IsFieldConstructibleSheaf F) : IsFieldConstructibleSheaf G := by
  intro x
  obtain ⟨W, j, hj, hx, h⟩ := hF x
  exact ⟨W, j, hj, hx, h.of_iso ((_)^*ᶠ[Λ].mapIso e)⟩

/-- A stratified lisse sheaf is constructible. -/
lemma IsFieldStratifiedLisseSheaf.isFieldConstructibleSheaf
    {F : FieldSheaf Λ X}
    (hF : IsFieldStratifiedLisseSheaf F) : IsFieldConstructibleSheaf F := by
  intro x
  exact ⟨X, 𝟙 X, inferInstance, ⟨x, rfl⟩, hF.of_iso ((fieldUpperStarId Λ X).app F).symm⟩

/-- A lisse sheaf is constructible. -/
lemma IsFieldLisseSheaf.isFieldConstructibleSheaf
    {F : FieldSheaf Λ X} (hF : IsFieldLisseSheaf F) :
    IsFieldConstructibleSheaf F :=
  hF.isFieldStratifiedLisseSheaf.isFieldConstructibleSheaf

/-- The constant sheaf is constructible. -/
lemma isFieldConstructibleSheaf_fieldConstantSheaf (X : Scheme.{u}) :
    IsFieldConstructibleSheaf (FieldSheaf.unit Λ X) :=
  (isFieldLisseSheaf_fieldConstantSheaf X).isFieldConstructibleSheaf

/-- Pulling back a trivialisation: if `g^* Λ_V ≅ Λ_W` and `F ≅ Λ_Vⁿ`, then
`g^* F ≅ Λ_Wⁿ`. -/
lemma nonempty_fieldUpperStar_iso_biproduct {V W : Scheme.{u}} (g : W ⟶ V)
    (hg : Nonempty ((g)^*ᶠ[Λ].obj (FieldSheaf.unit Λ V) ≅
      FieldSheaf.unit Λ W))
    {F : FieldSheaf Λ V} {n : ℕ}
    (e : F ≅ ⨁ fun _ : Fin n ↦ FieldSheaf.unit Λ V) :
    Nonempty ((g)^*ᶠ[Λ].obj F ≅ ⨁ fun _ : Fin n ↦ FieldSheaf.unit Λ W) :=
  ⟨(g)^*ᶠ[Λ].mapIso e ≪≫ (g)^*ᶠ[Λ].mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ hg.some⟩

/-- The pullback of a lisse sheaf is lisse: the pullback of a trivialising cover is a
trivialising cover, and the pullback of the constant sheaf is the constant
sheaf (`AlgebraicGeometry.ProEtale.upperStarFieldConstantSheafIso`). -/
theorem IsFieldLisseSheaf.upperStar {Y : Scheme.{u}} (f : Y ⟶ X)
    {F : FieldSheaf Λ X} (hF : IsFieldLisseSheaf F) :
    IsFieldLisseSheaf ((f)^*ᶠ[Λ].obj F) := by
  obtain ⟨R, hR, h⟩ := hF
  refine ⟨R.pullbackArrows f, Precoverage.pullbackArrows_mem f hR, ?_⟩
  rintro _ _ ⟨V, g, hg⟩
  obtain ⟨n, ⟨e⟩⟩ := h g hg
  obtain ⟨e'⟩ := nonempty_fieldUpperStar_iso_biproduct (pullback.fst g f)
    ⟨fieldUpperStarUnitIso Λ _⟩ e
  exact ⟨n, ⟨(fieldUpperStarCompIso Λ pullback.condition.symm).app F ≪≫ e'⟩⟩

/-- The pullback of a stratified lisse sheaf is stratified lisse: the base changes of the
strata are strata, and the restrictions to them are pullbacks of lisse sheaves. -/
theorem IsFieldStratifiedLisseSheaf.upperStar {Y : Scheme.{u}} (f : Y ⟶ X)
    {F : FieldSheaf Λ X}
    (hF : IsFieldStratifiedLisseSheaf F) :
    IsFieldStratifiedLisseSheaf ((f)^*ᶠ[Λ].obj F) := by
  obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hF
  refine ⟨ι, hι, fun k ↦ pullback (i k) f, fun k ↦ pullback.snd (i k) f, fun k ↦ inferInstance,
    fun k ↦ ?_, fun y ↦ ?_, fun k ↦ ((h k).upperStar (pullback.fst (i k) f)).of_iso
      ((fieldUpperStarCompIso Λ pullback.condition).app F)⟩
  · rw [Scheme.Pullback.range_snd]
    exact f.isConstructible_preimage (hc k)
  obtain ⟨k, ⟨z, hz⟩, hk⟩ := hcover (f y)
  obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback z y hz
  refine ⟨k, ⟨t, ht⟩, fun k' ⟨t', ht'⟩ ↦ hk k' ⟨pullback.fst (i k') f t', ?_⟩⟩
  rw [← ht', ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

/-- The pullback of a constructible sheaf is constructible: the preimages of the open
neighbourhoods and of the strata are open neighbourhoods and strata, given by the base changes
of the immersions, and the restrictions to them are pullbacks of lisse sheaves. -/
theorem IsFieldConstructibleSheaf.upperStar {Y : Scheme.{u}} (f : Y ⟶ X)
    {F : FieldSheaf Λ X}
    (hF : IsFieldConstructibleSheaf F) :
    IsFieldConstructibleSheaf ((f)^*ᶠ[Λ].obj F) := by
  intro y
  obtain ⟨W, j, hj, ⟨w, hw⟩, h⟩ := hF (f y)
  obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback w y hw
  exact ⟨pullback j f, pullback.snd j f, inferInstance, ⟨t, ht⟩,
    (h.upperStar (pullback.fst j f)).of_iso ((fieldUpperStarCompIso Λ pullback.condition).app F)⟩

/-- A finite direct sum of lisse sheaves is lisse: refine the two trivialising covers. -/
theorem IsFieldLisseSheaf.biprod
    {F G : FieldSheaf Λ X} (hF : IsFieldLisseSheaf F)
    (hG : IsFieldLisseSheaf G) : IsFieldLisseSheaf (F ⊞ G) := by
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨R', hR', hR'G⟩ := hG
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨ι', V', f', rfl⟩ := R'.exists_eq_ofArrows
  refine ⟨_, Precoverage.comp_mem_coverings f hR (fun i j ↦ pullback.fst (f i) (f' j))
    (fun i ↦ Precoverage.mem_coverings_of_isPullback f' hR' (f i) _ _
      fun j ↦ IsPullback.of_hasPullback (f i) (f' j)), ?_⟩
  rintro _ _ ⟨⟨i, j⟩⟩
  have := Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  have := Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR' (.mk j)
  obtain ⟨n, ⟨e⟩⟩ := hRF (f i) (.mk i)
  obtain ⟨m, ⟨e'⟩⟩ := hR'G (f' j) (.mk j)
  obtain ⟨e₁⟩ := nonempty_fieldUpperStar_iso_biproduct (pullback.fst (f i) (f' j))
    ⟨fieldUpperStarUnitIso Λ _⟩ e
  obtain ⟨e₂⟩ := nonempty_fieldUpperStar_iso_biproduct (pullback.snd (f i) (f' j))
    ⟨fieldUpperStarUnitIso Λ _⟩ e'
  refine ⟨n + m, ⟨(_)^*ᶠ[Λ].mapBiprod F G ≪≫ biprod.mapIso
    ((fieldUpperStarComp Λ _ _).app F ≪≫ e₁)
    ((fieldUpperStarCongr Λ pullback.condition).app G ≪≫ (fieldUpperStarComp Λ _ _).app G ≪≫ e₂) ≪≫
    biprodBiproductSumIso (fun _ ↦ FieldSheaf.unit Λ _) ≪≫
      biproduct.whiskerEquiv finSumFinEquiv (g := fun _ ↦ FieldSheaf.unit Λ _)
        (fun _ ↦ Iso.refl _)⟩⟩

/-- A binary direct sum of stratified lisse sheaves is stratified lisse: on the common
refinement of the two stratifications both summands are lisse. -/
theorem IsFieldStratifiedLisseSheaf.biprod
    {F G : FieldSheaf Λ X}
    (hF : IsFieldStratifiedLisseSheaf F) (hG : IsFieldStratifiedLisseSheaf G) :
    IsFieldStratifiedLisseSheaf (F ⊞ G) := by
  obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hF
  obtain ⟨ι', hι', Z', i', hi', hc', hcover', h'⟩ := hG
  refine ⟨ι × ι', inferInstance, fun k ↦ pullback (i k.1) (i' k.2),
    fun k ↦ pullback.fst (i k.1) (i' k.2) ≫ i k.1, fun k ↦ inferInstance, fun k ↦ ?_,
    fun x ↦ ?_, fun k ↦ ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst,
      Set.image_preimage_eq_inter_range]
    exact (hc' k.2).inter (hc k.1)
  · obtain ⟨k, ⟨z, hz⟩, hk⟩ := hcover x
    obtain ⟨k', ⟨z', hz'⟩, hk'⟩ := hcover' x
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback z z' (hz.trans hz'.symm)
    refine ⟨(k, k'), ⟨t, by rw [Scheme.Hom.comp_apply, ht, hz]⟩, fun m ⟨t', ht'⟩ ↦ ?_⟩
    refine Prod.ext (hk m.1 ⟨_, ht'⟩) (hk' m.2 ⟨pullback.snd (i m.1) (i' m.2) t', ?_⟩)
    rw [← ht', ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  · exact (((h k.1).upperStar _).biprod (((h' k.2).upperStar
      (pullback.snd (i k.1) (i' k.2))).of_iso
        ((fieldUpperStarCompIso Λ pullback.condition.symm).app G))).of_iso
      ((fieldUpperStarComp Λ (pullback.fst (i k.1) (i' k.2)) (i k.1)).app (F ⊞ G) ≪≫
        (pullback.fst (i k.1) (i' k.2))^*ᶠ[Λ].mapIso ((i k.1)^*ᶠ[Λ].mapBiprod F G) ≪≫
        (pullback.fst (i k.1) (i' k.2))^*ᶠ[Λ].mapBiprod _ _).symm

/-- A binary direct sum of constructible sheaves is constructible: on the intersection of the
two open neighbourhoods both summands are stratified lisse. -/
theorem IsFieldConstructibleSheaf.biprod
    {F G : FieldSheaf Λ X}
    (hF : IsFieldConstructibleSheaf F) (hG : IsFieldConstructibleSheaf G) :
    IsFieldConstructibleSheaf (F ⊞ G) := by
  intro x
  obtain ⟨W, j, hj, ⟨w, hw⟩, h⟩ := hF x
  obtain ⟨W', j', hj', ⟨w', hw'⟩, h'⟩ := hG x
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback w w' (hw.trans hw'.symm)
  refine ⟨pullback j j', pullback.fst j j' ≫ j, inferInstance,
    ⟨t, by rw [Scheme.Hom.comp_apply, ht, hw]⟩, ?_⟩
  exact ((h.upperStar _).biprod ((h'.upperStar (pullback.snd j j')).of_iso
      ((fieldUpperStarCompIso Λ pullback.condition.symm).app G))).of_iso
    ((fieldUpperStarComp Λ (pullback.fst j j') j).app (F ⊞ G) ≪≫
      (pullback.fst j j')^*ᶠ[Λ].mapIso ((j)^*ᶠ[Λ].mapBiprod F G) ≪≫
      (pullback.fst j j')^*ᶠ[Λ].mapBiprod _ _).symm

/-- A sheaf of `Λ`-modules on the small pro-étale site of `X` is an *irreducible `Λ`-adic local
system* if it is lisse and nonzero, and every lisse subsheaf of it is zero or all of it. For
`X` connected this says that the corresponding continuous representation of `π₁(X)` is
irreducible. -/
def IsIrreducibleFieldLocalSystem
    (F : FieldSheaf Λ X) : Prop :=
  IsFieldLisseSheaf F ∧ ¬ IsZero F ∧
    ∀ (G : FieldSheaf Λ X) (i : G ⟶ F), Mono i →
      IsFieldLisseSheaf G → IsZero G ∨ IsIso i

variable (Λ X) in
/-- Constructibility of `Λ`-adic pro-étale sheaves, as an object property. -/
def fieldConstructibleSheaf :
    ObjectProperty (FieldSheaf Λ X) :=
  fun F ↦ IsFieldConstructibleSheaf F

lemma fieldConstructibleSheaf_iff (F : FieldSheaf Λ X) :
    fieldConstructibleSheaf Λ X F ↔ IsFieldConstructibleSheaf F :=
  Iff.rfl

instance : (fieldConstructibleSheaf Λ X).IsClosedUnderIsomorphisms where
  of_iso e hF := IsFieldConstructibleSheaf.of_iso e hF

instance : (fieldConstructibleSheaf Λ X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (IsFieldLisseSheaf.of_isZero (isZero_zero _)).isFieldConstructibleSheaf⟩

/-- **Finite products of constructible sheaves are constructible**: the empty product is `0`,
and a binary product is a binary direct sum
(`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.biprod`). -/
instance : (fieldConstructibleSheaf Λ X).IsClosedUnderFiniteProducts := by
  have : (fieldConstructibleSheaf Λ X).IsClosedUnderBinaryProducts := by
    refine ⟨fun Y ⟨p⟩ ↦ ?_⟩
    exact ((p.prop_diag_obj ⟨.left⟩).biprod (p.prop_diag_obj ⟨.right⟩)).of_iso
      (biprod.isoProd _ _ ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair _)).symm ≪≫
        (p.isLimit.conePointUniqueUpToIso (limit.isLimit _)).symm)
  exact .mk'

end AlgebraicGeometry.ProEtale
