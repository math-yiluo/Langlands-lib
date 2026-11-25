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
public import WeilConjectures.SixFunctors.ProEtale.Adic.Module

/-!
# Lisse and constructible `ℓ`-adic sheaves on the pro-étale site

Let `X` be a scheme. Following Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8) and
the blueprint (`definition-constructible-sheaves`), a
sheaf `F` of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is

- *lisse* (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf`) if it is pro-étale locally a finite
  direct sum of copies of the constant `ℓ`-adic sheaf `ℚ̄_ℓ`
  (`AlgebraicGeometry.ProEtale.adicConstantSheaf`), that is, locally free of finite rank over
  `ℚ̄_ℓ,X`;
- *constructible* (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf`) if, locally on `X`,
  `X` is the disjoint union of finitely many locally closed subschemes on each of which `F` is
  lisse (`AlgebraicGeometry.ProEtale.IsAdicStratifiedLisseSheaf`).

A lisse sheaf on a connected `X` is the same as a continuous finite-dimensional representation
of `π₁(X)` with coefficients in a finite extension `E` of `ℚ_ℓ`: the trivialising pro-étale
cover may be taken to be a pro-finite étale Galois cover, whose group acts continuously on the
fibre `E^n`. In particular a lisse sheaf has a finite field of definition, and the category
of constructible `ℚ̄_ℓ`-sheaves is the `2`-colimit over finite `E ⊆ ℚ̄_ℓ` of the categories of
constructible `E`-sheaves.

The strata are only required to be locally closed: on the noetherian schemes of the blueprint
every locally closed subset is constructible, and with this convention pullback along an
arbitrary morphism preserves constructibility. The stratification is only required locally on
`X`, so that constructibility is a local property; on the quasi-compact schemes of the blueprint
this is the same as a global finite stratification.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf` and
  `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf`.
- `AlgebraicGeometry.ProEtale.adicConstructibleSheaf`: constructibility as an object property.
- `AlgebraicGeometry.ProEtale.IsIrreducibleAdicLocalSystem`: irreducible lisse sheaves.

## Main results

- `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_adicConstantSheaf`: `ℚ̄_ℓ,X` is lisse.
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.upperStar`,
  `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.upperStar`: pullback preserves lisse and
  constructible sheaves. Both rest on `g^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
  (`AlgebraicGeometry.ProEtale.upperStarAdicConstantSheafIso`).
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.biprod`,
  `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.biprod`: binary direct sums of lisse,
  resp. constructible, sheaves are lisse, resp. constructible.
- The constructible sheaves contain `0` and are closed under isomorphisms and finite products.
  On a locally Noetherian scheme they are also closed under kernels and cokernels
  (`WeilConjectures.SixFunctors.ProEtale.Adic.Abelian`), and they are closed under extensions
  (`WeilConjectures.SixFunctors.ProEtale.Adic.Extension`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- A sheaf of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is *lisse* if it is pro-étale
locally isomorphic to a finite direct sum of copies of the constant `ℓ`-adic sheaf `ℚ̄_ℓ`: there
is a pro-étale covering family of `X` over each member `f : V ⟶ X` of which `f^* F ≅ ℚ̄_ℓ,Vⁿ`. -/
def IsAdicLisseSheaf (F : AdicSheaf l X) : Prop :=
  ∃ R ∈ Scheme.proetalePrecoverage X, ∀ ⦃V : Scheme.{u}⦄ (f : V ⟶ X), R f →
    ∃ n : ℕ, Nonempty ((f)^*ᵃ[l].obj F ≅
      ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V)

/-- Being lisse is invariant under isomorphism. -/
lemma IsAdicLisseSheaf.of_iso {F G : AdicSheaf l X}
    (e : F ≅ G) (hF : IsAdicLisseSheaf F) : IsAdicLisseSheaf G := by
  obtain ⟨R, hR, h⟩ := hF
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, ⟨e'⟩⟩ := h f hf
  exact ⟨n, ⟨((f)^*ᵃ[l].mapIso e).symm ≪≫ e'⟩⟩

/-- The constant `ℓ`-adic sheaf is lisse, trivialised by the identity cover. -/
lemma isAdicLisseSheaf_adicConstantSheaf (X : Scheme.{u}) :
    IsAdicLisseSheaf (AdicSheaf.unit l X) := by
  refine ⟨.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, fun V f hf ↦ ?_⟩
  obtain ⟨⟩ := hf
  exact ⟨1, ⟨(adicUpperStarId l X).app _ ≪≫ (biproduct.isoProduct
    (fun _ : Fin 1 ↦ AdicSheaf.unit l X) ≪≫ productUniqueIso _).symm⟩⟩

/-- The zero sheaf is lisse: it is the empty direct sum of copies of `ℚ̄_ℓ`. -/
lemma IsAdicLisseSheaf.of_isZero {F : AdicSheaf l X}
    (hF : IsZero F) : IsAdicLisseSheaf F := by
  refine ⟨.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, fun V f hf ↦ ?_⟩
  obtain ⟨⟩ := hf
  refine ⟨0, ⟨IsZero.iso ?_ ?_⟩⟩
  · exact Functor.map_isZero _ hF
  · exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
      fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩

/-- A sheaf of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is *stratified lisse* if `X` is
the disjoint union of finitely many locally closed constructible subschemes `Z_k`, given by
immersions `i_k : Z_k ⟶ X` whose images are constructible subsets partitioning `X`, such that
each restriction `i_k^* F` is lisse (`definition-constructible-sheaves`). -/
def IsAdicStratifiedLisseSheaf (F : AdicSheaf l X) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (Z : ι → Scheme.{u}) (i : (k : ι) → Z k ⟶ X),
    (∀ k, IsImmersion (i k)) ∧ (∀ k, Topology.IsConstructible (Set.range (i k).base)) ∧
      (∀ x : X, ∃! k, x ∈ Set.range (i k).base) ∧
      ∀ k, IsAdicLisseSheaf ((i k)^*ᵃ[l].obj F)

/-- Being stratified lisse is invariant under isomorphism. -/
lemma IsAdicStratifiedLisseSheaf.of_iso
    {F G : AdicSheaf l X} (e : F ≅ G)
    (hF : IsAdicStratifiedLisseSheaf F) : IsAdicStratifiedLisseSheaf G := by
  obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hF
  exact ⟨ι, hι, Z, i, hi, hc, hcover, fun k ↦ (h k).of_iso ((_)^*ᵃ[l].mapIso e)⟩

/-- A lisse sheaf is stratified lisse, with the trivial stratification. -/
lemma IsAdicLisseSheaf.isAdicStratifiedLisseSheaf
    {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F) :
    IsAdicStratifiedLisseSheaf F :=
  ⟨Unit, inferInstance, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ inferInstance,
    fun _ ↦ by simp, fun x ↦ ⟨(), ⟨x, rfl⟩, fun _ _ ↦ rfl⟩,
    fun _ ↦ hF.of_iso ((adicUpperStarId l X).app F).symm⟩

/-- A sheaf of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is *constructible* if it is
stratified lisse locally on `X`: every point of `X` has an open neighbourhood `W`, given by an
open immersion `j : W ⟶ X`, such that `X ∩ W` is the disjoint union of finitely many locally
closed subschemes on each of which `j^* F` is lisse. On a quasi-compact `X` this is the same as
being stratified lisse. -/
def IsAdicConstructibleSheaf (F : AdicSheaf l X) :
    Prop :=
  ∀ x : X, ∃ (W : Scheme.{u}) (j : W ⟶ X), IsOpenImmersion j ∧ x ∈ Set.range j.base ∧
    IsAdicStratifiedLisseSheaf ((j)^*ᵃ[l].obj F)

/-- Being constructible is invariant under isomorphism. -/
lemma IsAdicConstructibleSheaf.of_iso
    {F G : AdicSheaf l X} (e : F ≅ G)
    (hF : IsAdicConstructibleSheaf F) : IsAdicConstructibleSheaf G := by
  intro x
  obtain ⟨W, j, hj, hx, h⟩ := hF x
  exact ⟨W, j, hj, hx, h.of_iso ((_)^*ᵃ[l].mapIso e)⟩

/-- A stratified lisse sheaf is constructible. -/
lemma IsAdicStratifiedLisseSheaf.isAdicConstructibleSheaf
    {F : AdicSheaf l X}
    (hF : IsAdicStratifiedLisseSheaf F) : IsAdicConstructibleSheaf F := by
  intro x
  exact ⟨X, 𝟙 X, inferInstance, ⟨x, rfl⟩, hF.of_iso ((adicUpperStarId l X).app F).symm⟩

/-- A lisse sheaf is constructible. -/
lemma IsAdicLisseSheaf.isAdicConstructibleSheaf
    {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F) :
    IsAdicConstructibleSheaf F :=
  hF.isAdicStratifiedLisseSheaf.isAdicConstructibleSheaf

/-- The constant `ℓ`-adic sheaf is constructible. -/
lemma isAdicConstructibleSheaf_adicConstantSheaf (X : Scheme.{u}) :
    IsAdicConstructibleSheaf (AdicSheaf.unit l X) :=
  (isAdicLisseSheaf_adicConstantSheaf X).isAdicConstructibleSheaf

/-- Pulling back a trivialisation: if `g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W` and `F ≅ ℚ̄_ℓ,Vⁿ`, then
`g^* F ≅ ℚ̄_ℓ,Wⁿ`. -/
lemma nonempty_upperStar_iso_biproduct {V W : Scheme.{u}} (g : W ⟶ V)
    (hg : Nonempty ((g)^*ᵃ[l].obj (AdicSheaf.unit l V) ≅
      AdicSheaf.unit l W))
    {F : AdicSheaf l V} {n : ℕ}
    (e : F ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V) :
    Nonempty ((g)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l W) :=
  ⟨(g)^*ᵃ[l].mapIso e ≪≫ (g)^*ᵃ[l].mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ hg.some⟩

/-- The pullback of a lisse sheaf is lisse: the pullback of a trivialising cover is a
trivialising cover, and the pullback of the constant `ℓ`-adic sheaf is the constant `ℓ`-adic
sheaf (`AlgebraicGeometry.ProEtale.upperStarAdicConstantSheafIso`). -/
theorem IsAdicLisseSheaf.upperStar {Y : Scheme.{u}} (f : Y ⟶ X)
    {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F) :
    IsAdicLisseSheaf ((f)^*ᵃ[l].obj F) := by
  obtain ⟨R, hR, h⟩ := hF
  refine ⟨R.pullbackArrows f, Precoverage.pullbackArrows_mem f hR, ?_⟩
  rintro _ _ ⟨V, g, hg⟩
  obtain ⟨n, ⟨e⟩⟩ := h g hg
  obtain ⟨e'⟩ := nonempty_upperStar_iso_biproduct (pullback.fst g f)
    ⟨adicUpperStarUnitIso l _⟩ e
  exact ⟨n, ⟨(adicUpperStarCompIso l pullback.condition.symm).app F ≪≫ e'⟩⟩

/-- The pullback of a stratified lisse sheaf is stratified lisse: the base changes of the
strata are strata, and the restrictions to them are pullbacks of lisse sheaves. -/
theorem IsAdicStratifiedLisseSheaf.upperStar {Y : Scheme.{u}} (f : Y ⟶ X)
    {F : AdicSheaf l X}
    (hF : IsAdicStratifiedLisseSheaf F) :
    IsAdicStratifiedLisseSheaf ((f)^*ᵃ[l].obj F) := by
  obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hF
  refine ⟨ι, hι, fun k ↦ pullback (i k) f, fun k ↦ pullback.snd (i k) f, fun k ↦ inferInstance,
    fun k ↦ ?_, fun y ↦ ?_, fun k ↦ ((h k).upperStar (pullback.fst (i k) f)).of_iso
      ((adicUpperStarCompIso l pullback.condition).app F)⟩
  · rw [Scheme.Pullback.range_snd]
    exact f.isConstructible_preimage (hc k)
  obtain ⟨k, ⟨z, hz⟩, hk⟩ := hcover (f y)
  obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback z y hz
  refine ⟨k, ⟨t, ht⟩, fun k' ⟨t', ht'⟩ ↦ hk k' ⟨pullback.fst (i k') f t', ?_⟩⟩
  rw [← ht', ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

/-- The pullback of a constructible sheaf is constructible: the preimages of the open
neighbourhoods and of the strata are open neighbourhoods and strata, given by the base changes
of the immersions, and the restrictions to them are pullbacks of lisse sheaves. -/
theorem IsAdicConstructibleSheaf.upperStar {Y : Scheme.{u}} (f : Y ⟶ X)
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) :
    IsAdicConstructibleSheaf ((f)^*ᵃ[l].obj F) := by
  intro y
  obtain ⟨W, j, hj, ⟨w, hw⟩, h⟩ := hF (f y)
  obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback w y hw
  exact ⟨pullback j f, pullback.snd j f, inferInstance, ⟨t, ht⟩,
    (h.upperStar (pullback.fst j f)).of_iso ((adicUpperStarCompIso l pullback.condition).app F)⟩

/-- A finite direct sum of lisse sheaves is lisse: refine the two trivialising covers. -/
theorem IsAdicLisseSheaf.biprod
    {F G : AdicSheaf l X} (hF : IsAdicLisseSheaf F)
    (hG : IsAdicLisseSheaf G) : IsAdicLisseSheaf (F ⊞ G) := by
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
  obtain ⟨e₁⟩ := nonempty_upperStar_iso_biproduct (pullback.fst (f i) (f' j))
    ⟨adicUpperStarUnitIso l _⟩ e
  obtain ⟨e₂⟩ := nonempty_upperStar_iso_biproduct (pullback.snd (f i) (f' j))
    ⟨adicUpperStarUnitIso l _⟩ e'
  refine ⟨n + m, ⟨(_)^*ᵃ[l].mapBiprod F G ≪≫ biprod.mapIso
    ((adicUpperStarComp l _ _).app F ≪≫ e₁)
    ((adicUpperStarCongr l pullback.condition).app G ≪≫ (adicUpperStarComp l _ _).app G ≪≫ e₂) ≪≫
    biprodBiproductSumIso (fun _ ↦ AdicSheaf.unit l _) ≪≫
      biproduct.whiskerEquiv finSumFinEquiv (g := fun _ ↦ AdicSheaf.unit l _)
        (fun _ ↦ Iso.refl _)⟩⟩

/-- A binary direct sum of stratified lisse sheaves is stratified lisse: on the common
refinement of the two stratifications both summands are lisse. -/
theorem IsAdicStratifiedLisseSheaf.biprod
    {F G : AdicSheaf l X}
    (hF : IsAdicStratifiedLisseSheaf F) (hG : IsAdicStratifiedLisseSheaf G) :
    IsAdicStratifiedLisseSheaf (F ⊞ G) := by
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
        ((adicUpperStarCompIso l pullback.condition.symm).app G))).of_iso
      ((adicUpperStarComp l (pullback.fst (i k.1) (i' k.2)) (i k.1)).app (F ⊞ G) ≪≫
        (pullback.fst (i k.1) (i' k.2))^*ᵃ[l].mapIso ((i k.1)^*ᵃ[l].mapBiprod F G) ≪≫
        (pullback.fst (i k.1) (i' k.2))^*ᵃ[l].mapBiprod _ _).symm

/-- A binary direct sum of constructible sheaves is constructible: on the intersection of the
two open neighbourhoods both summands are stratified lisse. -/
theorem IsAdicConstructibleSheaf.biprod
    {F G : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) (hG : IsAdicConstructibleSheaf G) :
    IsAdicConstructibleSheaf (F ⊞ G) := by
  intro x
  obtain ⟨W, j, hj, ⟨w, hw⟩, h⟩ := hF x
  obtain ⟨W', j', hj', ⟨w', hw'⟩, h'⟩ := hG x
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback w w' (hw.trans hw'.symm)
  refine ⟨pullback j j', pullback.fst j j' ≫ j, inferInstance,
    ⟨t, by rw [Scheme.Hom.comp_apply, ht, hw]⟩, ?_⟩
  exact ((h.upperStar _).biprod ((h'.upperStar (pullback.snd j j')).of_iso
      ((adicUpperStarCompIso l pullback.condition.symm).app G))).of_iso
    ((adicUpperStarComp l (pullback.fst j j') j).app (F ⊞ G) ≪≫
      (pullback.fst j j')^*ᵃ[l].mapIso ((j)^*ᵃ[l].mapBiprod F G) ≪≫
      (pullback.fst j j')^*ᵃ[l].mapBiprod _ _).symm

/-- A sheaf of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is an *irreducible `ℓ`-adic local
system* if it is lisse and nonzero, and every lisse subsheaf of it is zero or all of it. For
`X` connected this says that the corresponding continuous representation of `π₁(X)` is
irreducible. -/
def IsIrreducibleAdicLocalSystem
    (F : AdicSheaf l X) : Prop :=
  IsAdicLisseSheaf F ∧ ¬ IsZero F ∧
    ∀ (G : AdicSheaf l X) (i : G ⟶ F), Mono i →
      IsAdicLisseSheaf G → IsZero G ∨ IsIso i

variable (l X) in
/-- Constructibility of `ℓ`-adic pro-étale sheaves, as an object property. -/
def adicConstructibleSheaf :
    ObjectProperty (AdicSheaf l X) :=
  fun F ↦ IsAdicConstructibleSheaf F

lemma adicConstructibleSheaf_iff (F : AdicSheaf l X) :
    adicConstructibleSheaf l X F ↔ IsAdicConstructibleSheaf F :=
  Iff.rfl

instance : (adicConstructibleSheaf l X).IsClosedUnderIsomorphisms where
  of_iso e hF := IsAdicConstructibleSheaf.of_iso e hF

instance : (adicConstructibleSheaf l X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (IsAdicLisseSheaf.of_isZero (isZero_zero _)).isAdicConstructibleSheaf⟩

/-- **Finite products of constructible sheaves are constructible**: the empty product is `0`,
and a binary product is a binary direct sum
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.biprod`). -/
instance : (adicConstructibleSheaf l X).IsClosedUnderFiniteProducts := by
  have : (adicConstructibleSheaf l X).IsClosedUnderBinaryProducts := by
    refine ⟨fun Y ⟨p⟩ ↦ ?_⟩
    exact ((p.prop_diag_obj ⟨.left⟩).biprod (p.prop_diag_obj ⟨.right⟩)).of_iso
      (biprod.isoProd _ _ ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair _)).symm ≪≫
        (p.isLimit.conePointUniqueUpToIso (limit.isLimit _)).symm)
  exact .mk'

end AlgebraicGeometry.ProEtale
