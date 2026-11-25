/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

/-!
# The exceptional Künneth maps are isomorphisms

Let `k` be a field and `Λ` a finite ring whose exponent is invertible in `k`. For a morphism
`g : T ⟶ S` admitting a compactification, with `S` of finite type over `k`, and a scheme `W` of
finite type over `k`, consider the products `P = S ×_k W` (projections `q`, `r`) and
`Q = T ×_k W`, with the base change `h = g × 𝟙 : Q ⟶ P` of `g` along `q`. We show that the two
canonical maps

* the base change map `Lq'^* Rg^! N ⟶ Rh^! Lq^* N`
  (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`), and
* the tensor map `Rh^!(Lq^* N) ⊗ᴸ Lh^* Lr^* M ⟶ Rh^!(Lq^* N ⊗ᴸ Lr^* M)`
  (`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`)

are isomorphisms for all `N` and `M` (`AlgebraicGeometry.Etale.isExceptionalKunneth`). Together
they identify `Rh^!(N ⊠ M)` with `Rg^! N ⊠ M`, the exceptional Künneth formula
(`proposition-exceptional-external-kunneth--1`).

Following the blueprint proof, the property (`AlgebraicGeometry.Etale.IsExceptionalKunneth`)
holds for smooth morphisms, by smooth duality
(`proposition-exceptional-inverse-image-smooth-morphism`) and its base change
(`proposition-exceptional-inverse-image-smooth-morphism--6`), and for closed immersions, by
localization (`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.ClosedImmersion`); it
is stable under composition, by the composition laws of the canonical maps, and local on the source
for open covers, by the étale locality of the canonical maps. Locally on the source, every `g`
factors as a closed immersion into an affine space over an affine open of `S`, followed by the
projection and the open immersion.

## Main definitions

- `AlgebraicGeometry.Etale.IsExceptionalKunneth`

## Main statements

- `AlgebraicGeometry.Etale.isExceptionalKunneth`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section TensorMap

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f] [IsIso (projectionMap A f)]
  {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adj : R(f)_![A] ⊣ G)

/-- The tensor map `τ_f(M, N) : G M ⊗ᴸ Lf^* N ⟶ G(M ⊗ᴸ N)` of a right adjoint `G` of `Rf_!`
(`AlgebraicGeometry.Etale.lowerShriekRightAdjointTensorMap`), with source and target written
with the derived tensor product `AlgebraicGeometry.Etale.derivedTensor`. -/
noncomputable def lowerShriekRightAdjointTensorMapOfDerivedTensor
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensor A X).obj (G.obj M)).obj ((L((f)^*[A])).obj N) ⟶
      G.obj (((derivedTensor A Y).obj M).obj N) :=
  lowerShriekRightAdjointTensorMap adj M N

lemma isIso_lowerShriekRightAdjointTensorMapOfDerivedTensor_iff
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (lowerShriekRightAdjointTensorMapOfDerivedTensor adj M N) ↔
      IsIso (lowerShriekRightAdjointTensorMap adj M N) :=
  Iff.rfl

/-- The proposition that the tensor map `τ_f(M, N) : G M ⊗ᴸ Lf^* N ⟶ G(M ⊗ᴸ N)` is an
isomorphism. Stated for a general coefficient category, so that its specialization to a finite
ring of coefficients does not involve comparing monoidal structures. -/
def IsIsoLowerShriekRightAdjointTensorMap
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
  IsIso (lowerShriekRightAdjointTensorMap adj M N)

lemma isIsoLowerShriekRightAdjointTensorMap_iff
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIsoLowerShriekRightAdjointTensorMap adj M N ↔
      IsIso (lowerShriekRightAdjointTensorMap adj M N) :=
  Iff.rfl

end TensorMap

section Composition

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (w : f ≫ g = h)
  [HasCompactification f] [HasCompactification g] [HasCompactification h]
  [IsIso (projectionMap A f)] [IsIso (projectionMap A g)] [IsIso (projectionMap A h)]
  {Gf : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adjf : R(f)_![A] ⊣ Gf)
  {Gg : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (adjg : R(g)_![A] ⊣ Gg)
  {Gh : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adjh : R(h)_![A] ⊣ Gh)
  (e : R(h)_![A] ≅ R(f)_![A] ⋙ R(g)_![A])
  (he : Adjunction.ProjectionCompCompatible (fun M N ↦ ((projectionMap A f).app M).app N)
    (fun M N ↦ ((projectionMap A g).app M).app N) (fun M N ↦ ((projectionMap A h).app M).app N)
    (fun N ↦ (leftDerivedUpperStarComp A f g h w.symm).hom.app N) e)
include he

set_option hygiene false in
/-- The isomorphism `Gh ≅ Gg ⋙ Gf` of right adjoints induced by `e`. -/
local notation "ρ[" e "]" =>
  Adjunction.rightAdjointUniq (adjh.ofNatIsoLeft e) (adjf.comp adjg)

/-- **The tensor map of a composite.** For `h = f ≫ g` and right adjoints `Gf`, `Gg`, `Gh` of
`Rf_!`, `Rg_!`, `Rh_!` (for finite coefficients, `Rf^!`, `Rg^!`, `Rh^!`), the tensor map of `h`
at `(M, N)` is an isomorphism if the tensor maps of `f` at `(Gg M, Lg^* N)` and of `g` at
`(M, N)` are. -/
theorem isIso_lowerShriekRightAdjointTensorMap_comp
    (M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hf : IsIso (lowerShriekRightAdjointTensorMap adjf (Gg.obj M) ((L((g)^*[A])).obj N)))
    (hg : IsIso (lowerShriekRightAdjointTensorMap adjg M N)) :
    IsIso (lowerShriekRightAdjointTensorMap adjh M N) := by
  have hc := lowerShriekRightAdjointTensorMap_comp w adjf adjg adjh e he M N
  have : IsIso (lowerShriekRightAdjointTensorMap adjh M N ≫ (ρ[e]).hom.app (M ⊗ N)) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((ρ[e]).hom.app (M ⊗ N))

/-- **Descent of the tensor maps along a composite.** For `h = f ≫ g` with an associative
projection map of `f` and `θ_f` invertible everywhere, if the tensor map of `h` at `(M, N)` is
an isomorphism, then so is `Gf` of the tensor map of `g` at `(M, N)`. -/
theorem isIso_map_lowerShriekRightAdjointTensorMap_of_comp
    (hassoc : ProjectionMapAssociativity A f)
    (hθ : ∀ P, IsIso (lowerShriekRightAdjointUnitTensorMap adjf P))
    (M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hh : IsIso (lowerShriekRightAdjointTensorMap adjh M N)) :
    IsIso (Gf.map (lowerShriekRightAdjointTensorMap adjg M N)) := by
  have := isIso_lowerShriekRightAdjointTensorMap_of_forall adjf hassoc hθ (Gg.obj M)
    ((L((g)^*[A])).obj N)
  have hc := lowerShriekRightAdjointTensorMap_comp w adjf adjg adjh e he M N
  have : IsIso (lowerShriekRightAdjointTensorMap adjh M N ≫ (ρ[e]).hom.app (M ⊗ N)) :=
    inferInstance
  rw [hc] at this
  have := (isIso_comp_left_iff _ _).1 this
  have := (isIso_comp_left_iff _ _).1 this
  exact (isIso_comp_left_iff _ _).1 this

end Composition

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (k : Type u) [Field k]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section Smooth

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
  [SmoothOfRelativeDimension d f] [HasInvertibleExponent Λ X]

include d in
/-- For a smooth `f` of relative dimension `d`, the canonical map `θ_f` is an isomorphism at every
object (`proposition-exceptional-inverse-image-smooth-morphism`). -/
lemma isIso_dualizingComplexTensorMapOfIsIso_of_smoothOfRelativeDimension
    (P : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (dualizingComplexTensorMap Λ f P) := by
  obtain ⟨-, -, -, -, h⟩ := exists_dualizingComplex_iso_and_tensor Λ f d
  exact h P

include d in
/-- For a smooth `f` of relative dimension `d`, the dualizing complex `ω_f` is invertible
(`proposition-exceptional-inverse-image-smooth-morphism`). -/
lemma isInvertible_dualizingComplex_of_smoothOfRelativeDimension :
    DerivedCategory.isInvertible Λ X (dualizingComplex Λ f) := by
  obtain ⟨L, hL₁, hL, ⟨e⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ f d
  have := hL₁
  exact DerivedCategory.isInvertible.of_iso e.symm
    (isInvertible_shift_singleFunctor_obj_of_isLocallyConstantSheaf L hL _)

end Smooth

/-- A morphism `g : T ⟶ S` admitting a compactification *satisfies the exceptional Künneth
formula over `k`* if, for every `W` of finite type over `k`, all cartesian squares
`P = S ×_k W` (projections `q`, `r`, for `S` of finite type over `k`) and `Q = T ×_k W`
(projection `q'`, and base change `h : Q ⟶ P` of `g` along `q`), the base change map
`Lq'^* Rg^! N ⟶ Rh^! Lq^* N` and the tensor map
`Rh^!(Lq^* N) ⊗ᴸ Lh^* Lr^* M ⟶ Rh^!(Lq^* N ⊗ᴸ Lr^* M)` are isomorphisms for all `N` and `M`. -/
def IsExceptionalKunneth {T S : Scheme.{u}} (g : T ⟶ S) [HasCompactification g] : Prop :=
  ∀ ⦃W P Q : Scheme.{u}⦄ (b : S ⟶ Spec (.of k)) (c : W ⟶ Spec (.of k))
    [LocallyOfFiniteType b] [QuasiCompact b] [LocallyOfFiniteType c] [QuasiCompact c]
    {q : P ⟶ S} {r : P ⟶ W} (_ : IsPullback q r b c) {q' : Q ⟶ T} {h : Q ⟶ P}
    (sq : IsPullback q' h g q) [HasCompactification h] [QuasiCompact h],
    (∀ N, IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app N)) ∧
      ∀ N M, IsIsoLowerShriekRightAdjointTensorMap (rightDerivedUpperShriekAdjunction Λ h)
        ((L((q)^*[ModuleCat.{u + 1} Λ])).obj N) ((L((r)^*[ModuleCat.{u + 1} Λ])).obj M)

variable {Λ k}

/-- The exceptional Künneth property only depends on the morphism. -/
lemma IsExceptionalKunneth.of_eq {T S : Scheme.{u}} {g g' : T ⟶ S} [HasCompactification g]
    [HasCompactification g'] (hg : IsExceptionalKunneth Λ k g) (e : g = g') :
    IsExceptionalKunneth Λ k g' := by
  subst e
  exact hg

variable (Λ k) [HasInvertibleExponent Λ (Spec (.of k))]

/-- **Smooth morphisms** satisfy the exceptional Künneth formula: the base change map is invertible
by `proposition-exceptional-inverse-image-smooth-morphism--6`, and the tensor maps of the smooth
base change `h` are invertible since `θ_h` is
(`proposition-exceptional-inverse-image-smooth-morphism`). The base `S` is quasi-separated, as in
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`
(it is of finite type over `k` in the blueprint). -/
theorem isExceptionalKunneth_of_smoothOfRelativeDimension {T S : Scheme.{u}}
    [QuasiSeparatedSpace S] (g : T ⟶ S) [HasCompactification g] (d : ℕ)
    [SmoothOfRelativeDimension d g] :
    IsExceptionalKunneth Λ k g := by
  intro W P Q b c _ _ _ _ q r sqP q' h sq _ _
  have : HasInvertibleExponent Λ T := .of_hom (g ≫ b)
  have : HasInvertibleExponent Λ Q := .of_hom (h ≫ q ≫ b)
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d h := MorphismProperty.of_isPullback sq ‹_›
  refine ⟨fun N ↦ ?_, fun N M ↦ ?_⟩
  · have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ g d sq
    infer_instance
  · exact (isIsoLowerShriekRightAdjointTensorMap_iff _ _ _).2
      (isIso_lowerShriekRightAdjointTensorMap_of_forall _ (projectionMapAssociativity Λ h)
        (isIso_dualizingComplexTensorMapOfIsIso_of_smoothOfRelativeDimension Λ h d) _ _)

/-- **Closed immersions** satisfy the exceptional Künneth formula
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isClosedImmersion`,
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekTensorMap_pullback_of_isClosedImmersion`).
-/
theorem isExceptionalKunneth_of_isClosedImmersion {T S : Scheme.{u}} (i : T ⟶ S)
    [IsClosedImmersion i] : IsExceptionalKunneth Λ k i := by
  intro W P Q b c _ _ _ _ q r sqP q' h sq _ _
  exact ⟨isIso_rightDerivedUpperShriekBaseChangeMap_of_isClosedImmersion Λ b c sqP i sq,
    fun N M ↦ (isIsoLowerShriekRightAdjointTensorMap_iff _ _ _).2
      (isIso_rightDerivedUpperShriekTensorMap_pullback_of_isClosedImmersion Λ b c sqP i sq N M)⟩

omit [HasInvertibleExponent Λ (Spec (.of k))] in
/-- **Composition.** The exceptional Künneth property is stable under composition, by the
composition laws of the base change maps
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff`) and of the
tensor maps (`AlgebraicGeometry.Etale.isIso_lowerShriekRightAdjointTensorMap_comp`). -/
theorem IsExceptionalKunneth.comp {T T₂ S : Scheme.{u}} (g₁ : T ⟶ T₂) (g₂ : T₂ ⟶ S)
    [HasCompactification g₁] [HasCompactification g₂] [HasCompactification (g₁ ≫ g₂)]
    [QuasiCompact g₁] [QuasiCompact g₂] (hg₁ : IsExceptionalKunneth Λ k g₁)
    (hg₂ : IsExceptionalKunneth Λ k g₂) : IsExceptionalKunneth Λ k (g₁ ≫ g₂) := by
  intro W P Q b c _ _ _ _ q r sqP q' h sq _ _
  obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
  have sq₂ : IsPullback (pullback.fst g₂ q) (pullback.snd g₂ q) g₂ q :=
    IsPullback.of_hasPullback g₂ q
  let h₁ : Q ⟶ pullback g₂ q := pullback.lift (q' ≫ g₁) h (by rw [Category.assoc, sq.w])
  have hw : h₁ ≫ pullback.snd g₂ q = h := pullback.lift_snd _ _ _
  have sq₁ : IsPullback q' h₁ g₁ (pullback.fst g₂ q) :=
    IsPullback.of_bot (by rw [hw]; exact sq) (pullback.lift_fst _ _ _).symm sq₂
  have sqP₂ : IsPullback (pullback.fst g₂ q) (pullback.snd g₂ q ≫ r) (g₂ ≫ b) c :=
    sq₂.paste_vert sqP
  have : HasCompactification h₁ := .of_isPullback sq₁
  have : QuasiCompact h₁ := MorphismProperty.of_isPullback sq₁ ‹_›
  have H₁ := hg₁ (g₂ ≫ b) c sqP₂ sq₁
  have H₂ := hg₂ b c sqP sq₂
  refine ⟨fun N ↦ ?_, fun N M ↦ ?_⟩
  · have := H₂.1 N
    exact (isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff sq₁ sq₂ sq rfl hw N
      (H₁.1 _)).2 inferInstance
  · refine (isIsoLowerShriekRightAdjointTensorMap_iff _ _ _).2 ?_
    have := (isIsoLowerShriekRightAdjointTensorMap_iff _ _ _).1 (H₂.2 N M)
    have := (isIsoLowerShriekRightAdjointTensorMap_iff _ _ _).1
      (H₁.2 ((R(g₂)^![Λ]).obj N) M)
    have := H₂.1 N
    let e₁ : (L((pullback.fst g₂ q)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(g₂)^![Λ]).obj N) ≅ (R(pullback.snd g₂ q)^![Λ]).obj
          ((L((q)^*[ModuleCat.{u + 1} Λ])).obj N) :=
      asIso ((rightDerivedUpperShriekBaseChangeMap Λ sq₂).app N)
    have := isIso_lowerShriekRightAdjointTensorMap_of_iso_left
      (rightDerivedUpperShriekAdjunction Λ h₁) e₁
      (N := (L((pullback.snd g₂ q ≫ r)^*[ModuleCat.{u + 1} Λ])).obj M)
    have := isIso_lowerShriekRightAdjointTensorMap_of_iso_right
      (rightDerivedUpperShriekAdjunction Λ h₁)
      ((leftDerivedUpperStarComp _ (pullback.snd g₂ q) r).app M)
      (M := (R(pullback.snd g₂ q)^![Λ]).obj
        ((L((q)^*[ModuleCat.{u + 1} Λ])).obj N))
    exact isIso_lowerShriekRightAdjointTensorMap_comp hw (rightDerivedUpperShriekAdjunction Λ h₁)
      (rightDerivedUpperShriekAdjunction Λ (pullback.snd g₂ q))
      (rightDerivedUpperShriekAdjunction Λ h) (E _ _ _ hw) (hPF _ _ _ hw) _ _ ‹_› ‹_›

/-- **Locality on the source.** If `u_i : U_i ⟶ T` is a jointly surjective family of
quasi-compact open immersions and every `u_i ≫ g` satisfies the exceptional Künneth formula,
then so does `g`: through the composition laws, the canonical maps of `u_i ≫ g` determine
`Ru_i^!`, hence `Lu_i^*`, of those of `g`, and isomorphisms descend along the family. -/
theorem IsExceptionalKunneth.of_jointlySurjective {T S : Scheme.{u}} (g : T ⟶ S)
    [HasCompactification g] [QuasiCompact g] {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ T)
    [∀ i, IsOpenImmersion (u i)] [∀ i, QuasiCompact (u i)] [∀ i, HasCompactification (u i ≫ g)]
    (hu : ∀ x : T, ∃ (i : ι) (y : U i), u i y = x) (H : ∀ i, IsExceptionalKunneth Λ k (u i ≫ g)) :
    IsExceptionalKunneth Λ k g := by
  intro W P Q b c _ _ _ _ q r sqP q' h sq _ _
  obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
  have : HasInvertibleExponent Λ Q := .of_hom (h ≫ q ≫ b)
  have (i : ι) : HasInvertibleExponent Λ (U i) := .of_hom (u i ≫ g ≫ b)
  let v (i : ι) : pullback (u i) q' ⟶ Q := pullback.snd (u i) q'
  have sqv (i : ι) : IsPullback (pullback.fst (u i) q') (v i) (u i) q' :=
    IsPullback.of_hasPullback _ _
  have sqi (i : ι) : IsPullback (pullback.fst (u i) q') (v i ≫ h) (u i ≫ g) q :=
    (sqv i).paste_vert sq
  have (i : ι) : HasInvertibleExponent Λ (pullback (u i) q') := .of_hom (v i ≫ h ≫ q ≫ b)
  have hv (z : Q) : ∃ (i : ι) (y : ↥(pullback (u i) q')), v i y = z := by
    obtain ⟨i, y, hy⟩ := hu (q' z)
    obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback (f := u i) (g := q') y z hy
    exact ⟨i, t, ht⟩
  have (i : ι) : HasCompactification (u i) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have (i : ι) : HasCompactification (v i) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have (i : ι) : HasCompactification (v i ≫ h) := .of_isPullback (sqi i)
  have (i : ι) : QuasiCompact (v i ≫ h) := MorphismProperty.of_isPullback (sqi i) inferInstance
  have hθ (i : ι) := isIso_dualizingComplexTensorMapOfIsIso_of_smoothOfRelativeDimension Λ (v i) 0
  have hω (i : ι) := (isInvertible_iff_exists_derivedTensor _).2
    (isInvertible_dualizingComplex_of_smoothOfRelativeDimension Λ (v i) 0)
  refine ⟨fun N ↦ ?_, fun N M ↦ ?_⟩
  · refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ v hv _ fun i ↦ ?_
    have := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ (sqv i)
    have := (isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff (sqv i) sq (sqi i) rfl rfl N
      inferInstance).1 ((H i b c sqP (sqi i)).1 N)
    exact isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map
      (rightDerivedUpperShriekAdjunction Λ (v i)) (hθ i) (hω i) _ this
  · refine (isIsoLowerShriekRightAdjointTensorMap_iff _ _ _).2 ?_
    refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ v hv _ fun i ↦ ?_
    exact isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map
      (rightDerivedUpperShriekAdjunction Λ (v i)) (hθ i) (hω i) _
      (isIso_map_lowerShriekRightAdjointTensorMap_of_comp rfl
        (rightDerivedUpperShriekAdjunction Λ (v i)) (rightDerivedUpperShriekAdjunction Λ h)
        (rightDerivedUpperShriekAdjunction Λ (v i ≫ h))
        (E _ _ _ rfl) (hPF _ _ _ rfl) (projectionMapAssociativity Λ (v i)) (hθ i) _ _
        ((isIsoLowerShriekRightAdjointTensorMap_iff _ _ _).1 ((H i b c sqP (sqi i)).2 N M)))

/-- A morphism locally of finite type between affine schemes factors as a closed immersion into
an affine space of finite dimension followed by the projection. -/
lemma exists_isClosedImmersion_affineSpace {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    ∃ (s : Type u) (_ : Finite s) (c : X ⟶ 𝔸(s; Y)),
      IsClosedImmersion c ∧ c ≫ 𝔸(s; Y) ↘ Y = f := by
  have hft : f.appTop.hom.FiniteType := HasRingHomProperty.appTop @LocallyOfFiniteType f ‹_›
  let := f.appTop.hom.toAlgebra
  obtain ⟨t, ht⟩ := hft.out
  refine ⟨t, inferInstance, AffineSpace.homOfVector f (fun x : t ↦ x.1),
    AffineSpace.isClosedImmersion_homOfVector f _ ?_, AffineSpace.homOfVector_over f _⟩
  have h₁ := Algebra.adjoin_eq_ring_closure (R := Γ(Y, ⊤)) (A := Γ(X, ⊤)) (t : Set Γ(X, ⊤))
  rw [ht, Algebra.top_toSubring] at h₁
  have hA : Set.range ⇑(ConcreteCategory.hom f.appTop) =
      Set.range ⇑(algebraMap Γ(Y, ⊤) Γ(X, ⊤)) := rfl
  have hB : Set.range (fun x : t ↦ x.1) = (t : Set Γ(X, ⊤)) := by
    ext
    simp
  rw [hA, hB, ← h₁]

/-- **The exceptional Künneth formula.** Every quasi-compact morphism `g : T ⟶ S` admitting a
compactification, with `S` of finite type over `k`, satisfies the exceptional Künneth formula
(`AlgebraicGeometry.Etale.IsExceptionalKunneth`): locally on `T`, `g` is a closed immersion into
an affine space over an affine open `V` of `S`, followed by the projection and the open
immersion of `V`. -/
theorem isExceptionalKunneth {T S : Scheme.{u}} (g : T ⟶ S) [HasCompactification g]
    [QuasiCompact g] (b : S ⟶ Spec (.of k)) [LocallyOfFiniteType b] [QuasiCompact b] :
    IsExceptionalKunneth Λ k g := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace b
  have : IsNoetherian S := { __ := LocallyOfFiniteType.isLocallyNoetherian b }
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (g ≫ b)
  have : IsNoetherian T := { __ := LocallyOfFiniteType.isLocallyNoetherian (g ≫ b) }
  have hx (x : T) : ∃ (V : S.Opens) (U : T.Opens), IsAffineOpen V ∧ IsAffineOpen U ∧ x ∈ U ∧
      U ≤ g ⁻¹ᵁ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (g ⁻¹ᵁ V : Set T) from hxV) (g ⁻¹ᵁ V).isOpen
    exact ⟨V, U, hV, hU, hxU, hUV⟩
  choose V U hV hU hxU hUV using hx
  refine IsExceptionalKunneth.of_jointlySurjective Λ k g (fun x ↦ (U x).ι)
    (fun x ↦ ⟨x, ⟨x, hxU x⟩, by simp⟩) fun x ↦ ?_
  have : IsAffine (U x) := hU x
  have : IsAffine (V x) := hV x
  obtain ⟨s, _, c, _, hc⟩ := exists_isClosedImmersion_affineSpace (g.resLE (V x) (U x) (hUV x))
  have : HasCompactification (V x).ι :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have h₁ := isExceptionalKunneth_of_isClosedImmersion Λ k c
  have h₂ := isExceptionalKunneth_of_smoothOfRelativeDimension Λ k (𝔸(s; V x) ↘ V x) (Nat.card s)
  have h₃ := isExceptionalKunneth_of_smoothOfRelativeDimension Λ k (V x).ι 0
  refine (IsExceptionalKunneth.comp Λ k c _ h₁
    (IsExceptionalKunneth.comp Λ k _ _ h₂ h₃)).of_eq ?_
  rw [← Category.assoc, hc, Scheme.Hom.resLE_comp_ι]

end Etale

end AlgebraicGeometry
