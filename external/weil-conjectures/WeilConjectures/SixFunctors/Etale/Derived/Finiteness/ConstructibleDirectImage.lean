/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact

/-!
# Constructibility of direct images: the predicate `𝒞(f)`

For a coefficient ring `Λ` and a morphism of schemes `f : X ⟶ S`, the predicate
`AlgebraicGeometry.Etale.HasConstructibleDirectImages Λ f` (the blueprint's `𝒞(f)`,
`proposition-proper-direct-image-finite-coefficients`) says that every higher direct image `Rᵠf_* F`
of every constructible sheaf `F` of `Λ`-modules on `X_ét` is constructible on `S_ét`. Here
`Rᵠf_* F` is the `q`-th homology sheaf of the total derived direct image `Rf_*(F[0])`.

This file proves the formal properties of `𝒞` that need no geometry:

- `AlgebraicGeometry.Etale.HasConstructibleDirectImages.constructibleHomology_obj`: if `𝒞(f)`
  holds, then `Rf_*` sends every bounded complex with constructible homology sheaves to a
  complex with constructible homology sheaves (dévissage along the truncation triangles);
- `AlgebraicGeometry.Etale.HasConstructibleDirectImages.comp`: `𝒞(f)` and `𝒞(g)` imply
  `𝒞(f ≫ g)` (`proposition-proper-direct-image-finite-coefficients`).

The blueprint proves the composition lemma with the Grothendieck spectral sequence; we use
instead that `Hⁿ(Rg_* K)` only depends on the truncation `τ^{≤ n} K` of a complex `K` with
`K ∈ D^{≥ 0}` (`Rg_*` is left t-exact, `CategoryTheory.Functor.isGE_rightDerivedFunctor_obj`),
and the dévissage above. Both arguments only use that constructible sheaves form a weak Serre
class (`thm-constructible-serre`), which holds for a finite coefficient ring.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Constructibility under direct
image.

For a morphism `f : X ⟶ S`, the assertion `𝒞(f)`: for every constructible sheaf `F` of
`Λ`-modules on `X_ét` and every `q`, the higher direct image `Rᵠf_* F` is constructible on
`S_ét`. Here `Rᵠf_* F` is the `q`-th homology sheaf of the total derived direct image
`Rf_*(F[0])`; it vanishes for `q < 0`, so asking for all `q : ℤ` is the same as asking for all
`q ≥ 0`. The blueprint applies the predicate to morphisms between schemes of finite type over a
field `k` and a finite ring `Λ` killed by an integer invertible in `k`; these assumptions are
made in the statements using it. -/
def HasConstructibleDirectImages {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F →
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))

variable {Λ}

/-- **Dévissage of bounded constructible complexes.** A triangulated subcategory `P` of
`D(X_ét, Λ)`, closed under isomorphisms, containing every constructible sheaf placed in
degree `0` contains every bounded complex with constructible homology sheaves: by induction
on the length of the amplitude, along the truncation triangle `τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶`
whose third term is `Hᵇ K` placed in degree `b`. -/
lemma prop_of_constructibleHomology {X : Scheme.{u}}
    (P : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F →
      P ((singleFunctor _ 0).obj F))
    (m : ℕ) :
    ∀ (a : ℤ) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      K.IsGE a → K.IsLE (a + m - 1) →
      Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) X K → P K := by
  induction m with
  | zero =>
    intro a K _ _ _
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    exact P.prop_of_isZero (TStructure.t.isZero K (a - 1) a (by lia))
  | succ m ih =>
    intro a K _ _ hK
    set b : ℤ := a + m
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    -- the third term is `Hᵇ K` placed in degree `b`
    have : T.obj₃.IsLE b := by
      have : K.IsLE b := TStructure.t.isLE_of_le K (a + ↑(m + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b)
    have : T.obj₃.IsGE b := inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj K) b)
    obtain ⟨G, ⟨eG⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl (isZero_of_isLE _ (b - 1) _ (by lia))
      (isZero_of_isLE _ (b - 1) _ (by lia))
    have hG : IsConstructibleSheaf G := by
      have : IsConstructibleSheaf ((homologyFunctor _ b).obj T.obj₂) := hK b
      exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ b).map T.mor₂) ≪≫
        (homologyFunctor _ b).mapIso eG ≪≫ (singleFunctorCompHomologyFunctorIso _ b).app G)
    have h₃ : P T.obj₃ := by
      have : P (((singleFunctor _ 0).obj G)⟦-b⟧) := P.le_shift (-b) _ (hP G hG)
      exact P.prop_of_iso ((((singleFunctors _).shiftIso (-b) b 0 (by lia)).app G) ≪≫ eG.symm)
        this
    -- the first term is handled by induction
    have h₁ : P T.obj₁ := by
      refine ih a T.obj₁
        (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a))
        (TStructure.t.isLE_truncLT_obj _ _ _ (by lia)) fun q ↦ ?_
      by_cases hq : q < b
      · have : IsIso ((homologyFunctor _ q).map T.mor₁) :=
          isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
            (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
        have : IsConstructibleSheaf ((homologyFunctor _ q).obj T.obj₂) := hK q
        exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ q).map T.mor₁)).symm
      · have : T.obj₁.IsLE (b - 1) := TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
        exact IsConstructibleSheaf.of_isZero (isZero_of_isLE _ (b - 1) _ (by lia))
    exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

/-- A bounded complex with constructible homology sheaves lies in every triangulated
subcategory of `D(X_ét, Λ)`, closed under isomorphisms, which contains the constructible
sheaves placed in degree `0`. -/
lemma prop_of_boundedConstructible {X : Scheme.{u}}
    (P : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F →
      P ((singleFunctor _ 0).obj F))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) : P K := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  have : K.IsGE a := ha
  have : K.IsLE (a + (b - a + 1).toNat - 1) :=
    TStructure.t.isLE_of_le K b _ (by lia)
  exact prop_of_constructibleHomology P hP _ a K inferInstance this hc

variable [Finite Λ]

instance (X : Scheme.{u}) : (Etale.DerivedCategory.constructibleHomology
    (ModuleCat.{u + 1} Λ) X).IsClosedUnderIsomorphisms := by
  rw [Etale.DerivedCategory.constructibleHomology_eq]
  infer_instance

instance (X : Scheme.{u}) :
    (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) X).IsTriangulated := by
  rw [Etale.DerivedCategory.constructibleHomology_eq]
  infer_instance

/-- **Bounded constructible complexes under a direct image satisfying `𝒞`.** If `𝒞(f)` holds,
then `Rf_*` sends a bounded complex with constructible homology sheaves to a complex with
constructible homology sheaves. -/
lemma HasConstructibleDirectImages.constructibleHomology_obj {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : HasConstructibleDirectImages Λ f)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  prop_of_boundedConstructible
    ((Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).inverseImage
      (R((f)_*[ModuleCat.{u + 1} Λ]))) hf hK

omit [Finite Λ] in
/-- **The homology of `Rg_* K` in degree `n` only depends on `τ^{≤ n} K`.** For `K` in
`D^{≥ a}` and `n : ℤ`, the map `Hⁿ(Rg_* τ^{≤ n} K) ⟶ Hⁿ(Rg_* K)` is an isomorphism, because
`Rg_* τ^{> n} K` is concentrated in degrees `> n`. -/
lemma isIso_homologyMap_rightDerivedLowerStar_truncLE {Y S : Scheme.{u}} (g : Y ⟶ S)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    IsIso ((homologyFunctor _ n).map ((R((g)_*[ModuleCat.{u + 1} Λ])).map
      ((TStructure.t.triangleLEGT n).obj K).mor₁)) := by
  let T := (TStructure.t.triangleLEGT n).obj K
  have hT : T ∈ distTriang _ := TStructure.t.triangleLEGT_distinguished n K
  have : T.obj₃.IsGE (n + 1) :=
    (inferInstance : TStructure.t.IsGE ((TStructure.t.truncGT n).obj K) (n + 1))
  have : ((R((g)_*[ModuleCat.{u + 1} Λ])).obj T.obj₃).IsGE (n + 1) :=
    Functor.isGE_rightDerivedFunctor_obj _ _ _
  exact isIso_homologyMap_mor₁ _ ((R((g)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT)
    (n - 1) n (by lia) (isZero_of_isGE _ (n + 1) _ (by lia) (hX := this))
    (isZero_of_isGE _ (n + 1) _ (by lia) (hX := this))

/-- **`Rg_*` of a bounded below complex with constructible homology.** If `𝒞(g)` holds and `K`
is bounded below with constructible homology sheaves, then `Rg_* K` has constructible homology
sheaves: `Hⁿ(Rg_* K) = Hⁿ(Rg_* τ^{≤ n} K)` and `τ^{≤ n} K` is bounded. -/
lemma HasConstructibleDirectImages.constructibleHomology_obj_of_isGE {Y S : Scheme.{u}}
    {g : Y ⟶ S} (hg : HasConstructibleDirectImages Λ g)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (a : ℤ)
    [K.IsGE a] (hK : Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y K) :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((g)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  intro n
  have hb : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((TStructure.t.truncLE n).obj K) := by
    refine ⟨⟨⟨a, ?_⟩, ⟨n, inferInstance⟩⟩, ?_⟩
    · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLE n).obj K) a)
    · rw [Etale.DerivedCategory.constructibleHomology_eq] at hK ⊢
      exact homologyProperty_truncLE hK n
  have : IsConstructibleSheaf ((homologyFunctor _ n).obj
      ((R((g)_*[ModuleCat.{u + 1} Λ])).obj ((TStructure.t.triangleLEGT n).obj K).obj₁)) :=
    hg.constructibleHomology_obj hb n
  have := isIso_homologyMap_rightDerivedLowerStar_truncLE g K n
  exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ n).map
    ((R((g)_*[ModuleCat.{u + 1} Λ])).map ((TStructure.t.triangleLEGT n).obj K).mor₁)))

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Composition for
constructibility alone.

If `𝒞(f)` and `𝒞(g)` hold for composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S`, then `𝒞(f ≫ g)`
holds. Here `Λ` is a finite ring, so that constructible sheaves form a weak Serre class. The
blueprint uses the Grothendieck spectral sequence; we use `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` and
`AlgebraicGeometry.Etale.HasConstructibleDirectImages.constructibleHomology_obj_of_isGE`, since
`Rf_*(F[0])` is concentrated in degrees `≥ 0`. -/
theorem HasConstructibleDirectImages.comp {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    (hf : HasConstructibleDirectImages Λ f) (hg : HasConstructibleDirectImages Λ g) :
    HasConstructibleDirectImages Λ (f ≫ g) := by
  intro F hF
  have : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)).IsGE 0 :=
    Functor.isGE_rightDerivedFunctor_obj_singleFunctor _ F
  have h := hg.constructibleHomology_obj_of_isGE 0 (hf F hF)
  exact (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).prop_of_iso
    ((rightDerivedLowerStarComp _ f g).app _) h
/-- **Approximating a sheaf by a resolution, to finite order.** Suppose every constructible
sheaf `Q` on `X` embeds into a constructible sheaf `G` such that `Rf_*(G[0])` has constructible
homology. Then for every constructible `F` and every `m : ℕ` there are a constructible `Q` and a
morphism `Q[-m] ⟶ F[0]` whose cone `B` has `Rf_* B` with constructible homology. Indeed, if
`Q[-m] ⟶ F[0]` is such a morphism and `0 ⟶ Q ⟶ G ⟶ Q' ⟶ 0` is exact, the cone of the
morphism `Q'[-1] ⟶ Q` of the corresponding triangle is `G`, so the composition
`Q'[-m-1] ⟶ Q[-m] ⟶ F[0]` is again such a morphism (the morphisms whose cone lies in a
triangulated subcategory are stable under composition, by the octahedral axiom). This is the
truncated form of the resolution `0 ⟶ F ⟶ G⁰ ⟶ G¹ ⟶ ⋯` of the blueprint. -/
lemma exists_trW_of_exists_mono {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf Q →
      ∃ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : Q ⟶ G), Mono ι ∧
        IsConstructibleSheaf G ∧ Etale.DerivedCategory.constructibleHomology
          (ModuleCat.{u + 1} Λ) S
            ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj G)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : IsConstructibleSheaf F)
    (m : ℕ) :
    ∃ (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (_ : IsConstructibleSheaf Q)
      (s : ((singleFunctor _ 0).obj Q)⟦(-(m : ℤ))⟧ ⟶ (singleFunctor _ 0).obj F),
      ((Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).inverseImage
        (R((f)_*[ModuleCat.{u + 1} Λ]))).trW s := by
  set P := (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).inverseImage
    (R((f)_*[ModuleCat.{u + 1} Λ]))
  induction m with
  | zero =>
    exact ⟨F, hF, (shiftFunctorZero' _ (-((0 : ℕ) : ℤ)) (by simp)).hom.app _,
      P.trW_of_isIso _⟩
  | succ m ih =>
    obtain ⟨Q, hQ, s, hs⟩ := ih
    obtain ⟨G, ι, _, hG, hGf⟩ := h Q hQ
    let S' := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS' : S'.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    have hQ' : IsConstructibleSheaf (cokernel ι) := IsConstructibleSheaf.cokernel ι
    let T := Triangle.invRotate hS'.singleTriangle
    have hT : T ∈ distTriang _ := inv_rot_of_distTriang _ hS'.singleTriangle_distinguished
    have ha : P.trW T.mor₁ := ObjectProperty.trW.mk _ hT hGf
    let e : ((singleFunctor _ 0).obj (cokernel ι))⟦(-((m + 1 : ℕ) : ℤ))⟧ ≅
        (((singleFunctor _ 0).obj (cokernel ι))⟦(-1 : ℤ)⟧)⟦(-(m : ℤ))⟧ :=
      (shiftFunctorAdd' _ (-1) (-(m : ℤ)) _ (by push_cast; lia)).app _
    refine ⟨cokernel ι, hQ', e.hom ≫ (T.mor₁)⟦(-(m : ℤ))⟧' ≫ s, ?_⟩
    exact P.trW.comp_mem _ _ (P.trW_of_isIso _) (P.trW.comp_mem _ _ (ha.shift _) hs)

/-- **Constructibility from embeddings into good sheaves.** Suppose every constructible sheaf
`Q` on `X` embeds into a constructible sheaf `G` such that all `Rᵠf_* G` are constructible.
Then `𝒞(f)` holds. This is the resolution argument of the blueprint proofs of
`proposition-proper-direct-image-finite-coefficients` and
`proposition-proper-direct-image-finite-coefficients`: for a given degree `n`, `Rⁿf_* F` agrees with
`Hⁿ(Rf_* B)` for the cone `B` of a morphism `Q[-n-2] ⟶ F[0]` given by
`AlgebraicGeometry.Etale.exists_trW_of_exists_mono`, because `Rf_*(Q[-n-2])` is concentrated in
degrees `≥ n + 2`. -/
theorem hasConstructibleDirectImages_of_exists_mono {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf Q →
      ∃ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : Q ⟶ G), Mono ι ∧
        IsConstructibleSheaf G ∧ Etale.DerivedCategory.constructibleHomology
          (ModuleCat.{u + 1} Λ) S
            ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj G))) :
    HasConstructibleDirectImages Λ f := by
  intro F hF n
  have : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)).IsGE 0 :=
    Functor.isGE_rightDerivedFunctor_obj_singleFunctor _ F
  by_cases hn : n < 0
  · exact IsConstructibleSheaf.of_isZero (isZero_of_isGE _ 0 _ hn)
  obtain ⟨Q, -, s, Z, g, k, hT, hZ⟩ := exists_trW_of_exists_mono f h F hF (n.toNat + 2)
  have : (((singleFunctor _ 0).obj Q)⟦(-((n.toNat + 2 : ℕ) : ℤ))⟧).IsGE (n + 2) :=
    TStructure.t.isGE_shift _ 0 _ _ (by lia)
  have : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
      (((singleFunctor _ 0).obj Q)⟦(-((n.toNat + 2 : ℕ) : ℤ))⟧)).IsGE (n + 2) :=
    Functor.isGE_rightDerivedFunctor_obj _ _ _
  have hT' := (R((f)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT
  have hiso : IsIso ((homologyFunctor _ n).map ((R((f)_*[ModuleCat.{u + 1} Λ])).map g)) :=
    isIso_homologyMap_mor₂ _ hT' n (n + 1) rfl
      (isZero_of_isGE _ (n + 2) _ (by lia) (hX := this))
      (isZero_of_isGE _ (n + 2) _ (by lia) (hX := this))
  have : IsConstructibleSheaf ((homologyFunctor _ n).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj Z)) := hZ n
  exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ n).map
    ((R((f)_*[ModuleCat.{u + 1} Λ])).map g))).symm

end Etale

end AlgebraicGeometry
