/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom

/-!
# The typing rule: the operations on `Dctf` are restrictions of the ambient ones

Every operation of the six-functor formalism is defined on the ambient derived categories
`D(X_ét, Λ)`; the functors between the small categories `Dctf(X, Λ)` are *restrictions* of the
ambient ones, and that the restriction exists is a theorem (blueprint
`proposition-six-operations-dctf`). This file

* proves the general fact behind the typing rule: a functor into an ambient category restricts
  to a full subcategory (closed under isomorphisms) exactly when it carries every object into
  it, and the restriction is unique up to isomorphism
  (`CategoryTheory.ObjectProperty.exists_comp_ι_iso_iff`,
  `CategoryTheory.ObjectProperty.isoLiftOfCompιIso`);
* restricts the tensor-hom adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` to `Dctf(X, Λ)`
  (`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.tensorHomAdjunction`), the restricted
  bifunctors of clause (ii) of `proposition-six-operations-dctf` being
  `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.derivedTensor` and
  `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.derivedHom`;
* proves the part of clause (vi) of `proposition-six-operations-dctf` that concerns the restricted
  functor: `𝔻_X 𝔻_X K ≅ K` in `Dctf(X, Λ)`, and `𝔻_X : Dctf(X, Λ)ᵒᵖ ⥤ Dctf(X, Λ)` is an
  equivalence;
* states the typing rule: each restricted functor, followed by the inclusion, is the inclusion
  followed by the ambient operation (`AlgebraicGeometry.Etale.typingRule`).

## Implementation notes

The comparison isomorphisms are all built from `CategoryTheory.ObjectProperty.liftCompιIso` and
`CategoryTheory.ObjectProperty.liftFullSubcategoryCompιIso`, which are identities on the nose;
no `rfl` through the derived tensor product or internal hom is needed, which would make the
kernel unfold them.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.ObjectProperty

variable {D E : Type*} [Category* D] [Category* E] (Q : ObjectProperty D)

/-- **Restrictions to a full subcategory are unique.** If `G : E ⥤ Q.FullSubcategory` followed
by the inclusion is isomorphic to `F`, then `G` is isomorphic to the lift of `F`, the inclusion
being fully faithful. -/
noncomputable def isoLiftOfCompιIso {F : E ⥤ D} (hF : ∀ X, Q (F.obj X))
    (G : E ⥤ Q.FullSubcategory) (e : G ⋙ Q.ι ≅ F) : G ≅ Q.lift F hF :=
  (Q.fullyFaithfulι.whiskeringRight E).preimageIso (e ≪≫ (Q.liftCompιIso F hF).symm)

/-- **A functor restricts to a full subcategory iff it carries every object into it.** For `Q`
closed under isomorphisms, `F : E ⥤ D` is isomorphic to a functor `G : E ⥤ Q.FullSubcategory`
followed by the inclusion exactly when every `F.obj X` satisfies `Q`. -/
lemma exists_comp_ι_iso_iff [Q.IsClosedUnderIsomorphisms] (F : E ⥤ D) :
    (∃ G : E ⥤ Q.FullSubcategory, Nonempty (G ⋙ Q.ι ≅ F)) ↔ ∀ X, Q (F.obj X) :=
  ⟨fun ⟨G, ⟨e⟩⟩ X ↦ Q.prop_of_iso (e.app X) (G.obj X).property,
    fun h ↦ ⟨Q.lift F h, ⟨Q.liftCompιIso F h⟩⟩⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-! ### Clause (ii): the restricted tensor-hom adjunction -/

section Bifunctors

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ X]

/-- The tensor-hom adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` restricts to the small category
`Dctf(X, Λ)`, with the unit and counit of
`AlgebraicGeometry.Etale.derivedTensorHomAdjunction`. -/
noncomputable def DerivedCategoryFiniteTor.tensorHomAdjunction
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    (DerivedCategoryFiniteTor.derivedTensor Λ X).obj K ⊣
      (DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K) :=
  (derivedTensorHomAdjunction _ K.obj).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _
      fun _ hM ↦ constructibleFiniteTor_tensor Λ X K.property hM).symm
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _
      fun _ hM ↦ constructibleFiniteTor_derivedHom Λ aX K.property hM).symm

end Bifunctors

/-! ### Clause (vi): the restricted Verdier dual -/

section VerdierDual

variable {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasCompactification aX]

/-- Blueprint `proposition-six-operations-dctf`, clause (vi): for `X` separated of finite type over
an algebraically closed field `k` and a finite `Λ` whose exponent is invertible on `k`, every
object `K` of the small category `Dctf(X, Λ)` is isomorphic, inside `Dctf(X, Λ)`, to its double
Verdier dual `𝔻_X 𝔻_X K`, the Verdier dual being restricted to `Dctf(X, Λ)` by
`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`. -/
theorem DerivedCategoryFiniteTor.nonempty_iso_verdierDual_verdierDual
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    Nonempty (K ≅ (DerivedCategoryFiniteTor.verdierDual _ aX
      fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK).obj
        (op ((DerivedCategoryFiniteTor.verdierDual _ aX
          fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK).obj (op K)))) :=
  ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    (Etale.nonempty_iso_verdierDual_verdierDual Λ aX K.property).some⟩

/-- The anti-equivalence `AlgebraicGeometry.Etale.verdierDualEquivalence` has the restricted
Verdier dual `DerivedCategoryFiniteTor.verdierDual` as its functor. -/
noncomputable def DerivedCategoryFiniteTor.verdierDualEquivalenceFunctorIso :
    (verdierDualEquivalence Λ aX).functor ≅ DerivedCategoryFiniteTor.verdierDual _ aX
      fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK :=
  ObjectProperty.isoLiftOfCompιIso _ _ _ (ObjectProperty.liftCompιIso _ _ _)

/-- Blueprint `proposition-six-operations-dctf`, clause (vi): the restricted Verdier dual
`𝔻_X : Dctf(X, Λ)ᵒᵖ ⥤ Dctf(X, Λ)` is an equivalence, i.e. `𝔻_X` is a contravariant
anti-equivalence of `Dctf(X, Λ)` (`AlgebraicGeometry.Etale.verdierDualEquivalence`). -/
theorem DerivedCategoryFiniteTor.isEquivalence_verdierDual :
    (DerivedCategoryFiniteTor.verdierDual Λ aX
      fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK).IsEquivalence :=
  Functor.isEquivalence_of_iso (DerivedCategoryFiniteTor.verdierDualEquivalenceFunctorIso Λ aX)

end VerdierDual

/-! ### The typing rule -/

section TypingRule

variable {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aX] [HasCompactification aX] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsSeparated f] [QuasiCompact f]
  [HasCompactification f]

/-- Blueprint `proposition-six-operations-dctf`: The typing rule of this section.

Every operation is defined on the ambient derived categories `D(-_ét, Λ)`, and its version on
the small categories `Dctf(-, Λ)` is its restriction: for an algebraically closed field `k`, a
finite `Λ` whose exponent is invertible on `k` and a separated morphism `f : X ⟶ Y` of schemes
of finite type over `k`,
with `X` separated over `k`, each of the functors `Lf^*`, `Rf_*`, `Rf_!`, `Rf^!`, `𝔻_X`,
`K ⊗ᴸ -` and `RHom(K, -)` (for `K ∈ Dctf(X, Λ)`) between the small categories, followed by the
inclusion, is isomorphic to the inclusion followed by the ambient operation. By
`CategoryTheory.ObjectProperty.isoLiftOfCompιIso` a functor between the small categories with
this property is unique up to isomorphism, and by
`CategoryTheory.ObjectProperty.exists_comp_ι_iso_iff` its existence is equivalent to the
preservation statements of `proposition-six-operations-dctf`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_stability`). -/
theorem typingRule (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    Nonempty (DerivedCategoryFiniteTor.leftDerivedUpperStar (ModuleCat.{u + 1} Λ) f ⋙
        DerivedCategoryFiniteTor.ι _ X ≅
      DerivedCategoryFiniteTor.ι _ Y ⋙ L((f)^*[ModuleCat.{u + 1} Λ])) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerStar Λ aX aY f hf ⋙
        DerivedCategoryFiniteTor.ι _ Y ≅
      DerivedCategoryFiniteTor.ι _ X ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⋙
        DerivedCategoryFiniteTor.ι _ Y ≅
      DerivedCategoryFiniteTor.ι _ X ⋙ R(f)_![ModuleCat.{u + 1} Λ]) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f ⋙
        DerivedCategoryFiniteTor.ι _ X ≅
      DerivedCategoryFiniteTor.ι _ Y ⋙ R(f)^![Λ]) ∧
    Nonempty (DerivedCategoryFiniteTor.verdierDual Λ aX
          (fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK) ⋙
        DerivedCategoryFiniteTor.ι _ X ≅
      (DerivedCategoryFiniteTor.ι _ X).op ⋙ verdierDual Λ aX) ∧
    Nonempty ((DerivedCategoryFiniteTor.derivedTensor Λ X).obj K ⋙
        DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ≅
      DerivedCategoryFiniteTor.ι _ X ⋙ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K.obj) ∧
    Nonempty ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K) ⋙
        DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ≅
      DerivedCategoryFiniteTor.ι _ X ⋙ (RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K.obj)) :=
  ⟨⟨ObjectProperty.liftCompιIso _ _ _⟩, ⟨ObjectProperty.liftCompιIso _ _ _⟩,
    ⟨ObjectProperty.liftCompιIso _ _ _⟩, ⟨ObjectProperty.liftCompιIso _ _ _⟩,
    ⟨ObjectProperty.liftCompιIso _ _ _⟩,
    ⟨ObjectProperty.liftFullSubcategoryCompιIso _ _ _
      fun _ hM ↦ constructibleFiniteTor_tensor Λ X K.property hM⟩,
    ⟨ObjectProperty.liftFullSubcategoryCompιIso _ _ _
      fun _ hM ↦ constructibleFiniteTor_derivedHom Λ aX K.property hM⟩⟩

end TypingRule

/-! ### The typing table -/

section TypingTable

variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
  (f : X ⟶ Y) (hf : f ≫ aY = aX)

include hf

/-- Blueprint `proposition-six-operations-dctf`: Typing table: ambient definition, small-category
theorem.

Let `Λ` be a finite ring whose exponent is invertible on an algebraically closed field `k`, and
`f : X ⟶ Y` a separated morphism of schemes of finite type over `k`, with `X` separated over
`k`. Each row of the table is a theorem:

* `Lf^*` maps `Dᵇc(Y) ⥤ Dᵇc(X)` and `Dctf(Y) ⥤ Dctf(X)`, preserving Tor amplitude `[a, b]`;
* `- ⊗ᴸ -` maps `Dᵇc × Dctf ⥤ Dᵇc` and `Dctf × Dctf ⥤ Dctf`, with `[a, b] + [c, d] ↦
  [a + c, b + d]`;
* `RHom(-, -)` maps `Dctf × Dctf ⥤ Dctf` for two arbitrary objects, with
  `[a, b], [c, d] ↦ [c - b - 2m, d - a + 2m]` if `dim X ≤ m`, and `[c - b, d - a]` for a
  site-perfect (dualizable) first argument;
* `Rf_*` maps `Dᵇc(X) ⥤ Dᵇc(Y)` and `Dctf(X) ⥤ Dctf(Y)`, and on the pro-étale site
  `[a, b] ↦ [a, b + 2 dim X]`;
* `Rf_!` maps `Dᵇc(X) ⥤ Dᵇc(Y)` and `Dctf(X) ⥤ Dctf(Y)`;
* `Rf^!` maps `Dctf(Y) ⥤ Dctf(X)` for every such `f`, shifting `D_c^[a, b]` (with Tor amplitude
  `[a, b]`) to `[a - 2d, b - 2d]` for `g` smooth of pure relative dimension `d`, to
  `[a, b + 2d + 1]` for a closed immersion `i` into a target of dimension `≤ d`, and to
  `[a - 2D, b + 2 dim Y + 1]` in general;
* `𝔻_X` maps `Dctf(X) ⥤ Dctf(X)` with `K ≅ 𝔻_X 𝔻_X K`, an anti-equivalence, and
  `[a, b] ↦ [-b - 2d, -a]` if `dim X ≤ d`.

The row `Rf^×` asserts nothing: it is an ambient functor used nowhere. The statement collects
`AlgebraicGeometry.Etale.boundedConstructible_preservation`,
`AlgebraicGeometry.Etale.constructibleFiniteTor_preservation`,
`AlgebraicGeometry.Etale.torAmplitudeIn_preservation`,
`AlgebraicGeometry.Etale.boundedConstructible_tensor` and the two shift estimates of
`theorem-f-shriek-finite-coefficients`. -/
theorem sixOperations_typing [QuasiCompact f] [HasCompactification f]
    [IsSeparated aX] [HasCompactification aX] [IsAlgClosed k] :
    ((∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
        boundedConstructible (ModuleCat.{u + 1} Λ) X
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K))) ∧
    ((∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((R(f)^![Λ]).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((verdierDual Λ aX).obj (op K)))) ∧
    ((∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a + c) (b + d)
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))),
      ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
              ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) ∧
            ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
              ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K)) ∧
    (∀ m : ℕ, topologicalKrullDim X ≤ (m : WithBot ℕ∞) → ∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K → IsDualizable K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∃ D : ℕ, ∀ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * d + 1)
          ((R(f)^![Λ]).obj K)) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * (d : ℤ)) (-a)
            ((verdierDual Λ aX).obj (op K))) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            ((verdierDual Λ aX).obj (op K)) ∧
          Nonempty (K ≅ (verdierDual Λ aX).obj
            (op ((verdierDual Λ aX).obj (op K)))))) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          boundedConstructible (ModuleCat.{u + 1} Λ) X
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ {X' : Scheme.{u}} (g : X' ⟶ Y) [HasCompactification g] (d : ℕ)
      [SmoothOfRelativeDimension d g] (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X' (a - 2 * d) (b - 2 * d)
          ((R(g)^![Λ]).obj K)) ∧
    (∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i] (d : ℕ),
      topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + 2 * d + 1)
          ((R(i)^![Λ]).obj K)) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  have : HasInvertibleExponent Λ Y := .of_hom aY
  refine ⟨boundedConstructible_preservation Λ aX aY f hf,
    constructibleFiniteTor_preservation Λ aX aY f hf,
    torAmplitudeIn_preservation Λ aX aY f hf,
    fun K M hK hM ↦ boundedConstructible_tensor Λ X hK hM.1 hM.2,
    fun g _ d _ a b K hK ↦
      constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension Λ g d a b hK,
    fun i _ _ d hd a b K hK ↦
      constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion Λ aX i d hd a b hK⟩

end TypingTable

end Etale

end AlgebraicGeometry
