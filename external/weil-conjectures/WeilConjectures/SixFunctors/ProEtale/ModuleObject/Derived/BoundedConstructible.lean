/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.Compactification.Over
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FieldCoefficientTensorHypotheses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseHypotheses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!

# The six functors on bounded constructible module objects over `Λ`

Let `Λ` be a commutative condensed ring. For a scheme `X`, the bounded constructible derived
category `D_cons(X_proét, Λ_X)` of module objects over the coefficient ring object
`Λ_X = p_X^* Λ` is the full subcategory
`ProEtale.BoundedConstructible (condensedRingObj Λ X)` of `D(Mod_{Λ_X})`
(`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`), with scoped notation
`Dᵇc(X)⟦Λ⟧`. This file restricts the six functors on `D(Mod_{Λ_X})` of the folder
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived` to these full subcategories.

## The setting

Following Bhatt–Scholze, Section 6.8, in the simplified setting of schemes over a field: fix a
prime `ℓ` and a field `k` of characteristic `p > 0` with `p ≠ ℓ`
(`[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`). All schemes are separated and of finite
type over `Spec k`: they are objects `X : Over (Spec (.of k))` of the category of schemes over
`Spec k`, with structure morphism `X.hom` locally of finite type, quasi-compact and separated.
All morphisms are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`, and the functors are those of
the underlying morphism of schemes `f.left`. In the documentation, `X` also stands for the
underlying scheme `X.left`, so that for instance `Dᵇc(X)⟦Λ⟧` is `Dᵇc(X.left)⟦Λ⟧` in the code.
No further hypothesis is imposed on the schemes or morphisms. In particular every such morphism
has a compactification, by Nagata's theorem (`AlgebraicGeometry.HasCompactification.of_over`),
with the choice `compactificationOverField f`. A compactification
`c = (X.left ⟶[i] Z ⟶[p] Y.left)` of `f.left` is a factorization in `Over (Spec (.of k))`,
through the object `c.overObj` and the morphisms `c.overI` and `c.overG` of
`WeilConjectures.Compactification.Over`.

| functor | restriction |
| --- | --- |
| `Lf^* = L((f)^*⟦Λ⟧)` | `boundedConstructibleUpperStar` |
| `j_! = D((j)_!open⟦Λ⟧)`, `j` an open immersion | `boundedConstructibleOpenImmersionLowerShriek` |
| `- ⊗ᴸ -` | `boundedConstructibleTensor` (`ℓ`-adic `Λ`) |
| `RHom(-, -)` | `boundedConstructibleHom` (`ℓ`-adic `Λ`) |

The pullback, the pushforward and the extension by zero are the `ObjectProperty.lift` of the
composite of the inclusion with the functor on the ambient derived category, so they are
compatible with the inclusions by construction (`ObjectProperty.liftCompιIso`). The derived
tensor product and the derived hom are instead the monoidal closed structure of the full
subcategory `Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalSubcategory`,
`ObjectProperty.fullMonoidalClosedSubcategory`), given by the instances
`isMonoidal_boundedConstructible` and `isMonoidalClosed_boundedConstructible`; they are again
compatible with the inclusions, the inclusion being strict monoidal (`ObjectProperty.monoidalι`).
The restricted pullback `Lf^*` is strong monoidal, with the comparison isomorphisms of the
strong monoidal derived pullback `ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`
(`monoidal_boundedConstructibleUpperStar`, by `ObjectProperty.monoidalLift`).

The derived pushforward `Rf_* = R((f)_*⟦Λ⟧)` (`boundedConstructibleLowerStar`, `ℓ`-adic `Λ`),
the adjunction `Lf^* ⊣ Rf_*` and the derived lower shriek are in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar`: that
`Rf_*` preserves bounded constructible complexes is proved from the finiteness of the direct image
of a constructible sheaf, whose proof imports
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`, an importer of this file.
The derived lower shriek is not a restriction: it is assembled on bounded constructible
complexes out of the functors above. For a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`,
`Rf_!^c := i_! ⋙ Rp_*` (`boundedConstructibleLowerShriekOfCompactification`), and `Rf_!` is
`Rf_!^c` for the chosen compactification `compactificationOverField f`
(`boundedConstructibleLowerShriek`). Both are compatible with the derived lower shrieks
`Rf_!(c)⟦Λ⟧` and `R(f)_!⟦Λ⟧` on the ambient derived categories
(`boundedConstructibleLowerShriekOfCompactificationCompatibility`,
`boundedConstructibleLowerShriekCompatibility`).

The adjunctions `Lf^* ⊣ Rf_*` (in `BoundedConstructibleLowerStar`) and `j_! ⊣ j^*` restrict
along the fully faithful inclusions (`Adjunction.restrictFullyFaithful`), and so does the
composition isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`boundedConstructibleUpperStarComp`). Its conjugates under these
adjunctions are the composition isomorphisms `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`
(`boundedConstructibleLowerStarComp`) and `(j ≫ j')_! ≅ j_! ⋙ j'_!` for open immersions
(`boundedConstructibleOpenImmersionLowerShriekComp`). The adjunction
`- ⊗ᴸ - ⊣₂ RHom(-, -)` is the tensor-hom adjunction of the monoidal closed category
`Dᵇc(X)⟦Λ⟧` (`boundedConstructibleTensorHomAdjunction₂`).

The exceptional inverse image `Rf^!` is not the restriction of a functor on the ambient derived
category: it is constructed on bounded constructible complexes directly, for the `ℓ`-adic
coefficient rings, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.

## Finiteness

The pullback and the extension by zero preserve bounded constructible complexes
(`boundedConstructible_leftDerivedUpperStar_obj_of_scheme`,
`boundedConstructible_openImmersionLowerShriek_obj`). So does the derived pushforward
(`boundedConstructible_rightDerivedLowerStar_obj`, proved in `BoundedConstructibleLowerStar`).
The theorem `isMonoidal_boundedConstructible` (`Dᵇc(X)⟦Λ⟧` contains `Λ_X` and is stable under
`- ⊗ᴸ -`), used as an instance, is proved by noetherian induction from the lisse case
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj`). The
monoidal closed structure (`isMonoidalClosed_boundedConstructible`, `boundedConstructibleHom` and
the tensor-hom adjunctions) uses `boundedConstructible_rightDerivedLowerStar_obj` and is in
`BoundedConstructibleLowerStar`.

The pullback and the extension by zero preserve bounded constructible complexes for every `Λ`,
and are defined for a general condensed ring `Λ`. The other three statements are false for a
general `Λ`: for the constant discrete ring `𝔽_p` and the affine line over an algebraically
closed field of characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`,
which is infinite; for `Λ = ℤ/4` on a geometric point of characteristic `3`, `Tor_i` and
`Ext^i` of `ℤ/2` over `ℤ/4` are `ℤ/2` in every degree `i ≥ 0`. They are theorems for the
`ℓ`-adic coefficients with `ℓ` invertible in `k` (Deligne's finiteness theorems, SGA 4½
[Th. finitude]; Bhatt–Scholze, Section 6.8).

## The `ℓ`-adic coefficient rings

The pushforward, the lower shriek, the derived tensor product and the derived hom on bounded
constructible complexes, and the statements above, are made for each of the three `ℓ`-adic
coefficient rings separately, with the same declaration names:

* `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`, in the namespace `ProEtale.CondensedRing`
  (`boundedConstructibleLowerStar ℓ f`);
* `E̲ = Profinite.continuousMapRingObj E` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
  (`E : PadicAlgCl.FiniteIntermediateField ℓ`, with category `Dᵇc(X)⟦E̲⟧`),
  in the namespace `ProEtale.CondensedRing.ContinuousMapRingObj`
  (`ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E f`);
* `𝒪̲_E = Profinite.padicIntegersRingObj ℓ E` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, in
  the namespace `ProEtale.CondensedRing.PadicIntegersRingObj`
  (`PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E f`).

The pullback and the extension by zero are stated once, for a general `Λ`.

-/

-- The `privateModule` linter alone takes about 20 s on this file.
set_option linter.privateModule false

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The pullback and the pushforward -/

section UpperLowerStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

set_option linter.unusedSectionVars false in
/-- The derived pullback `Lf^*` on module objects over `Λ` preserves bounded constructible
complexes (SGA 4 XVII, 5.1.16; Bhatt–Scholze, Section 6.8). -/
lemma boundedConstructible_leftDerivedUpperStar_obj (K : Dᵇc(Y.left)⟦Λ⟧) :
    boundedConstructible (condensedRingObj Λ X.left) ((L((f.left)^*⟦Λ⟧)).obj K.obj) :=
  boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ f.left K.obj K.property

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes:
the restriction of `L((f)^*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K

/-- The restricted derived pullback is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperStarCompatibility :
    boundedConstructibleUpperStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes:
the restriction of `ProEtale.CondensedRing.leftDerivedUpperStarComp` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleUpperStar Λ ℓ (f ≫ g) ≅
      boundedConstructibleUpperStar Λ ℓ g ⋙ boundedConstructibleUpperStar Λ ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ ℓ (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp Λ f.left g.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ g).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

end UpperLowerStar

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

include ℓ k

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

-- The section variables are kept, as for all functors on `Dᵇc(-)⟦Λ⟧`, so that the restricted
-- functor `boundedConstructibleOpenImmersionLowerShriek` has the same arguments as the others.
set_option linter.unusedSectionVars false in
/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `Λ`, preserves bounded constructible complexes (SGA 4 XVII, 5.1.16;
Bhatt–Scholze, Section 6.8): `j_!` is exact, so it commutes with the cohomology sheaves, and it
preserves zero objects and constructible module objects
(`ProEtale.CondensedRing.isConstructibleModuleObject_openImmersionLowerShriek_obj`). -/
lemma boundedConstructible_openImmersionLowerShriek_obj (K : Dᵇc(U.left)⟦Λ⟧) :
    boundedConstructible (condensedRingObj Λ X.left) ((D((j.left)_!open⟦Λ⟧)).obj K.obj) := by
  have : TopologicalSpace.NoetherianSpace X.left := by
    have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    have : IsNoetherian X.left := {}
    infer_instance
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ K.obj).1 K.property
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact ((j.left)_!open⟦Λ⟧.map_isZero (hab i hi)).of_iso
      ((Functor.mapDerivedCategoryHomologyFunctorIso _ i).app K.obj).symm
  · exact (isConstructibleModuleObject_openImmersionLowerShriek_obj Λ j.left _ (hc n)).of_iso
      ((Functor.mapDerivedCategoryHomologyFunctorIso _ n).app K.obj)

/-- The extension by zero `j_! : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor
`D((j)_!open⟦Λ⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek : Dᵇc(U.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j K

/-- The restricted extension by zero is compatible with the inclusions. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekCompatibility :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `j_! ⊣ j^*` along an open immersion on bounded constructible complexes: the
restriction of `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`
along the fully faithful inclusions, the levelwise `D((j)^*⟦Λ⟧)` being identified with the
derived pullback `L((j)^*⟦Λ⟧)` that `boundedConstructibleUpperStar` restricts. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⊣ boundedConstructibleUpperStar Λ ℓ j :=
  Adjunction.restrictFullyFaithful
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ j).symm

/-- The extension by zero `j_!` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleUpperStar`. -/
instance isLeftAdjoint_boundedConstructibleOpenImmersionLowerShriek :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).IsLeftAdjoint :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).isLeftAdjoint

/-- The derived pullback `j^*` along an open immersion on bounded constructible complexes is a
right adjoint, its left adjoint being `boundedConstructibleOpenImmersionLowerShriek`. -/
instance isRightAdjoint_boundedConstructibleUpperStar_of_isOpenImmersion :
    (boundedConstructibleUpperStar Λ ℓ j).IsRightAdjoint :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).isRightAdjoint

/-- The composition isomorphism `(j ≫ j')_! ≅ j_! ⋙ j'_!` of the extensions by zero along open
immersions on bounded constructible complexes: the conjugate of
`boundedConstructibleUpperStarComp` under the adjunctions `(j ≫ j')_! ⊣ L(j ≫ j')^*` and
`j_! ⋙ j'_! ⊣ Lj'^* ⋙ Lj^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekComp {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] (j' : X ⟶ V)
    [IsOpenImmersion j'.left] [IsOpenImmersion (j ≫ j').left] :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ (j ≫ j') ≅
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' :=
  ((conjugateIsoEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ (j ≫ j'))
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).comp
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j'))).symm
    (boundedConstructibleUpperStarComp Λ ℓ j j')).symm

end OpenImmersion

/-! ### The compactification chosen by Nagata's theorem -/

/-- The compactification of the underlying morphism of schemes `f.left` of a morphism `f` of
separated `k`-schemes of finite type chosen by Nagata's theorem
(`AlgebraicGeometry.HasCompactification.of_over`): the compactification
`HasCompactification.compactification f.left` for the instance it provides. It is the
compactification defining `boundedConstructibleLowerShriek`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar`). -/
noncomputable abbrev compactificationOverField {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) : Compactification f.left :=
  haveI := HasCompactification.of_over f
  HasCompactification.compactification f.left


/-! ### The derived tensor product and the derived hom -/

section TensorHom

include ℓ k

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance keeps only the section variables its statement and proof mention, so its
-- hypotheses are restated as binders; they repeat section variables.
omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
-- the statement keeps the hypothesis `ℓ ≠ char k` of the setting, unused by the proof
set_option linter.unusedSectionVars false in
set_option linter.overlappingInstances false in
/-- Blueprint `proposition-six-operations-dctf--14`: the bounded constructible complexes of
`ℚ̄_ℓ`-sheaves form a monoidal subcategory of
`D(Mod_{ℚ̄_ℓ,X})` for the derived tensor product: they contain the unit
`ℚ̄_ℓ,X` and are stable under `- ⊗ᴸ -` (SGA 4½ [Th. finitude], 1.6; Bhatt–Scholze, Section 6.8). It
is false for a general condensed ring: for `Λ = ℤ/4` on a geometric point of characteristic `3`,
`Tor_i^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
theorem isMonoidal_boundedConstructible :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).IsMonoidal :=
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  { prop_unit := boundedConstructible_tensorUnit _ X.left
    prop_tensor _ _ hK hL :=
      boundedConstructible_tensorObj
        (tensorHypotheses_padicAlgClRingObj ℓ).lisseTensorHypotheses hK hL }
set_option linter.overlappingInstances false in
attribute [instance] isMonoidal_boundedConstructible

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the
full subcategory `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of
`-⊗ᴸ-(X)⟦ℚ̲̄_ℓ⟧` in both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  curriedTensor _

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleTensor ℓ X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

end TensorHom

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section TensorHom

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance keeps only the section variables its statement and proof mention, so its
-- hypotheses are restated as binders; they repeat section variables.
omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
-- the statement keeps the hypothesis `ℓ ≠ char k` of the setting, unused by the proof
set_option linter.unusedSectionVars false in
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `E`-sheaves form a monoidal subcategory of
`D(Mod_{E_X})` for the derived tensor product: they contain the unit `E_X` and are
stable under `- ⊗ᴸ -` (SGA 4½ [Th. finitude], 1.6; Bhatt–Scholze, Section 6.8). It is false for a
general condensed ring: for `Λ = ℤ/4` on a geometric point of characteristic `3`,
`Tor_i^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
theorem isMonoidal_boundedConstructible :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)).IsMonoidal :=
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  { prop_unit := boundedConstructible_tensorUnit _ X.left
    prop_tensor _ _ hK hL :=
      boundedConstructible_tensorObj
        (tensorHypotheses_continuousMapRingObj ℓ E).lisseTensorHypotheses hK hL }
set_option linter.overlappingInstances false in
attribute [instance] isMonoidal_boundedConstructible

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the full
subcategory `Dᵇc(X)⟦E̲⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of
`-⊗ᴸ-(X)⟦E̲⟧` in both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤
      Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ :=
  curriedTensor _

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦E̲⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Profinite.continuousMapRingObj E⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

end TensorHom

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section TensorHom

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance keeps only the section variables its statement and proof mention, so its
-- hypotheses are restated as binders; they repeat section variables.
omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
-- the statement keeps the hypothesis `ℓ ≠ char k` of the setting, unused by the proof
set_option linter.unusedSectionVars false in
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `𝒪_E`-sheaves form a monoidal subcategory of
`D(Mod_{𝒪_{E,X}})` for the derived tensor product: they contain the unit
`𝒪_{E,X}` and are stable under `- ⊗ᴸ -` (SGA 4½ [Th. finitude], 1.6; Bhatt–Scholze, Section 6.8). It
is false for a general condensed ring: for `Λ = ℤ/4` on a geometric point of characteristic `3`,
`Tor_i^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
theorem isMonoidal_boundedConstructible :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)).IsMonoidal :=
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  { prop_unit := boundedConstructible_tensorUnit _ X.left
    prop_tensor _ _ hK hL :=
      boundedConstructible_tensorObj (lisseHypotheses ℓ E).toLisseTensorHypotheses hK hL }
set_option linter.overlappingInstances false in
attribute [instance] isMonoidal_boundedConstructible

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the
full subcategory `Dᵇc(X)⟦𝒪̲_E⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of
`-⊗ᴸ-(X)⟦𝒪̲_E⟧` in both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  curriedTensor _

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦𝒪̲_E⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

end TensorHom

end PadicIntegersRingObj

section MonoidalUpperStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded constructible complexes
is strong monoidal, with the comparison isomorphisms of `L((f)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

end MonoidalUpperStar

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section MonoidalUpperStar

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧` on bounded constructible complexes
is strong monoidal, with the comparison isomorphisms of `L((f)^*⟦E̲⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

end MonoidalUpperStar

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section MonoidalUpperStar

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` on bounded constructible complexes
is strong monoidal, with the comparison isomorphisms of `L((f)^*⟦𝒪̲_E⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

end MonoidalUpperStar

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
