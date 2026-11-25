/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SmoothPurity.OrientationCanonical
public import WeilConjectures.SmoothPurity.SmoothImageFactor
public import WeilConjectures.SmoothPurity.TateTwistBoundedConstructible
public import WeilConjectures.SmoothPurity.UpperShriekUnitOpenImmersionComp

/-!

# Smooth purity for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
objects `X : Over (Spec (.of k))`, separated and of finite type over `Spec k`, and all morphisms
are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`; in particular `ℓ` is invertible on every
scheme considered. In the documentation, `X` also stands for the underlying scheme `X.left`.

Let `f : X ⟶ Y` be a morphism whose underlying morphism of schemes `f.left` is smooth of pure
relative dimension `d`. *Smooth purity* (SGA 4, Exposé XVIII, Théorème 3.2.5, and Bhatt–Scholze,
*The pro-étale topology for schemes*, Section 6.8, for `ℚ̄_ℓ`-coefficients) identifies the
exceptional inverse image of the constant coefficient object with a shifted Tate twist:
```
pur_f : Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]
```
in the derived category `D(Mod_{ℚ̄_ℓ,X})` of module objects over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`, the
pullback of the condensed ring `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`). Here `Rf^!` is
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriek` on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (the right adjoint of `Rf_!`, built from the
compactification of `f` chosen by Nagata's theorem), `ℚ̄_ℓ,Y` is the tensor unit of the
monoidal category `Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible`), whose underlying
complex is the tensor unit of `D(Mod_{ℚ̄_ℓ,Y})`, and `ℚ̄_ℓ,X(d)` is the Tate twist of
`WeilConjectures.TateTwist.ProEtale`. The isomorphism is stated after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`, which is fully faithful, so that the constructibility of the Tate
twists need not be recorded.

## The orientation and its normalizations

The orientation `γ_f : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation`, the datum the trace map is built
from) is a
`@[no_expose]` definition. Up to the normalization along open immersions described below, it is the
canonical orientation (`AlgebraicGeometry.ProEtale.CondensedRing.IsCanonicalSmoothOrientation`): the
extension of scalars to `ℚ̄_ℓ` of the integral morphism `ℤ_ℓ,X(d)[2d] ⟶ Rf^! ℤ_ℓ,Y` lifting the
finite orientations `Rf^! Λ_Y ≅ Λ_X(d)[2d]`, `Λ = ℤ ⧸ ℓⁿ`, of the diagonal argument
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`), when an isomorphism with this property
is known to exist. The lift always exists mathematically (SGA 4, Exposé XVIII: the finite
orientations are compatible under change of coefficients) and is unique, but its existence is not
formalized; when it is not available, `γ_f` is a non-canonical isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.nonempty_iso_tateTwist_upperShriekUnit`). In all cases
`γ_f` is an isomorphism (`AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothOrientation`). The
trace map `Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of SGA 4, Exposé XVIII
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace`) is the composite of `Rf_! γ_f`
and the counit of `Rf_! ⊣ Rf^!`. The purity map `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityMap`) is `γ_f` itself; it is an
isomorphism (`AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap`, smooth purity
proper), and it is the adjoint of the trace map for `Rf_! ⊣ Rf^!`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityMap_eq_homEquiv_smoothTrace`). The purity
isomorphism `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` is the inverse of the
purity map. For an open immersion `j` in relative dimension zero the purity isomorphism is the
canonical identification `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion`).

The orientation is normalized along open immersions of the target (compatibility of purity with
composition with an open immersion): `f` factors as a surjective smooth morphism
`g : X ⟶ U` followed by the open immersion of its image, and the factorization is chosen once for
all the morphisms `f ≫ j`, `j` an open immersion (`AlgebraicGeometry.smoothImageFactor`); `γ_f` is
the orientation of `g` (the canonical identification if `g` is an open immersion, and otherwise the
canonical orientation if known to exist, or a non-canonical one) transported along the canonical
comparison `Rg^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ`. The comparisons satisfy a cocycle condition
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitCompIso_padicAlgCl_comp`),
and the purity isomorphism is compatible with composition with an open immersion `j` on the
target, through the composition isomorphism `R(f ≫ j)^! ≅ Rj^! ⋙ Rf^!`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion`).

The normalizations pin the trace down far more than an arbitrary isomorphism
`Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`, but not completely: the compatibility with general composition and
with base change, and the identification of the trace of a smooth curve with the classical
trace on `H²_c`, need the comparison isomorphisms of Tate twists along pullbacks and tensor
products, which are not available yet.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Purity

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

omit [SmoothOfRelativeDimension d f.left] in
/-- Smooth purity, étale case: the **orientation of
an open immersion** `j` (relative dimension zero), `ℚ̄_ℓ,X(0)[0] ⟶ Rj^! ℚ̄_ℓ,Y`: the canonical
identification `ℚ̄_ℓ(0)[0] ≅ ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ Rj^! ℚ̄_ℓ`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`). -/
noncomputable def openImmersionOrientation (j : X ⟶ Y) [IsOpenImmersion j.left] :
    boundedConstructibleTateTwist ℓ X ((0 : ℕ) : ℤ) (2 * ((0 : ℕ) : ℤ)) ⟶
      (boundedConstructibleUpperShriek ℓ j).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  ((ObjectProperty.fullyFaithfulι _).preimageIso
    (Y := boundedConstructibleTateTwist ℓ X ((0 : ℕ) : ℤ) (2 * ((0 : ℕ) : ℤ)))
    ((ObjectProperty.ι _).mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j) ≪≫
      (tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
      ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm)).inv

omit [SmoothOfRelativeDimension d f.left] in
lemma isIso_openImmersionOrientation (j : X ⟶ Y) [IsOpenImmersion j.left] :
    IsIso (openImmersionOrientation ℓ j) := by
  rw [openImmersionOrientation]
  infer_instance

/-- The orientation of an open immersion is compatible with composition with an open immersion:
the orientation of `g ≫ ι` is that of `g` followed by
`Rg^! ℚ̄_ℓ ≅ R(g ≫ ι)^! ℚ̄_ℓ` (`boundedConstructibleUpperShriekUnitCompIso_padicAlgCl`). -/
lemma openImmersionOrientation_comp {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] [IsSeparated U.hom] (g : X ⟶ U) (ι : U ⟶ Y) [IsOpenImmersion g.left]
    [IsOpenImmersion ι.left] [IsOpenImmersion (g ≫ ι).left] :
    openImmersionOrientation ℓ (g ≫ ι) =
      openImmersionOrientation ℓ g ≫
        (boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ g ι).inv := by
  have hU : boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ (g ≫ ι) =
      boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ g ι ≪≫
        boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ g :=
    Iso.ext (by
      simpa only [boundedConstructibleUpperShriekUnitCompIso_padicAlgCl, Iso.trans_hom,
        Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
        (boundedConstructibleUpperShriekUnitIso_padicAlgCl_comp ℓ g ι).symm)
  refine (ObjectProperty.fullyFaithfulι _).map_injective ?_
  rw [openImmersionOrientation, openImmersionOrientation, hU]
  simp [Functor.FullyFaithful.preimageIso]

/-- The orientation `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` attached to `f` itself, before the
normalization along open immersions of the target: the canonical identification
`openImmersionOrientation` for an open immersion (relative dimension zero), and otherwise
`smoothOrientationOfSmooth`, the canonical orientation (`IsCanonicalSmoothOrientation`) when an
isomorphism with this property is known to exist and a non-canonical isomorphism otherwise. -/
noncomputable def smoothOrientationBase :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) := by
  classical
  exact if h : d = 0 ∧ IsOpenImmersion f.left then
    haveI := h.2
    h.1 ▸ openImmersionOrientation ℓ f
  else
    haveI := neZero_natCast_of_ringChar_ne ℓ (k := k)
    smoothOrientationOfSmooth ℓ f d

/-- The orientation `smoothOrientationBase` is an isomorphism. -/
instance isIso_smoothOrientationBase : IsIso (smoothOrientationBase ℓ f d) := by
  rw [smoothOrientationBase]
  split_ifs with h
  · obtain ⟨h₁, h₂⟩ := h
    subst h₁
    exact isIso_openImmersionOrientation ℓ f
  · infer_instance

omit [SmoothOfRelativeDimension d f.left] in
/-- For an open immersion, `smoothOrientationBase` is `openImmersionOrientation`. -/
lemma smoothOrientationBase_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j.left] :
    smoothOrientationBase ℓ j 0 = openImmersionOrientation ℓ j := by
  rw [smoothOrientationBase, dite_eq_left (⟨rfl, inferInstance⟩ : 0 = 0 ∧ IsOpenImmersion j.left)]

omit [SmoothOfRelativeDimension d f.left] in
/-- The orientation of `f` attached to a factorization `f = g ≫ ι` through an open immersion `ι`:
the orientation `smoothOrientationBase` of `g`, followed by the comparison
`Rg^! ℚ̄_ℓ ≅ R(g ≫ ι)^! ℚ̄_ℓ = Rf^! ℚ̄_ℓ`
(`boundedConstructibleUpperShriekUnitCompIso_padicAlgCl`). -/
noncomputable def smoothOrientationOfFactor {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] [IsSeparated U.hom] (g : X ⟶ U) [SmoothOfRelativeDimension d g.left]
    (ι : U ⟶ Y) [IsOpenImmersion ι.left] (h : g ≫ ι = f) :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  smoothOrientationBase ℓ g d ≫ (boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ g ι).inv ≫
    eqToHom (by rw [h])

omit [SmoothOfRelativeDimension d f.left] in
/-- The orientation attached to a factorization is an isomorphism. -/
instance isIso_smoothOrientationOfFactor {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] [IsSeparated U.hom] (g : X ⟶ U) [SmoothOfRelativeDimension d g.left]
    (ι : U ⟶ Y) [IsOpenImmersion ι.left] (h : g ≫ ι = f) :
    IsIso (smoothOrientationOfFactor ℓ f d g ι h) := by
  rw [smoothOrientationOfFactor]
  infer_instance

omit [SmoothOfRelativeDimension d f.left] in
/-- The orientation attached to a factorization only depends on the open immersion `ι`. -/
lemma smoothOrientationOfFactor_congr {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] [IsSeparated U.hom] (g : X ⟶ U) [SmoothOfRelativeDimension d g.left]
    {ι ι' : U ⟶ Y} [IsOpenImmersion ι.left] [IsOpenImmersion ι'.left] (e : ι = ι')
    (h : g ≫ ι = f) (h' : g ≫ ι' = f) :
    smoothOrientationOfFactor ℓ f d g ι h = smoothOrientationOfFactor ℓ f d g ι' h' := by
  subst e
  rfl

omit [SmoothOfRelativeDimension d f.left] in
/-- The orientations attached to factorizations are compatible with composition with an open
immersion `j` on the target, through `R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ`
(`boundedConstructibleUpperShriekUnitCompIso_padicAlgCl`); this is the cocycle condition
`boundedConstructibleUpperShriekUnitCompIso_padicAlgCl_comp`. -/
lemma smoothOrientationOfFactor_comp {U Z : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (g : X ⟶ U) [SmoothOfRelativeDimension d g.left] (ι : U ⟶ Y)
    [IsOpenImmersion ι.left] (j : Y ⟶ Z) [IsOpenImmersion j.left] [IsOpenImmersion (ι ≫ j).left]
    (h : g ≫ ι = f) (h' : g ≫ ι ≫ j = f ≫ j) :
    smoothOrientationOfFactor ℓ (f ≫ j) d g (ι ≫ j) h' =
      smoothOrientationOfFactor ℓ f d g ι h ≫
        (boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ f j).inv := by
  subst h
  have hc := congrArg Iso.inv (Iso.ext
    (α := boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ g (ι ≫ j))
    (β := eqToIso (congrArg (fun m ↦ (boundedConstructibleUpperShriek ℓ m).obj
        (𝟙_ (Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) (Category.assoc g ι j).symm) ≪≫
      boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ (g ≫ ι) j ≪≫
      boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ g ι)
    (boundedConstructibleUpperShriekUnitCompIso_padicAlgCl_comp ℓ g ι j))
  simp only [Iso.trans_inv, eqToIso.inv, Category.assoc] at hc
  rw [smoothOrientationOfFactor, smoothOrientationOfFactor, hc]
  simp only [Category.assoc, eqToHom_refl, Category.comp_id]

omit [SmoothOfRelativeDimension d f.left] in
/-- For a factorization `f = g ≫ ι` of an open immersion `f` through open immersions, the
attached orientation is `openImmersionOrientation`. -/
lemma smoothOrientationOfFactor_of_isOpenImmersion {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (g : X ⟶ U)
    [IsOpenImmersion g.left] (ι : U ⟶ Y) [IsOpenImmersion ι.left] [IsOpenImmersion f.left]
    (h : g ≫ ι = f) :
    smoothOrientationOfFactor ℓ f 0 g ι h = openImmersionOrientation ℓ f := by
  subst h
  rw [smoothOrientationOfFactor, smoothOrientationBase_of_isOpenImmersion,
    openImmersionOrientation_comp, eqToHom_refl, Category.comp_id]

omit [SmoothOfRelativeDimension d f.left] in
/-- The orientation of `f` attached to an image factorization `p` (`IsSmoothImageFactor`):
`smoothOrientationOfFactor` for the factorization `f = g ≫ ι` it provides. -/
noncomputable def smoothOrientationOfImageFactor (p : Σ U : Over (Spec (.of k)), X ⟶ U)
    (hp : IsSmoothImageFactor f d p) :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  haveI := hp.1
  haveI := hp.2.1
  haveI := hp.2.2.1
  haveI := hp.2.2.2.1
  haveI := hp.2.2.2.2.2.choose_spec.1
  smoothOrientationOfFactor ℓ f d p.2 hp.2.2.2.2.2.choose hp.2.2.2.2.2.choose_spec.2

omit [SmoothOfRelativeDimension d f.left] in
/-- The orientation attached to an image factorization is an isomorphism. -/
instance isIso_smoothOrientationOfImageFactor (p : Σ U : Over (Spec (.of k)), X ⟶ U)
    (hp : IsSmoothImageFactor f d p) : IsIso (smoothOrientationOfImageFactor ℓ f d p hp) := by
  rw [smoothOrientationOfImageFactor]
  infer_instance

omit [SmoothOfRelativeDimension d f.left] in
/-- The orientation attached to an image factorization `(U, g)` is the orientation attached to the
factorization `f = g ≫ ι`, for the (unique) open immersion `ι`. -/
lemma smoothOrientationOfImageFactor_eq {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] [IsSeparated U.hom] (g : X ⟶ U) [SmoothOfRelativeDimension d g.left]
    (ι : U ⟶ Y) [IsOpenImmersion ι.left] (h : g ≫ ι = f)
    (hp : IsSmoothImageFactor f d ⟨U, g⟩) :
    smoothOrientationOfImageFactor ℓ f d ⟨U, g⟩ hp = smoothOrientationOfFactor ℓ f d g ι h := by
  rw [smoothOrientationOfImageFactor]
  have := hp.2.2.2.2.2.choose_spec.1
  exact smoothOrientationOfFactor_congr ℓ f d g (hp.ι_eq hp.2.2.2.2.2.choose_spec.2 h) _ _

omit [SmoothOfRelativeDimension d f.left] in
/-- The orientation attached to an image factorization only depends on the factorization. -/
lemma smoothOrientationOfImageFactor_congr {p p' : Σ U : Over (Spec (.of k)), X ⟶ U}
    (e : p = p') (hp : IsSmoothImageFactor f d p) (hp' : IsSmoothImageFactor f d p') :
    smoothOrientationOfImageFactor ℓ f d p hp = smoothOrientationOfImageFactor ℓ f d p' hp' := by
  subst e
  rfl

omit [SmoothOfRelativeDimension d f.left] in
/-- Smooth purity (`γ_{f,ℚ̄_ℓ}(ℚ̄_ℓ,Y)`, used in `smoothTrace`): the
**orientation** `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` of a morphism `f` smooth of pure relative dimension
`d`, the datum the smooth trace is built from. It is normalized along open immersions: `f`
factors as a surjective morphism `g : X ⟶ U` smooth of pure relative dimension `d` followed by
an open immersion `ι : U ⟶ Y`, and the factorization `(U, g)` is chosen
(`smoothImageFactor`) so that it is the same for `f` and for `f ≫ j`, `j` an open immersion.
The orientation of `f` is the orientation `smoothOrientationBase` of `g` transported along
`Rg^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ` (`smoothOrientationOfFactor`). The orientation of `g` is the canonical
identification `openImmersionOrientation` when `g` is an open immersion (relative dimension zero,
the normalization of smooth purity in relative dimension zero), and otherwise
`smoothOrientationOfSmooth`: the canonical orientation (`IsCanonicalSmoothOrientation`, the
extension of scalars of the integral lift of the finite orientations `Rf^! Λ_Y ≅ Λ_X(d)[2d]` of the
diagonal argument) when an isomorphism with this property is known to exist, and otherwise a
non-canonical isomorphism (`nonempty_iso_tateTwist_upperShriekUnit`). The canonical orientation
always exists mathematically (SGA 4, Exposé XVIII: the finite orientations are compatible under
change of coefficients), but the
existence of the compatible lift is not formalised. It is an isomorphism
(`isIso_smoothOrientation`). The signature does not carry `[SmoothOfRelativeDimension d f.left]`:
for `f` not smooth of pure relative dimension `d` there is no image factorization and the value is
`0`; the datum is meaningful only for `f` smooth of pure relative dimension `d`. -/
@[no_expose]
noncomputable def smoothOrientation :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) := by
  classical
  exact if h : IsSmoothImageFactor f d (smoothImageFactor f d) then
    smoothOrientationOfImageFactor ℓ f d _ h
  else 0

omit [SmoothOfRelativeDimension d f.left] in
/-- The orientation of `f` is the orientation attached to the factorization `f = g ≫ ι` given by
the chosen image factorization `(U, g)` of `f`. -/
lemma smoothOrientation_eq_smoothOrientationOfFactor {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (g : X ⟶ U)
    [SmoothOfRelativeDimension d g.left] (ι : U ⟶ Y) [IsOpenImmersion ι.left] (h : g ≫ ι = f)
    (e : smoothImageFactor f d = ⟨U, g⟩) (hp : IsSmoothImageFactor f d ⟨U, g⟩) :
    smoothOrientation ℓ f d = smoothOrientationOfFactor ℓ f d g ι h := by
  rw [smoothOrientation, dite_eq_left (e ▸ hp)]
  exact (smoothOrientationOfImageFactor_congr ℓ f d e _ hp).trans
    (smoothOrientationOfImageFactor_eq ℓ f d g ι h hp)

omit [SmoothOfRelativeDimension d f.left] in
/-- For an open immersion `j`, the orientation is the canonical identification
`openImmersionOrientation`. -/
lemma smoothOrientation_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j.left] :
    smoothOrientation ℓ j 0 = openImmersionOrientation ℓ j := by
  obtain ⟨⟨U, g⟩, e⟩ : ∃ p, smoothImageFactor j 0 = p := ⟨_, rfl⟩
  have hp : IsSmoothImageFactor j 0 ⟨U, g⟩ := e ▸ isSmoothImageFactor_smoothImageFactor j 0
  obtain ⟨_, _, _, _, _, ι, _, h⟩ := id hp
  have : IsOpenImmersion g.left := MorphismProperty.of_postcomp _ (W' := @IsOpenImmersion) _
    ι.left inferInstance (by rw [← Over.comp_left, h]; infer_instance)
  rw [smoothOrientation_eq_smoothOrientationOfFactor ℓ j 0 g ι h e hp,
    smoothOrientationOfFactor_of_isOpenImmersion]

omit [SmoothOfRelativeDimension d f.left] in
/-- **Compatibility of the orientation with composition with an open immersion** `j` on the
target: `γ_{f ≫ j}` is `γ_f` followed by `Rf^! ℚ̄_ℓ ≅ R(f ≫ j)^! ℚ̄_ℓ`
(`boundedConstructibleUpperShriekUnitCompIso_padicAlgCl`). -/
lemma smoothOrientation_comp_openImmersion {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (j : Y ⟶ Z) [IsOpenImmersion j.left]
    [SmoothOfRelativeDimension d f.left] :
    smoothOrientation ℓ (f ≫ j) d =
      smoothOrientation ℓ f d ≫
        (boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ f j).inv := by
  obtain ⟨⟨U, g⟩, e⟩ : ∃ p, smoothImageFactor f d = p := ⟨_, rfl⟩
  have hp : IsSmoothImageFactor f d ⟨U, g⟩ := e ▸ isSmoothImageFactor_smoothImageFactor f d
  obtain ⟨_, _, _, _, _, ι, _, h⟩ := id hp
  have : IsOpenImmersion (ι ≫ j).left := by
    rw [Over.comp_left]
    infer_instance
  have hp' : IsSmoothImageFactor (f ≫ j) d ⟨U, g⟩ := by
    rw [isSmoothImageFactor_comp_openImmersion]
    exact hp
  rw [smoothOrientation_eq_smoothOrientationOfFactor ℓ (f ≫ j) d g (ι ≫ j)
      (by rw [← Category.assoc, h]) ((smoothImageFactor_comp_openImmersion f j d).trans e) hp',
    smoothOrientation_eq_smoothOrientationOfFactor ℓ f d g ι h e hp,
    smoothOrientationOfFactor_comp]

-- The smoothness hypothesis is a binder of the instance: an `instance` drops unused
-- instance-implicit section variables, even under `include`. The elaborated signature has it
-- once; the linter also counts the section variable in scope.
set_option linter.overlappingInstances false in
/-- The orientation of a morphism smooth of pure relative dimension `d` is an isomorphism: both
the canonical and the non-canonical orientations are (`isIso_smoothOrientationOfSmooth`), and
so are the transports along open immersions. -/
instance isIso_smoothOrientation [SmoothOfRelativeDimension d f.left] :
    IsIso (smoothOrientation ℓ f d) := by
  rw [smoothOrientation, dite_eq_left (isSmoothImageFactor_smoothImageFactor f d)]
  infer_instance

/-- The **purity map** `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` of a morphism `f` smooth of pure relative
dimension `d`: the orientation `γ_f` (`smoothOrientation`). It is the adjoint of the trace map
`Tr_f` for `Rf_! ⊣ Rf^!` (`smoothPurityMap_eq_homEquiv_smoothTrace`). -/
noncomputable def smoothPurityMap :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  smoothOrientation ℓ f d

omit [SmoothOfRelativeDimension d f.left] in
/-- The purity map is the orientation `γ_f`. -/
theorem smoothPurityMap_eq_smoothOrientation :
    smoothPurityMap ℓ f d = smoothOrientation ℓ f d :=
  rfl

/-- The **trace map**
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of a morphism `f` smooth of pure relative dimension `d`
(SGA 4, Exposé XVIII, Théorème 2.9): the composite
`Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ Rf_! Rf^! ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,Y` of `Rf_!` of the orientation `γ_f`
(`smoothOrientation`) and the counit `Tr_f` of `Rf_! ⊣ Rf^!`. -/
@[no_expose]
noncomputable def smoothTrace :
    (boundedConstructibleLowerShriek ℓ f).obj
      (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶
      𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (boundedConstructibleLowerShriek ℓ f).map (smoothOrientation ℓ f d) ≫
    (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _

omit [SmoothOfRelativeDimension d f.left] in
/-- The smooth trace is the counit transpose of the orientation: `Tr^sm_f = Tr_f ∘ Rf_!(γ_f)`. -/
theorem smoothTrace_eq :
    smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map (smoothOrientation ℓ f d) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _ := by
  unfold smoothTrace
  rfl

omit [SmoothOfRelativeDimension d f.left] in
/-- The purity map is the adjoint of the trace map under `Rf_! ⊣ Rf^!`: the adjunct of
`Tr_f ∘ Rf_!(γ_f)` is `γ_f`. -/
theorem smoothPurityMap_eq_homEquiv_smoothTrace :
    smoothPurityMap ℓ f d =
      (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _ (smoothTrace ℓ f d) := by
  rw [smoothPurityMap_eq_smoothOrientation, smoothTrace_eq]
  exact ((congrArg ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _)
    ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv_counit _ _
      (smoothOrientation ℓ f d))).symm.trans
    (((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _).apply_symm_apply _)).symm

-- The smoothness hypothesis is a binder of the instance: an `instance` drops unused
-- instance-implicit section variables, even under `include`. The elaborated signature has it
-- once; the linter also counts the section variable in scope.
set_option linter.overlappingInstances false in
/-- **Smooth purity** (SGA 4, Exposé XVIII, Théorème 3.2.5): the
adjoint of the trace, `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`, is an isomorphism, for `f` smooth of
relative dimension `d`. -/
instance isIso_smoothPurityMap [SmoothOfRelativeDimension d f.left] :
    IsIso (smoothPurityMap ℓ f d) := by
  rw [smoothPurityMap_eq_smoothOrientation]
  infer_instance

/-- **Smooth purity**: for a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type
which is smooth of pure relative dimension `d`, the exceptional inverse image of the constant
coefficient object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. It is the inverse of
the adjoint of the trace (`smoothPurityMap`), after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  (ObjectProperty.ι _).mapIso (asIso (smoothPurityMap ℓ f d)).symm

/-- Smooth purity, étale case: **normalization of
purity in relative dimension zero**: for an open immersion `j`, the purity isomorphism
`Rj^! ℚ̄_ℓ ≅ ℚ̄_ℓ(0)[0]` is the canonical identification `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`); equivalently, the trace of `j` is the
counit `Rj_! Rj^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` read through it. -/
theorem smoothPurityIso_zero_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j.left] :
    smoothPurityIso ℓ j 0 =
      (ObjectProperty.ι _).mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j) ≪≫
        (tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
        ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm := by
  have h : smoothOrientation ℓ j 0 = openImmersionOrientation ℓ j :=
    smoothOrientation_of_isOpenImmersion ℓ j
  have h' : asIso (smoothPurityMap ℓ j 0) = ((ObjectProperty.fullyFaithfulι _).preimageIso
      (Y := boundedConstructibleTateTwist ℓ X ((0 : ℕ) : ℤ) (2 * ((0 : ℕ) : ℤ)))
      ((ObjectProperty.ι _).mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j) ≪≫
        (tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
        ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm)).symm :=
    Iso.ext ((smoothPurityMap_eq_smoothOrientation ℓ j 0).trans h)
  rw [smoothPurityIso, h', Iso.symm_symm_eq]
  ext1
  simp [Functor.FullyFaithful.preimageIso]

/-- **Compatibility of purity with composition with an open immersion**: for `f` smooth of
pure relative dimension `d` and an open immersion `j` on its target, the purity isomorphism of
`f ≫ j` is that of `f` precomposed with `R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! Rj^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ`, the
composition isomorphism of the exceptional inverse images followed by purity for `j`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`). -/
theorem smoothPurityIso_comp_openImmersion {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (j : Y ⟶ Z) [IsOpenImmersion j.left]
    [SmoothOfRelativeDimension d (f ≫ j).left] :
    smoothPurityIso ℓ (f ≫ j) d =
      (ObjectProperty.ι _).mapIso
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app _ ≪≫
            (boundedConstructibleUpperShriek ℓ f).mapIso
              (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)) ≪≫
        smoothPurityIso ℓ f d := by
  have hP : asIso (smoothPurityMap ℓ (f ≫ j) d) = asIso (smoothPurityMap ℓ f d) ≪≫
      (boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ f j).symm :=
    Iso.ext (by
      rw [asIso_hom, Iso.trans_hom, asIso_hom, Iso.symm_hom, smoothPurityMap_eq_smoothOrientation,
        smoothPurityMap_eq_smoothOrientation, smoothOrientation_comp_openImmersion])
  rw [smoothPurityIso, smoothPurityIso, hP]
  refine Iso.ext ?_
  rw [Functor.mapIso_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.map_comp,
    Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom, Iso.symm_hom]
  rfl

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing
