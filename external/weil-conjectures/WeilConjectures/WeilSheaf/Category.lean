/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Simple
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.Extension
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius

/-!
# Weil sheaves and Weil complexes

Let `k₀` be a finite field with algebraic closure `k̄`, `X` a scheme over `k₀`,
`X̄ = X ×_{k₀} k̄` its geometric fiber and `Fr_X = 𝟙 × σ : X̄ ≅ X̄` its geometric Galois Frobenius
(`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`). Following the blueprint
(`definition-weil-structure`, `definition-weil-representation--1`):

- a *Weil sheaf* on `X` is a constructible `ℓ`-adic sheaf `F` on the small pro-étale site of
  `X̄` together with an isomorphism `φ : Fr_X^* F ≅ F`;
- the *Weil complexes* on `X` form the triangulated category obtained from complexes of Weil
  sheaves by inverting the equivariant quasi-isomorphisms.

## Design

*Coefficients and site.* Sheaves are sheaves of `ℚ̄_ℓ`-modules
(`AlgebraicGeometry.WeilCoefficients`) on the small pro-étale site `X̄_proét`
(`AlgebraicGeometry.Scheme.ProEt.topology`). The `ℓ`-adic topology enters through
constructibility: `F` is constructible (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf`)
if `X̄` has, locally, a finite stratification by locally closed subschemes on which `F` is
pro-étale locally a finite sum of copies of the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X̄` of continuous
functions (`AlgebraicGeometry.ProEtale.adicConstantSheaf`), i.e. a constructible
`ℚ̄_ℓ,X̄`-module in the sense of Bhatt–Scholze. Each such sheaf has a finite field of
definition `E ⊆ ℚ̄_ℓ`, so this is the `ℚ̄_ℓ`-stage `2-colim_E Sh_c(X̄, E)` of the blueprint; we work
with `ℚ̄_ℓ` directly since the weights, the additive characters of the Fourier transform and the
embedding `ι : ℚ̄_ℓ →+* ℂ` all live there.

*Frobenius.* The pullback along the automorphism `Fr_X` of pro-étale sheaves is the
pushforward along `Fr_X⁻¹` (`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`), which is
given by an explicit formula and is lax monoidal; we use it as the Frobenius pullback
`AlgebraicGeometry.WeilSheaf.frobeniusPullback`. All pro-étale sheaves with a Weil structure
form the category `AlgebraicGeometry.ProEtaleWeilSheaf k₀ l X = IsoAlgebra (Fr_X^*)`, an abelian
category, Grothendieck since `Fr_X^*` is an autoequivalence
(`CategoryTheory.Endofunctor.IsoAlgebra.isGrothendieckAbelian`). The Weil sheaves are the full
subcategory of those with constructible underlying sheaf, `AlgebraicGeometry.WeilSheaf`; it is
abelian, being closed under kernels, cokernels and finite products.

*Weil complexes.* The derived category `D(ProEtaleWeilSheaf k₀ l X)` is the Verdier
localization of the homotopy category of complexes of pro-étale Weil sheaves at the
quasi-isomorphisms, which are exactly the equivariant quasi-isomorphisms. A *Weil complex*
(`AlgebraicGeometry.WeilComplex`) is an object of it which is bounded and whose cohomology
objects are Weil sheaves; these form a triangulated subcategory, so `WeilComplex k₀ l X` is a
triangulated category, and its morphisms are the `Ext` groups of Weil sheaves: a nonsplit
Frobenius extension of `ℚ̄_ℓ` by `ℚ̄_ℓ` (a Jordan block) is a nonzero morphism
`ℚ̄_ℓ ⟶ ℚ̄_ℓ[1]`. The blueprint localizes bounded complexes of *constructible* Weil sheaves; we
allow arbitrary pro-étale Weil sheaves as terms and impose constructibility on cohomology, which
gives a triangulated category with the same objects up to isomorphism in which the six
operations, being derived functors of functors defined on all pro-étale Weil sheaves, can be
constructed (see `WeilConjectures.WeilSheaf.LowerStar` and
`WeilConjectures.WeilSheaf.LowerShriek`). The functor from the blueprint's category,
`D^b(WeilSheaf k₀ l X) ⥤ WeilComplex k₀ l X`, induced by the exact inclusion of Weil sheaves, is
the realization functor; it is the identity on the heart.

A Weil sheaf is a Weil complex concentrated in degree zero (`WeilSheaf.toComplex`), the
cohomology sheaves `𝓗ᵃ` of a Weil complex are Weil sheaves (`WeilComplex.homologySheaf`), and
both notions pull back along morphisms of `k₀`-schemes (`WeilSheaf.upperStar`,
`WeilComplex.upperStar`), the base change `X̄ ⟶ Ȳ` commuting with the Frobenii.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.frobeniusPullback`: the Frobenius pullback `Fr_X^* = (Fr_X⁻¹)_*`.
- `AlgebraicGeometry.ProEtaleWeilSheaf`: all pro-étale `ℚ̄_ℓ`-sheaves with a Weil structure.
- `AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex`: the abelian category of
  constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme and the triangulated category of Weil
  complexes.
- `AlgebraicGeometry.WeilSheaf.toComplex` and `AlgebraicGeometry.WeilComplex.homologySheaf`:
  the embedding of Weil sheaves as Weil complexes in degree zero, which is fully faithful, and
  the cohomology sheaves, with `𝓗⁰ ∘ toComplex ≅ 𝟭`
  (`AlgebraicGeometry.WeilSheaf.toComplexCompHomologySheafIso`).
- `AlgebraicGeometry.WeilComplex.singleComplex`: a Weil sheaf placed in degree `a`, with
  `𝓗ᵃ` the sheaf itself (`AlgebraicGeometry.WeilComplex.homologySheafSingleComplexIso`) and
  `𝓗ᵇ = 0` for `b ≠ a`.
- `AlgebraicGeometry.WeilComplex.forget`: the forgetful functor to the derived category of
  `ℓ`-adic pro-étale sheaves.
- `AlgebraicGeometry.WeilSheaf.frobeniusPowIso`: the iterated Weil structure
  `φ_m : (Fr_Xᵐ)^* F ≅ F`.
- `AlgebraicGeometry.WeilSheaf.IsLisse`: the underlying sheaf is lisse.
- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse`: a simple object of the category of lisse
  Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.upperStar` and `AlgebraicGeometry.WeilComplex.upperStar`.

## Implementation notes

The coefficient ring `ℚ̄_ℓ = PadicAlgCl l` lives in `Type`, while the sheaf categories on the
sites of `Scheme.{u}` have `Hom`-types in `Type (u + 1)`; hence the `ULift` in
`AlgebraicGeometry.WeilCoefficients`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section Frobenius

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The Frobenius pullback `Fr_X^*` of `ℓ`-adic pro-étale sheaves on the geometric fiber `X̄`,
along its geometric Galois Frobenius `Fr_X`. It is realized as the pushforward along `Fr_X⁻¹`,
which is isomorphic to the pullback along `Fr_X`
(`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`). -/
noncomputable abbrev WeilSheaf.frobeniusPullback :
    AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*ᵃ[l]

/-- The Frobenius pullback is an equivalence, `Fr_X` being an automorphism. -/
instance : (WeilSheaf.frobeniusPullback k₀ l X).IsEquivalence :=
  isEquivalence_adicLowerStar _ _

/-- The category of all `ℓ`-adic pro-étale sheaves on the geometric fiber `X̄` with a Weil
structure: pairs of a sheaf `F` of `ℚ̄_ℓ`-modules on `X̄_proét` and an isomorphism
`φ : Fr_X^* F ≅ F`, with the morphisms of sheaves commuting with the `φ`'s. -/
abbrev ProEtaleWeilSheaf :=
  IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l X)

instance : IsGrothendieckAbelian.{u + 1} (ProEtaleWeilSheaf k₀ l X) :=
  IsoAlgebra.isGrothendieckAbelian _

/-- The property of a pro-étale sheaf with a Weil structure that the underlying sheaf is
constructible; it cuts out the Weil sheaves. -/
noncomputable abbrev WeilSheaf.objectProperty : ObjectProperty (ProEtaleWeilSheaf k₀ l X) :=
  (adicConstructibleSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverseImage
    (IsoAlgebra.forget _)

/-- The property of an object `K` of the derived category of pro-étale Weil sheaves that it is
bounded and that its cohomology objects are Weil sheaves; it cuts out the Weil complexes. -/
noncomputable abbrev WeilComplex.objectProperty :
    ObjectProperty (_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :=
  _root_.DerivedCategory.TStructure.t.bounded ⊓
    _root_.DerivedCategory.homologyProperty (WeilSheaf.objectProperty k₀ l X)

end Frobenius

/-- Blueprint `definition-weil-structure`: Weil sheaf and Weil complex.

The category of constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`: constructible
`ℓ`-adic sheaves `F` on the pro-étale site of the geometric fiber `X̄` with an isomorphism
`Fr_X^* F ≅ F`, where `Fr_X` is the geometric Galois Frobenius of `X̄`. -/
def WeilSheaf (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :=
  (WeilSheaf.objectProperty k₀ l X).FullSubcategory

/-- Blueprint `definition-weil-structure`: Weil sheaf and Weil complex.

The triangulated category of Weil complexes on a `k₀`-scheme `X`: the objects of the derived
category of pro-étale Weil sheaves on `X̄` which are bounded with constructible cohomology. -/
def WeilComplex (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :=
  (WeilComplex.objectProperty k₀ l X).FullSubcategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

noncomputable instance : Category (WeilSheaf k₀ l X) :=
  inferInstanceAs (Category (WeilSheaf.objectProperty k₀ l X).FullSubcategory)

instance : (WeilSheaf.objectProperty k₀ l X).IsClosedUnderFiniteProducts :=
  inferInstance

/-- The geometric fiber of a `k₀`-scheme locally of finite type is locally Noetherian. -/
instance isLocallyNoetherian_geometricFiber
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  have : IsLocallyNoetherian (Scheme.specAlgebraicClosure k₀).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (AlgebraicClosure k₀))))
  inferInstanceAs (IsLocallyNoetherian (pullback _ _))

noncomputable instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    Abelian (WeilSheaf k₀ l X) :=
  inferInstanceAs (Abelian (WeilSheaf.objectProperty k₀ l X).FullSubcategory)

noncomputable instance : Preadditive (WeilSheaf k₀ l X) :=
  inferInstanceAs (Preadditive (WeilSheaf.objectProperty k₀ l X).FullSubcategory)

instance : HasFiniteProducts (WeilSheaf k₀ l X) :=
  inferInstanceAs (HasFiniteProducts (WeilSheaf.objectProperty k₀ l X).FullSubcategory)

instance : HasFiniteBiproducts (WeilSheaf k₀ l X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance : HasBinaryBiproducts (WeilSheaf k₀ l X) :=
  hasBinaryBiproducts_of_finite_biproducts _

instance : (WeilSheaf.objectProperty k₀ l X).IsClosedUnderExtensions :=
  inferInstance

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.objectProperty k₀ l X).IsTriangulated :=
  inferInstance

noncomputable instance : Category (WeilComplex k₀ l X) :=
  inferInstanceAs (Category (WeilComplex.objectProperty k₀ l X).FullSubcategory)

noncomputable instance : Preadditive (WeilComplex k₀ l X) :=
  inferInstanceAs (Preadditive (WeilComplex.objectProperty k₀ l X).FullSubcategory)

noncomputable instance : HasZeroObject (WeilComplex k₀ l X) :=
  inferInstanceAs (HasZeroObject (WeilComplex.objectProperty k₀ l X).FullSubcategory)

noncomputable instance : HasShift (WeilComplex k₀ l X) ℤ :=
  inferInstanceAs (HasShift (WeilComplex.objectProperty k₀ l X).FullSubcategory ℤ)

instance (n : ℤ) : (shiftFunctor (WeilComplex k₀ l X) n).Additive :=
  inferInstanceAs ((shiftFunctor (WeilComplex.objectProperty k₀ l X).FullSubcategory n).Additive)

/-- **Weil complexes form a pretriangulated category**, the triangulated structure being that
of the derived category of pro-étale Weil sheaves. -/
noncomputable instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    Pretriangulated (WeilComplex k₀ l X) :=
  inferInstanceAs (Pretriangulated (WeilComplex.objectProperty k₀ l X).FullSubcategory)

/-- **Weil complexes form a triangulated category.** -/
instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    IsTriangulated (WeilComplex k₀ l X) :=
  inferInstanceAs (IsTriangulated (WeilComplex.objectProperty k₀ l X).FullSubcategory)

namespace WeilComplex

/-- A Weil sheaf placed in degree `a`, as a Weil complex. -/
noncomputable def singleComplex (a : ℤ) (G : WeilSheaf k₀ l X) : WeilComplex k₀ l X :=
  ⟨(_root_.DerivedCategory.singleFunctor _ a).obj G.obj, by
    refine ⟨⟨⟨a, inferInstanceAs (_root_.DerivedCategory.IsGE
      ((_root_.DerivedCategory.singleFunctor _ a).obj G.obj) a)⟩,
      ⟨a, inferInstanceAs (_root_.DerivedCategory.IsLE
        ((_root_.DerivedCategory.singleFunctor _ a).obj G.obj) a)⟩⟩, fun m ↦ ?_⟩
    obtain hm | rfl | hm := lt_trichotomy m a
    · exact (WeilSheaf.objectProperty k₀ l X).prop_of_isZero
        ((_root_.DerivedCategory.isGE_iff
          ((_root_.DerivedCategory.singleFunctor _ a).obj G.obj) a).1 inferInstance m hm)
    · exact (WeilSheaf.objectProperty k₀ l X).prop_of_iso
        ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ m).app G.obj).symm
          G.property
    · exact (WeilSheaf.objectProperty k₀ l X).prop_of_isZero
        ((_root_.DerivedCategory.isLE_iff
          ((_root_.DerivedCategory.singleFunctor _ a).obj G.obj) a).1 inferInstance m hm)⟩

end WeilComplex

namespace WeilSheaf

/-- The underlying pro-étale sheaf of a Weil sheaf. -/
noncomputable abbrev carrier (F : WeilSheaf k₀ l X) :
    AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  F.obj.carrier

/-- The underlying sheaf of a Weil sheaf is constructible. -/
lemma isAdicConstructibleSheaf_carrier (F : WeilSheaf k₀ l X) :
    IsAdicConstructibleSheaf F.obj.carrier :=
  F.property

/-- A Weil sheaf, viewed as a Weil complex concentrated in degree zero. -/
noncomputable def toComplex : WeilSheaf k₀ l X ⥤ WeilComplex k₀ l X :=
  (WeilSheaf.objectProperty k₀ l X).liftFullSubcategory (WeilComplex.objectProperty k₀ l X)
    (_root_.DerivedCategory.singleFunctor _ 0) fun F hF ↦
      (WeilComplex.singleComplex 0 ⟨F, hF⟩).property

instance : (toComplex (k₀ := k₀) (l := l) (X := X)).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

/-- Weil sheaves embed fully faithfully into Weil complexes, as the complexes concentrated in
degree zero: `DerivedCategory.singleFunctor` is fully faithful. -/
instance : (toComplex (k₀ := k₀) (l := l) (X := X)).Full :=
  ObjectProperty.liftFullSubcategory_full _ _ _ _

instance : (toComplex (k₀ := k₀) (l := l) (X := X)).Faithful :=
  ObjectProperty.liftFullSubcategory_faithful _ _ _ _

/-- The iterated Weil structure `φ_m : (Fr_Xᵐ)^* F ≅ F` of a Weil sheaf, the ordered composite

`(Fr_X^{m+1})^* F ≅ Fr_X^* (Fr_Xᵐ)^* F --Fr_X^* φ_m--> Fr_X^* F --φ--> F`

built from `Fr_X^{m+1} = Fr_X ≫ Fr_Xᵐ`, with `φ_0` the identification `𝟙^* F ≅ F`; here the
pullback along an automorphism `g` is the pushforward along `g⁻¹`. At a geometric point fixed
by `Fr_Xᵐ` up to reparametrisation it induces the Frobenius relative to `𝔽_{qᵐ}` on the
stalk. -/
noncomputable def frobeniusPowIso (F : WeilSheaf k₀ l X) (m : ℕ) :
    (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*ᵃ[l].obj
        F.obj.carrier ≅
      F.obj.carrier :=
  match m with
  | 0 => (adicLowerStarCongr l (by rw [pow_zero]; rfl)).app _ ≪≫ (adicLowerStarId l _).app _
  | m + 1 =>
    (adicLowerStarCongr l (by rw [pow_succ, Aut.mul_asIso, Iso.trans_inv])).app _ ≪≫
      (adicLowerStarComp l _ _).symm.app _ ≪≫
      (frobeniusPullback k₀ l X).mapIso (F.frobeniusPowIso m) ≪≫ F.obj.str

/-- A Weil sheaf is *lisse* if its underlying `ℓ`-adic sheaf is lisse: pro-étale locally a
finite direct sum of copies of `ℚ̄_ℓ`. -/
def IsLisse (F : WeilSheaf k₀ l X) : Prop :=
  IsAdicLisseSheaf F.obj.carrier

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- A direct sum of lisse Weil sheaves is lisse: the underlying sheaf of `F ⊞ G` is the direct
sum of those of `F` and `G`. -/
theorem IsLisse.biprod {F G : WeilSheaf k₀ l X} (hF : F.IsLisse) (hG : G.IsLisse) :
    (F ⊞ G).IsLisse := by
  let Φ := ObjectProperty.ι (objectProperty k₀ l X) ⋙ IsoAlgebra.forget (frobeniusPullback k₀ l X)
  have : HasBinaryBiproducts (objectProperty k₀ l X).FullSubcategory :=
    inferInstanceAs (HasBinaryBiproducts (WeilSheaf k₀ l X))
  have : PreservesBinaryBiproducts Φ := preservesBinaryBiproducts_of_preservesBiproducts _
  exact IsAdicLisseSheaf.of_iso (Φ.mapBiprod F G).symm
    (IsAdicLisseSheaf.biprod (F := Φ.obj F) (G := Φ.obj G) hF hG)

/-- A Weil sheaf `F` is *irreducible lisse* if it is lisse and nonzero, and every lisse Weil
subsheaf of `F` is zero or all of `F`: it is a simple object of the category of lisse Weil
sheaves, the meaning of "nonzero irreducible lisse Weil sheaf" in the blueprint. On a connected
normal `X` it says that the representation of the Weil group on the geometric generic stalk is
irreducible.

This is weaker than simplicity in the category of all Weil sheaves: a nonzero lisse sheaf `M`
on a curve `U₀` is never simple there, since for a closed point `x` the extension by zero of
`M|_{U₀ ∖ x}` is a nonzero proper subsheaf. (blueprint:
`lemma-unramified-at-infinity-no-linear-characters--1`) -/
def IsIrreducibleLisse (F : WeilSheaf k₀ l X) : Prop :=
  F.IsLisse ∧ ¬ IsZero F ∧
    ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ F), Mono i → G.IsLisse → IsZero G ∨ IsIso i

/-- A lisse Weil sheaf which is simple in the category of all Weil sheaves is irreducible
lisse. -/
theorem IsLisse.isIrreducibleLisse {F : WeilSheaf k₀ l X} (hF : F.IsLisse) [Simple F] :
    F.IsIrreducibleLisse := by
  refine ⟨hF, Simple.not_isZero F, fun G i _ _ ↦ ?_⟩
  by_cases h : i = 0
  · subst h
    exact Or.inl (IsZero.of_mono_zero G F)
  · exact Or.inr ((Simple.mono_isIso_iff_nonzero i).2 h)

/-- A Weil sheaf `F` is *geometrically irreducible* if its underlying `ℓ`-adic sheaf on the
geometric fiber `X̄` is an irreducible local system: it is lisse and nonzero, and every lisse
subsheaf of it, with no Weil structure, is zero or all of it. For `X̄` connected this says that
the geometric fundamental representation `π₁(X̄) → GL(F_η̄)` is irreducible. -/
def IsGeometricallyIrreducible (F : WeilSheaf k₀ l X) : Prop :=
  IsIrreducibleAdicLocalSystem F.obj.carrier

/-- A Weil sheaf is zero if and only if its underlying sheaf is: the forgetful functor is
additive, and a morphism of Weil sheaves is determined by the underlying morphism of sheaves. -/
theorem isZero_iff_isZero_carrier {F : WeilSheaf k₀ l X} : IsZero F ↔ IsZero F.obj.carrier := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact Functor.map_isZero ((WeilSheaf.objectProperty k₀ l X).ι ⋙ IsoAlgebra.forget _)
      (X := (show (WeilSheaf.objectProperty k₀ l X).FullSubcategory from F)) h
  · exact ⟨fun _ ↦ ⟨⟨0⟩, fun _ ↦ ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <|
      Algebra.Hom.ext <| h.eq_of_src _ _⟩,
    fun _ ↦ ⟨⟨0⟩, fun _ ↦ ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <|
      Algebra.Hom.ext <| h.eq_of_tgt _ _⟩⟩

end WeilSheaf

namespace WeilComplex

/-- The `a`-th cohomology sheaf `𝓗ᵃK` of a Weil complex, in cohomological indexing, a Weil
sheaf. -/
noncomputable def homologySheaf (a : ℤ) : WeilComplex k₀ l X ⥤ WeilSheaf k₀ l X :=
  (WeilComplex.objectProperty k₀ l X).liftFullSubcategory (WeilSheaf.objectProperty k₀ l X)
    (_root_.DerivedCategory.homologyFunctor _ a) fun _ hK ↦ hK.2 a

instance (a : ℤ) : (homologySheaf (k₀ := k₀) (l := l) (X := X) a).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

/-- The cohomology sheaf `𝓗⁰` of a Weil sheaf placed in degree zero is the Weil sheaf itself. -/
noncomputable def _root_.AlgebraicGeometry.WeilSheaf.toComplexCompHomologySheafIso :
    WeilSheaf.toComplex ⋙ homologySheaf 0 ≅ 𝟭 (WeilSheaf k₀ l X) :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F.obj))
    fun f ↦ ObjectProperty.hom_ext _
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.naturality f.hom)

/-- A Weil sheaf viewed as a complex is the Weil sheaf placed in degree `0`. -/
theorem _root_.AlgebraicGeometry.WeilSheaf.toComplex_obj (G : WeilSheaf k₀ l X) :
    WeilSheaf.toComplex.obj G = singleComplex 0 G :=
  rfl

/-- A cohomology sheaf of a Weil complex vanishes if and only if the underlying cohomology
object does. -/
theorem isZero_homologySheaf_obj_iff (a : ℤ) (M : WeilComplex k₀ l X) :
    IsZero ((homologySheaf a).obj M) ↔
      IsZero ((_root_.DerivedCategory.homologyFunctor _ a).obj M.obj) :=
  ⟨fun h ↦ (ObjectProperty.ι _).map_isZero h,
    fun h ↦ IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ h⟩

/-- A Weil sheaf placed in degree `a` has vanishing cohomology sheaves in degrees `b ≠ a`. -/
theorem isZero_homologySheaf_singleComplex {a b : ℤ} (h : b ≠ a) (G : WeilSheaf k₀ l X) :
    IsZero ((homologySheaf b).obj (singleComplex a G)) := by
  rw [isZero_homologySheaf_obj_iff]
  have : (singleComplex a G).obj.IsGE a := inferInstanceAs (_root_.DerivedCategory.IsGE
    ((_root_.DerivedCategory.singleFunctor _ a).obj G.obj) a)
  have : (singleComplex a G).obj.IsLE a := inferInstanceAs (_root_.DerivedCategory.IsLE
    ((_root_.DerivedCategory.singleFunctor _ a).obj G.obj) a)
  obtain h | h := h.lt_or_gt
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 inferInstance b h
  · exact (_root_.DerivedCategory.isLE_iff _ a).1 inferInstance b h

/-- The `a`-th cohomology sheaf of a Weil sheaf placed in degree `a` is the sheaf itself. -/
noncomputable def homologySheafSingleComplexIso (a : ℤ) (G : WeilSheaf k₀ l X) :
    (homologySheaf a).obj (singleComplex a G) ≅ G :=
  ObjectProperty.isoMk _ ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ a).app
    G.obj)

/-- The forgetful functor `For` from Weil complexes to the derived category of `ℓ`-adic
pro-étale sheaves on `X̄`, forgetting the Weil structure; the Weil structure of `K` induces the
derived Frobenius isomorphism `θ_K : Fr_X^* For(K) ≅ For(K)`. -/
noncomputable def forget :
    WeilComplex k₀ l X ⥤ _root_.DerivedCategory
      (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  ObjectProperty.ι _ ⋙ (IsoAlgebra.forget _).mapDerivedCategory

end WeilComplex

section UpperStar

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The pullback `φ^*` of pro-étale Weil sheaves along a morphism `φ : X ⟶ Y` of `k₀`-schemes:
the pullback along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
`ProEtale.upperStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def ProEtaleWeilSheaf.upperStar :
    ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mapOfNatIso
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ _))

instance : (ProEtaleWeilSheaf.upperStar k₀ l φ).Additive :=
  IsoAlgebra.additive_mapOfNatIso _

instance : PreservesFiniteLimits (ProEtaleWeilSheaf.upperStar k₀ l φ) :=
  IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

instance : PreservesFiniteColimits (ProEtaleWeilSheaf.upperStar k₀ l φ) :=
  IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

/-- The pullback `φ^*` of Weil sheaves along a morphism `φ : X ⟶ Y` of `k₀`-schemes: the
pullback along the base change `φ̄ : X̄ ⟶ Ȳ`, with the transported Weil structure. -/
noncomputable def WeilSheaf.upperStar : WeilSheaf k₀ l Y ⥤ WeilSheaf k₀ l X :=
  (WeilSheaf.objectProperty k₀ l Y).liftFullSubcategory (WeilSheaf.objectProperty k₀ l X)
    (ProEtaleWeilSheaf.upperStar k₀ l φ) fun _ hF ↦ IsAdicConstructibleSheaf.upperStar _ hF

instance : (WeilSheaf.upperStar (k₀ := k₀) (l := l) φ).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

/-- The pullback `φ^*` of Weil complexes along a morphism `φ : X ⟶ Y` of `k₀`-schemes: the
functor induced on derived categories by the exact pullback of pro-étale Weil sheaves. -/
noncomputable def WeilComplex.upperStar : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
  (WeilComplex.objectProperty k₀ l Y).liftFullSubcategory (WeilComplex.objectProperty k₀ l X)
    (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory
    fun K hK ↦ ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦ by
      have h : IsAdicConstructibleSheaf ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj
          ((_root_.DerivedCategory.homologyFunctor _ n).obj K)).carrier :=
        IsAdicConstructibleSheaf.upperStar _ (hK.2 n)
      exact (WeilSheaf.objectProperty k₀ l X).prop_of_iso
        ((Functor.mapDerivedCategoryHomologyFunctorIso _ n).app K) h⟩

instance : (WeilComplex.upperStar (k₀ := k₀) (l := l) φ).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

noncomputable instance : (WeilComplex.upperStar (k₀ := k₀) (l := l) φ).CommShift ℤ := by
  have : (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory.CommShift ℤ := inferInstance
  have : (WeilComplex.objectProperty k₀ l X).IsStableUnderShift ℤ := inferInstance
  exact ObjectProperty.commShiftLiftFullSubcategory _ _ _ _

/-- The pullback of Weil complexes is a triangulated functor. -/
instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.upperStar (k₀ := k₀) (l := l) φ).IsTriangulated := by
  have : (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory.IsTriangulated := inferInstance
  exact ObjectProperty.isTriangulated_liftFullSubcategory _ _ _ _

end UpperStar

end AlgebraicGeometry
