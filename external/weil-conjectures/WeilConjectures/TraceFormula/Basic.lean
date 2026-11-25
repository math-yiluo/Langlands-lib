/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Conj
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!

# The setting of the Lefschetz trace formula

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
objects `X : Over (Spec (.of k))`, separated and of finite type over `Spec k`, and the
coefficients are the bounded constructible derived categories `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of `ℚ̄_ℓ`-sheaves,
`ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`. For the trace formula `k` is algebraically closed.

This file collects the pieces of this setting that the trace formula uses and that the six
functors on `Dᵇc(-)⟦Λ⟧` do not provide yet.

* **The base point.** The base `s = Spec k` is the terminal object
  `ProEtale.CondensedRing.point k = Over.mk (𝟙 (Spec k))` of `Over (Spec (.of k))`. Every `X`
  has its structure morphism `a_X = ProEtale.CondensedRing.toPoint X : X ⟶ s`, and the
  `k`-rational points of `X` are the morphisms `x : s ⟶ X` of `Over (Spec (.of k))`, that is the
  sections of `a_X`.
* **Weil objects over a trivial Frobenius.** A Weil object for the identity `𝟙 X`
  is an object `K` together with an isomorphism `L(𝟙 X)^* K ≅ K`, that is an automorphism of `K`
  (`ProEtale.CondensedRing.WeilBoundedConstructible.frobenius`). The stalk of a Weil object at a
  fixed point and its compactly supported cohomology are Weil objects of this kind over the base
  point `s`, and the Frobenius operators of the trace formula are their automorphisms.
* **Traces.** The categorical trace (`CategoryTheory.MonoidalCategory.trace`) on `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`
  takes values in `End (𝟙_ Dᵇc(s)⟦ℚ̲̄_ℓ⟧)`, which is `ℚ̄_ℓ` when `k` is separably closed
  (`ProEtale.CondensedRing.unitEndRingEquiv`). The scalars act on the unit of every
  `Dᵇc(X)⟦Λ⟧` through the global sections of `Λ`
  (`ProEtale.CondensedRing.boundedConstructibleUnitEndRingHom`): a global section `s` of `Λ`
  acts on `Λ_X = p_X^* Λ` by multiplication by `p_X^* s`. For `Λ = ℚ̲̄_ℓ`, the constant global
  sections give the canonical map `ℚ̄_ℓ →+* End (𝟙_ Dᵇc(X)⟦ℚ̲̄_ℓ⟧)`
  (`ProEtale.CondensedRing.padicAlgClUnitEndRingHom`), and `unitEndRingEquiv` is its inverse
  over the base point.

## Main definitions

- `ProEtale.CondensedRing.point`: the base point `s = Spec k`, terminal in `Over (Spec (.of k))`.
- `ProEtale.CondensedRing.toPoint`: the structure morphism `a_X : X ⟶ s`.
- `ProEtale.CondensedRing.PointMod`: the category `Mod_{ℚ̲̄_ℓ,s}` of `ℚ̲̄_ℓ`-module objects on
  the pro-étale site of the point.
- `ProEtale.CondensedRing.WeilBoundedConstructible.frobenius`: the automorphism of a Weil
  object for the identity.

## Main results

- `ProEtale.CondensedRing.bijective_pointUnitEndRingHom`: for `k` separably closed, the
  endomorphisms of the unit of `Mod_{ℚ̲̄_ℓ,s}` are the scalars `ℚ̄_ℓ`.
- `ProEtale.CondensedRing.bijective_padicAlgClUnitEndRingHom_point`: for `k` separably closed,
  the canonical map `ℚ̄_ℓ ⟶ End (𝟙_ Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧) = H⁰(Spec k, ℚ̄_ℓ)` is bijective.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The base point -/

section Point

variable (k : Type u) [Field k]

/-- The base point `s = Spec k` of `Over (Spec (.of k))`: the object `Spec k` with the identity
as structure morphism. It is terminal (`ProEtale.CondensedRing.isTerminalPoint`). -/
noncomputable abbrev point : Over (Spec (.of k)) :=
  Over.mk (𝟙 (Spec (.of k)))

instance : LocallyOfFiniteType (point k).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

instance : QuasiCompact (point k).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

instance : IsSeparated (point k).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

/-- The base point is terminal in `Over (Spec (.of k))`. -/
noncomputable def isTerminalPoint : IsTerminal (point k) :=
  Over.mkIdTerminal

variable {k}

/-- The structure morphism `a_X : X ⟶ s` of a scheme over `Spec k`: the morphism to the terminal
object, as in `ProEtale.CondensedRing.dualizingComplex`. -/
noncomputable def toPoint (X : Over (Spec (.of k))) : X ⟶ point k :=
  Over.mkIdTerminal.from X

@[simp]
lemma toPoint_left (X : Over (Spec (.of k))) : (toPoint X).left = X.hom :=
  Over.mkIdTerminal_from_left X

/-- Two morphisms to the base point are equal. -/
lemma toPoint_ext {X : Over (Spec (.of k))} (f g : X ⟶ point k) : f = g :=
  (isTerminalPoint k).hom_ext f g

@[simp]
lemma comp_toPoint {X Y : Over (Spec (.of k))} (f : X ⟶ Y) : f ≫ toPoint Y = toPoint X :=
  toPoint_ext _ _

/-- The `k`-rational points of `X`: the morphisms `s ⟶ X` of `Over (Spec (.of k))`, that is the
sections of the structure morphism `a_X`. -/
abbrev RationalPoint (X : Over (Spec (.of k))) : Type u :=
  point k ⟶ X

end Point

section Scalars

open MonObj Functor.LaxMonoidal

/-- The inverse image `p_X^*` is additive, being a left adjoint. -/
instance additive_upperStarFromPoint (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The global sections of the coefficient ring `ℚ̲̄_ℓ` act on the unit `Λ_X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: a
global section `s : 𝟙 ⟶ ℚ̲̄_ℓ` is sent to the multiplication by its pullback `p_X^* s` on `Λ_X`
(`Mod.regularEndRingHom`), placed in degree `0`. -/
noncomputable def boundedConstructibleUnitEndRingHom :
    Γ (Profinite.padicAlgClRingObj ℓ) →+* End (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  let F := HomologicalComplex.single
      (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj
          (Profinite.padicAlgClRingObj ℓ) X.left))
      (ComplexShape.up ℤ) 0 ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  have hι : Function.Bijective ((ObjectProperty.ι _).mapEndRingHom (𝟙_
      (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :=
    ((ObjectProperty.fullyFaithfulι _).mulEquivEnd _).bijective
  have : IsIso (ε (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))) := inferInstanceAs (IsIso (𝟙 _))
  ((RingEquiv.ofBijective _ hι).symm.toRingHom.comp
    ((asIso (ε (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
            X.left))))).symm.conjRingEquiv.toRingHom.comp
      ((F.mapEndRingHom (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          X.left))).comp
        (Mod.regularEndRingHom.comp (Γ.mapFunctor (upperStarFromPoint X.left))))))

/-- The canonical map `ℚ̄_ℓ →+* End (𝟙_ Dᵇc(X)⟦ℚ̲̄_ℓ⟧)`: a scalar `a` acts on `ℚ̄_ℓ,X` by
multiplication by the constant global section `a` of `ℚ̲̄_ℓ`
(`Profinite.PadicAlgCl.constRingHom`). -/
noncomputable def padicAlgClUnitEndRingHom :
    PadicAlgCl ℓ →+* End (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (boundedConstructibleUnitEndRingHom ℓ X).comp (Profinite.PadicAlgCl.constRingHom ℓ)

end Scalars

section PointMod

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- The abelian category of `ℚ̲̄_ℓ`-module objects on the pro-étale site of the point
`s = Spec k`, the ambient category of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`. -/
abbrev PointMod : Type _ :=
  Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)

/-- The scalars `ℚ̄_ℓ` acting on the unit of `Mod_{ℚ̲̄_ℓ,s}`: a scalar `a` acts by the
multiplication by the constant global section `a`. -/
noncomputable def pointUnitEndRingHom : PadicAlgCl ℓ →+* End (𝟙_ (PointMod ℓ k)) :=
  (Mod.regularEndRingHom.comp (MonObj.Γ.mapFunctor (upperStarFromPoint (point k).left))).comp
    (Profinite.PadicAlgCl.constRingHom ℓ)

variable [IsSepClosed k]

/-- For `k` separably closed, the endomorphisms of the unit of `Mod_{ℚ̲̄_ℓ,s}` are the scalars
`ℚ̄_ℓ`. -/
theorem bijective_pointUnitEndRingHom : Function.Bijective (pointUnitEndRingHom ℓ k) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  have := isEquivalence_upperStarFromPointMod (Ω := k) Λ
  have hE := (upperStarFromPoint (Spec (.of k))).bijective_regularEndRingHom_comp_mapFunctor Λ
    (Functor.FullyFaithful.ofFullyFaithful (upperStarFromPointMod Λ (Spec (.of k))))
  have : Nontrivial (MonObj.Γ Λ) := ⟨⟨1, 0, fun h ↦ Profinite.PadicAlgCl.one_ne_zero_end_regular ℓ
    (by rw [← map_one Mod.regularEndRingHom, h, map_zero])⟩⟩
  have hc : Function.Bijective (Profinite.PadicAlgCl.constRingHom.{u} ℓ) :=
    ⟨(Profinite.PadicAlgCl.constRingHom ℓ).injective,
      Profinite.PadicAlgCl.constRingHom_surjective ℓ⟩
  exact hE.comp hc

end PointMod

section ScalarsPoint

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

omit [Fact (ringChar k).Prime] in
/-- For `k` separably closed, the endomorphisms of the unit of `Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧` are
`H⁰(Spec k, ℚ̄_ℓ) = ℚ̄_ℓ`: the canonical map `ℚ̄_ℓ →+* End (𝟙_ Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧)` is
bijective. It is the composite of the bijection `ℚ̄_ℓ ≅ End_{ℚ̲̄_ℓ,s} ℚ̲̄_ℓ,s`
(`bijective_pointUnitEndRingHom`) and
`End_{ℚ̲̄_ℓ,s} ℚ̲̄_ℓ,s ≅ End_{D(ℚ̲̄_ℓ,s)} ℚ̲̄_ℓ,s` (the functor `singleFunctor 0` being fully
faithful). -/
theorem bijective_padicAlgClUnitEndRingHom_point :
    Function.Bijective (padicAlgClUnitEndRingHom ℓ (point k)) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let A := Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
    (condensedRingObj Λ (point k).left)
  let F := HomologicalComplex.single A (ComplexShape.up ℤ) 0 ⋙
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have : F.Full := Functor.Full.of_iso
    ((DerivedCategory.singleFunctorIsoCompQ A 0).trans
      (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso A).symm))
  have : F.Faithful := Functor.Faithful.of_iso
    ((DerivedCategory.singleFunctorIsoCompQ A 0).trans
      (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso A).symm))
  have hF :
      Function.Bijective (F.mapEndRingHom (Mod.regular (condensedRingObj Λ (point k).left))) :=
    ((Functor.FullyFaithful.ofFullyFaithful F).mulEquivEnd _).bijective
  have h := bijective_pointUnitEndRingHom ℓ k
  unfold padicAlgClUnitEndRingHom boundedConstructibleUnitEndRingHom
  unfold pointUnitEndRingHom at h
  simp only [RingHom.comp_assoc] at h ⊢
  rw [RingHom.coe_comp, RingHom.coe_comp, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ (hF.comp h)) <;>
    exact RingEquiv.bijective _

/-- For `k` separably closed, the endomorphisms of the unit of `Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧` are
`H⁰(Spec k, ℚ̄_ℓ) = ℚ̄_ℓ`: the inverse of the canonical map `padicAlgClUnitEndRingHom`. The
categorical traces of the trace formula take values here. -/
noncomputable def unitEndRingEquiv :
    End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ≃+* PadicAlgCl ℓ :=
  (RingEquiv.ofBijective _ (bijective_padicAlgClUnitEndRingHom_point ℓ k)).symm

end ScalarsPoint

/-! ### Weil objects for the identity -/

section Frobenius

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace WeilBoundedConstructible

variable {ℓ}

/-- The *Frobenius* of a Weil object `(K, φ_K)` for the identity `𝟙 X`: the automorphism
```
K --(L(𝟙 X)^* ≅ 𝟭)⁻¹--> L(𝟙 X)^* K --φ_K--> K.
```
For the stalk of a Weil object at a fixed point and for its compactly supported cohomology,
Weil objects for the identity of the base point, this is the Frobenius operator of the trace
formula. -/
noncomputable def frobenius (K : WeilBoundedConstructible ℓ (𝟙 X)) : K.carrier ≅ K.carrier :=
  ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app K.carrier).symm ≪≫
    K.str

lemma frobenius_hom (K : WeilBoundedConstructible ℓ (𝟙 X)) :
    K.frobenius.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).inv.app K.carrier ≫
        K.str.hom :=
  rfl

/-- The Frobenius of Weil objects for the identity is natural: a morphism of Weil objects
commutes with the Frobenius automorphisms. -/
lemma frobenius_hom_naturality {K L : WeilBoundedConstructible ℓ (𝟙 X)} (g : K ⟶ L) :
    K.frobenius.hom ≫ g.hom.f = g.hom.f ≫ L.frobenius.hom := by
  rw [frobenius_hom, frobenius_hom, Category.assoc, IsoAlgebra.str_hom, IsoAlgebra.str_hom,
    ← g.hom.h, ← Category.assoc,
    ← (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).inv.naturality,
    Category.assoc]
  rfl

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
